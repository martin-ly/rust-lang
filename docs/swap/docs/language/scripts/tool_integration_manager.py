#!/usr/bin/env python3
"""
Rust语言形式化理论体系 - 工具集成管理器

本脚本提供自动化工具集成管理功能，包括：
1. 工具配置管理
2. 工作流执行
3. 集成监控
4. 通知管理

作者: Rust语言形式化理论项目组
版本: v2.0
日期: 2025年1月27日
"""

import os
import json
import subprocess
import schedule
import time
import logging
from pathlib import Path
from typing import Dict, List, Optional, Any
from dataclasses import dataclass
from datetime import datetime
import argparse
import smtplib
import requests
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('tool_integration.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

@dataclass
class ToolResult:
    """工具执行结果"""
    tool_name: str
    success: bool
    execution_time: float
    output: str
    error: Optional[str] = None
    quality_score: Optional[float] = None

@dataclass
class WorkflowResult:
    """工作流执行结果"""
    workflow_name: str
    start_time: datetime
    end_time: datetime
    success: bool
    tool_results: List[ToolResult]
    overall_quality_score: float

class ToolIntegrationManager:
    """工具集成管理器"""
    
    def __init__(self, config_path: str = "scripts/tool_integration_config.json"):
        self.config_path = Path(config_path)
        self.config = self._load_config()
        self.tools = self.config.get('tools', {})
        self.workflows = self.config.get('workflows', {})
        self.integrations = self.config.get('integrations', {})
        self.notifications = self.config.get('notifications', {})
        
    def _load_config(self) -> Dict:
        """加载配置文件"""
        try:
            with open(self.config_path, 'r', encoding='utf-8') as f:
                return json.load(f)
        except Exception as e:
            logger.error(f"加载配置文件失败: {e}")
            return {}
            
    def execute_tool(self, tool_name: str, args: List[str] = None) -> ToolResult:
        """执行单个工具"""
        if tool_name not in self.tools:
            return ToolResult(
                tool_name=tool_name,
                success=False,
                execution_time=0.0,
                output="",
                error=f"工具 {tool_name} 不存在"
            )
            
        tool_config = self.tools[tool_name]
        tool_file = tool_config['file']
        
        # 构建命令
        cmd = ['python', tool_file]
        if args:
            cmd.extend(args)
            
        start_time = time.time()
        
        try:
            # 执行工具
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=600  # 10分钟超时
            )
            
            execution_time = time.time() - start_time
            
            if result.returncode == 0:
                logger.info(f"工具 {tool_name} 执行成功，耗时 {execution_time:.2f} 秒")
                return ToolResult(
                    tool_name=tool_name,
                    success=True,
                    execution_time=execution_time,
                    output=result.stdout
                )
            else:
                logger.error(f"工具 {tool_name} 执行失败: {result.stderr}")
                return ToolResult(
                    tool_name=tool_name,
                    success=False,
                    execution_time=execution_time,
                    output=result.stdout,
                    error=result.stderr
                )
                
        except subprocess.TimeoutExpired:
            execution_time = time.time() - start_time
            logger.error(f"工具 {tool_name} 执行超时")
            return ToolResult(
                tool_name=tool_name,
                success=False,
                execution_time=execution_time,
                output="",
                error="执行超时"
            )
        except Exception as e:
            execution_time = time.time() - start_time
            logger.error(f"工具 {tool_name} 执行异常: {e}")
            return ToolResult(
                tool_name=tool_name,
                success=False,
                execution_time=execution_time,
                output="",
                error=str(e)
            )
            
    def execute_workflow(self, workflow_name: str) -> WorkflowResult:
        """执行工作流"""
        if workflow_name not in self.workflows:
            logger.error(f"工作流 {workflow_name} 不存在")
            return None
            
        workflow_config = self.workflows[workflow_name]
        tools = workflow_config.get('tools', [])
        
        start_time = datetime.now()
        tool_results = []
        
        logger.info(f"开始执行工作流: {workflow_name}")
        
        for tool_name in tools:
            logger.info(f"执行工具: {tool_name}")
            result = self.execute_tool(tool_name)
            tool_results.append(result)
            
            if not result.success:
                logger.warning(f"工具 {tool_name} 执行失败，继续执行其他工具")
                
        end_time = datetime.now()
        
        # 计算整体质量分数
        successful_tools = [r for r in tool_results if r.success]
        overall_quality_score = 0.0
        
        if successful_tools:
            # 这里可以根据实际需求计算质量分数
            overall_quality_score = 85.0  # 示例值
            
        success = all(r.success for r in tool_results)
        
        workflow_result = WorkflowResult(
            workflow_name=workflow_name,
            start_time=start_time,
            end_time=end_time,
            success=success,
            tool_results=tool_results,
            overall_quality_score=overall_quality_score
        )
        
        logger.info(f"工作流 {workflow_name} 执行完成，成功: {success}")
        
        # 发送通知
        self._send_notification(workflow_result)
        
        return workflow_result
        
    def _send_notification(self, workflow_result: WorkflowResult) -> None:
        """发送通知"""
        if not self.notifications:
            return
            
        # 检查是否需要发送通知
        should_notify = self._should_send_notification(workflow_result)
        if not should_notify:
            return
            
        # 发送邮件通知
        if self.notifications.get('email', {}).get('enabled', False):
            self._send_email_notification(workflow_result)
            
        # 发送Slack通知
        if self.notifications.get('slack', {}).get('enabled', False):
            self._send_slack_notification(workflow_result)
            
        # 发送Webhook通知
        if self.notifications.get('webhook', {}).get('enabled', False):
            self._send_webhook_notification(workflow_result)
            
    def _should_send_notification(self, workflow_result: WorkflowResult) -> bool:
        """判断是否需要发送通知"""
        workflow_config = self.workflows.get(workflow_result.workflow_name, {})
        notification_config = workflow_config.get('notifications', {})
        
        if not notification_config.get('enabled', False):
            return False
            
        thresholds = notification_config.get('thresholds', {})
        
        # 检查质量分数阈值
        quality_threshold = thresholds.get('quality_score', 80)
        if workflow_result.overall_quality_score < quality_threshold:
            return True
            
        # 检查失败工具数量
        failed_tools = [r for r in workflow_result.tool_results if not r.success]
        if len(failed_tools) > 0:
            return True
            
        return False
        
    def _send_email_notification(self, workflow_result: WorkflowResult) -> None:
        """发送邮件通知"""
        try:
            email_config = self.notifications['email']
            
            msg = MIMEMultipart()
            msg['From'] = email_config['username']
            msg['To'] = ', '.join(email_config['recipients'])
            msg['Subject'] = f"工作流执行报告: {workflow_result.workflow_name}"
            
            # 构建邮件内容
            body = self._build_notification_content(workflow_result)
            msg.attach(MIMEText(body, 'plain', 'utf-8'))
            
            # 发送邮件
            server = smtplib.SMTP(email_config['smtp_server'], email_config['smtp_port'])
            server.starttls()
            server.login(email_config['username'], email_config['password'])
            server.send_message(msg)
            server.quit()
            
            logger.info("邮件通知发送成功")
            
        except Exception as e:
            logger.error(f"发送邮件通知失败: {e}")
            
    def _send_slack_notification(self, workflow_result: WorkflowResult) -> None:
        """发送Slack通知"""
        try:
            slack_config = self.notifications['slack']
            
            # 构建消息内容
            content = self._build_notification_content(workflow_result)
            
            payload = {
                'text': f"工作流执行报告: {workflow_result.workflow_name}",
                'attachments': [
                    {
                        'color': 'good' if workflow_result.success else 'danger',
                        'text': content
                    }
                ]
            }
            
            # 发送请求
            response = requests.post(slack_config['webhook_url'], json=payload)
            response.raise_for_status()
            
            logger.info("Slack通知发送成功")
            
        except Exception as e:
            logger.error(f"发送Slack通知失败: {e}")
            
    def _send_webhook_notification(self, workflow_result: WorkflowResult) -> None:
        """发送Webhook通知"""
        try:
            webhook_config = self.notifications['webhook']
            
            # 构建数据
            data = {
                'workflow_name': workflow_result.workflow_name,
                'success': workflow_result.success,
                'start_time': workflow_result.start_time.isoformat(),
                'end_time': workflow_result.end_time.isoformat(),
                'quality_score': workflow_result.overall_quality_score,
                'tool_results': [
                    {
                        'tool_name': r.tool_name,
                        'success': r.success,
                        'execution_time': r.execution_time,
                        'error': r.error
                    }
                    for r in workflow_result.tool_results
                ]
            }
            
            # 发送请求
            headers = webhook_config.get('headers', {})
            response = requests.post(
                webhook_config['url'],
                json=data,
                headers=headers
            )
            response.raise_for_status()
            
            logger.info("Webhook通知发送成功")
            
        except Exception as e:
            logger.error(f"发送Webhook通知失败: {e}")
            
    def _build_notification_content(self, workflow_result: WorkflowResult) -> str:
        """构建通知内容"""
        content = f"""
工作流执行报告
================

工作流名称: {workflow_result.workflow_name}
执行时间: {workflow_result.start_time.strftime('%Y-%m-%d %H:%M:%S')} - {workflow_result.end_time.strftime('%Y-%m-%d %H:%M:%S')}
执行状态: {'成功' if workflow_result.success else '失败'}
质量分数: {workflow_result.overall_quality_score:.2f}

工具执行结果:
"""
        
        for result in workflow_result.tool_results:
            status = '成功' if result.success else '失败'
            content += f"- {result.tool_name}: {status} (耗时: {result.execution_time:.2f}秒)\n"
            if result.error:
                content += f"  错误: {result.error}\n"
                
        return content
        
    def schedule_workflows(self) -> None:
        """调度工作流"""
        for workflow_name, workflow_config in self.workflows.items():
            schedule_type = workflow_config.get('schedule', '')
            
            if schedule_type == 'daily':
                time_str = workflow_config.get('time', '09:00')
                schedule.every().day.at(time_str).do(
                    self.execute_workflow, workflow_name
                )
                logger.info(f"已调度每日工作流: {workflow_name} at {time_str}")
                
            elif schedule_type == 'weekly':
                day = workflow_config.get('day', 'monday')
                time_str = workflow_config.get('time', '10:00')
                getattr(schedule.every(), day).at(time_str).do(
                    self.execute_workflow, workflow_name
                )
                logger.info(f"已调度每周工作流: {workflow_name} on {day} at {time_str}")
                
            elif schedule_type == 'monthly':
                day = workflow_config.get('day', 1)
                time_str = workflow_config.get('time', '11:00')
                schedule.every().month.do(
                    self.execute_workflow, workflow_name
                )
                logger.info(f"已调度每月工作流: {workflow_name} on day {day} at {time_str}")
                
    def run_scheduler(self) -> None:
        """运行调度器"""
        logger.info("启动工作流调度器")
        
        while True:
            schedule.run_pending()
            time.sleep(60)  # 每分钟检查一次
            
    def get_tool_status(self) -> Dict[str, Any]:
        """获取工具状态"""
        status = {}
        
        for tool_name, tool_config in self.tools.items():
            tool_file = Path(tool_config['file'])
            status[tool_name] = {
                'enabled': tool_config.get('enabled', True),
                'file_exists': tool_file.exists(),
                'description': tool_config.get('description', ''),
                'features': tool_config.get('features', [])
            }
            
        return status
        
    def get_workflow_status(self) -> Dict[str, Any]:
        """获取工作流状态"""
        status = {}
        
        for workflow_name, workflow_config in self.workflows.items():
            status[workflow_name] = {
                'schedule': workflow_config.get('schedule', ''),
                'tools': workflow_config.get('tools', []),
                'notifications': workflow_config.get('notifications', {}).get('enabled', False)
            }
            
        return status

def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='Rust语言形式化理论体系工具集成管理器')
    parser.add_argument('--config', default='scripts/tool_integration_config.json', help='配置文件路径')
    parser.add_argument('--workflow', help='执行指定工作流')
    parser.add_argument('--tool', help='执行指定工具')
    parser.add_argument('--schedule', action='store_true', help='启动调度器')
    parser.add_argument('--status', action='store_true', help='显示工具和工作流状态')
    
    args = parser.parse_args()
    
    # 创建管理器
    manager = ToolIntegrationManager(args.config)
    
    if args.workflow:
        # 执行指定工作流
        result = manager.execute_workflow(args.workflow)
        if result:
            print(f"工作流 {args.workflow} 执行完成")
            print(f"成功: {result.success}")
            print(f"质量分数: {result.overall_quality_score:.2f}")
            
    elif args.tool:
        # 执行指定工具
        result = manager.execute_tool(args.tool)
        print(f"工具 {args.tool} 执行完成")
        print(f"成功: {result.success}")
        print(f"执行时间: {result.execution_time:.2f}秒")
        
    elif args.schedule:
        # 启动调度器
        manager.schedule_workflows()
        manager.run_scheduler()
        
    elif args.status:
        # 显示状态
        tool_status = manager.get_tool_status()
        workflow_status = manager.get_workflow_status()
        
        print("工具状态:")
        for tool_name, status in tool_status.items():
            print(f"  {tool_name}: {'启用' if status['enabled'] else '禁用'} ({'文件存在' if status['file_exists'] else '文件不存在'})")
            
        print("\n工作流状态:")
        for workflow_name, status in workflow_status.items():
            print(f"  {workflow_name}: {status['schedule']} ({len(status['tools'])} 个工具)")
            
    else:
        # 默认执行所有工作流
        for workflow_name in manager.workflows:
            result = manager.execute_workflow(workflow_name)
            if result:
                print(f"工作流 {workflow_name} 执行完成")

if __name__ == "__main__":
    main()