//! AI集成演示示例
//! 
//! 展示如何使用c17_iot的AI集成功能进行智能数据分析和预测

use c17_iot::ai_integration::{
    AIIntegrationManager,
    AIModelConfig,
    AIModelType,
    AIConfig,
    AnalysisType,
    //PredictionType,
};
use std::time::Duration;
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动AI集成演示...");

    println!("📊 开始演示IoT系统AI集成功能...");

    // 1. AI集成管理器创建和配置
    println!("\n1️⃣ AI集成管理器创建和配置");
    demo_ai_manager_creation().await?;

    // 2. AI模型注册和管理
    println!("\n2️⃣ AI模型注册和管理");
    demo_model_registration().await?;

    // 3. 智能预测
    println!("\n3️⃣ 智能预测");
    demo_intelligent_prediction().await?;

    // 4. 数据分析
    println!("\n4️⃣ 数据分析");
    demo_data_analysis().await?;

    // 5. 异常检测
    println!("\n5️⃣ 异常检测");
    demo_anomaly_detection().await?;

    // 6. 趋势分析
    println!("\n6️⃣ 趋势分析");
    demo_trend_analysis().await?;

    // 7. 模式识别
    println!("\n7️⃣ 模式识别");
    demo_pattern_recognition().await?;

    // 8. 批量处理
    println!("\n8️⃣ 批量处理");
    demo_batch_processing().await?;

    // 9. 实时分析
    println!("\n9️⃣ 实时分析");
    demo_realtime_analysis().await?;

    // 10. AI统计和报告
    println!("\n🔟 AI统计和报告");
    demo_ai_statistics().await?;

    println!("\n✅ AI集成演示完成!");
    println!("🎯 演示展示了以下功能:");
    println!("  - AI模型管理和注册");
    println!("  - 智能预测和分析");
    println!("  - 异常检测和趋势分析");
    println!("  - 模式识别和聚类分析");
    println!("  - 实时分析和批量处理");

    Ok(())
}

/// AI集成管理器创建和配置演示
async fn demo_ai_manager_creation() -> Result<(), Box<dyn std::error::Error>> {
    // 创建AI配置
    let config = AIConfig {
        enable_ai: true,
        max_prediction_history: 1000,
        max_analysis_history: 500,
        batch_size: 32,
        processing_timeout: Duration::from_secs(30),
        enable_realtime_analysis: true,
        realtime_analysis_interval: Duration::from_secs(60),
    };

    println!("  创建AI集成管理器...");
    let ai_manager = AIIntegrationManager::new(config);
    
    // 获取初始统计信息
    let stats = ai_manager.get_stats().await;
    println!("  初始AI统计:");
    println!("    总预测数: {}", stats.total_predictions);
    println!("    总分析数: {}", stats.total_analyses);
    println!("    平均预测时间: {:?}", stats.avg_prediction_time);
    println!("    平均分析时间: {:?}", stats.avg_analysis_time);

    Ok(())
}

/// AI模型注册和管理演示
async fn demo_model_registration() -> Result<(), Box<dyn std::error::Error>> {
    let ai_manager = AIIntegrationManager::new(AIConfig::default());
    
    // 注册多个AI模型
    let models = vec![
        ("anomaly_detector", AIModelType::AnomalyDetection, 10, 1),
        ("temperature_predictor", AIModelType::Prediction, 5, 1),
        ("device_classifier", AIModelType::Classification, 8, 3),
        ("sensor_clusterer", AIModelType::Clustering, 6, 4),
        ("time_series_forecaster", AIModelType::TimeSeries, 12, 1),
    ];

    println!("  注册AI模型...");
    for (name, model_type, input_features, output_dimensions) in models {
        let model_config = AIModelConfig {
            model_type: model_type.clone(),
            name: name.to_string(),
            version: "1.0".to_string(),
            model_path: format!("/models/{}", name),
            input_features,
            output_dimensions,
            enable_gpu: true,
            batch_size: 32,
            confidence_threshold: 0.8,
            custom_params: HashMap::new(),
        };
        
        ai_manager.register_model(model_config).await?;
        println!("    注册模型: {} ({:?})", name, model_type);
    }

    // 获取已注册的模型列表
    let registered_models = ai_manager.get_models().await;
    println!("  已注册模型数量: {}", registered_models.len());
    for model in registered_models {
        println!("    - {}: {:?} (输入: {}, 输出: {})", 
                model.name, model.model_type, model.input_features, model.output_dimensions);
    }

    Ok(())
}

/// 智能预测演示
async fn demo_intelligent_prediction() -> Result<(), Box<dyn std::error::Error>> {
    let ai_manager = AIIntegrationManager::new(AIConfig::default());
    
    // 注册预测模型
    let model_config = AIModelConfig {
        model_type: AIModelType::Prediction,
        name: "temperature_predictor".to_string(),
        version: "1.0".to_string(),
        model_path: "/models/temperature_predictor".to_string(),
        input_features: 5,
        output_dimensions: 1,
        enable_gpu: true,
        batch_size: 32,
        confidence_threshold: 0.8,
        custom_params: HashMap::new(),
    };
    
    ai_manager.register_model(model_config).await?;
    
    println!("  执行智能预测...");
    
    // 模拟传感器数据
    let sensor_data = vec![
        vec![20.5, 21.0, 21.5, 22.0, 22.5], // 温度上升趋势
        vec![25.0, 24.5, 24.0, 23.5, 23.0], // 温度下降趋势
        vec![18.0, 18.2, 18.1, 18.3, 18.2], // 温度稳定
    ];
    
    for (i, features) in sensor_data.iter().enumerate() {
        println!("    预测 {}: 输入特征 {:?}", i + 1, features);
        
        let prediction = ai_manager.predict("temperature_predictor", features.clone()).await?;
        
        println!("      预测结果: {:?}", prediction.prediction);
        println!("      置信度: {:.2}%", prediction.confidence * 100.0);
        println!("      预测类型: {:?}", prediction.prediction_type);
        println!("      预测时间: {}", prediction.timestamp.format("%H:%M:%S"));
    }

    Ok(())
}

/// 数据分析演示
async fn demo_data_analysis() -> Result<(), Box<dyn std::error::Error>> {
    let ai_manager = AIIntegrationManager::new(AIConfig::default());
    
    println!("  执行数据分析...");
    
    // 模拟IoT设备数据
    let device_data = vec![
        1.0, 1.2, 1.5, 1.8, 2.0, 2.3, 2.5, 2.8, 3.0, 3.2, // 上升趋势
        3.0, 2.8, 2.5, 2.2, 2.0, 1.8, 1.5, 1.2, 1.0, 0.8, // 下降趋势
        1.0, 1.1, 0.9, 1.2, 0.8, 1.3, 0.7, 1.4, 0.6, 1.5, // 波动模式
    ];
    
    // 执行多种分析
    let analyses = vec![
        (AnalysisType::TrendAnalysis, "趋势分析"),
        (AnalysisType::CorrelationAnalysis, "相关性分析"),
        (AnalysisType::ClusteringAnalysis, "聚类分析"),
    ];
    
    for (analysis_type, description) in analyses {
        println!("    执行{}...", description);
        
        let analysis = ai_manager.analyze(analysis_type, device_data.clone(), "sensor_data".to_string()).await?;
        
        println!("      分析ID: {}", analysis.id);
        println!("      分析类型: {:?}", analysis.analysis_type);
        println!("      处理时间: {:?}", analysis.processing_time);
        println!("      置信度: {:.2}%", analysis.confidence * 100.0);
        println!("      建议数量: {}", analysis.recommendations.len());
        
        for (i, recommendation) in analysis.recommendations.iter().enumerate() {
            println!("        建议 {}: {}", i + 1, recommendation);
        }
    }

    Ok(())
}

/// 异常检测演示
async fn demo_anomaly_detection() -> Result<(), Box<dyn std::error::Error>> {
    let ai_manager = AIIntegrationManager::new(AIConfig::default());
    
    println!("  执行异常检测...");
    
    // 模拟包含异常的数据
    let normal_data = vec![1.0, 1.1, 1.0, 1.2, 1.1, 1.0, 1.1, 1.2, 1.0, 1.1];
    let anomaly_data = vec![1.0, 1.1, 1.0, 5.0, 1.1, 1.0, 1.1, 1.2, 1.0, 1.1]; // 包含异常值5.0
    
    let datasets = vec![
        (normal_data, "正常数据"),
        (anomaly_data, "异常数据"),
    ];
    
    for (data, description) in datasets {
        println!("    检测{}...", description);
        
        let analysis = ai_manager.analyze(AnalysisType::AnomalyDetection, data, "anomaly_detection".to_string()).await?;
        
        if let c17_iot::ai_integration::AnalysisResults::Anomaly(anomaly_result) = analysis.results {
            println!("      是否异常: {}", if anomaly_result.is_anomaly { "是" } else { "否" });
            println!("      异常分数: {:.2}", anomaly_result.anomaly_score);
            println!("      异常类型: {:?}", anomaly_result.anomaly_type);
            println!("      异常位置: {:?}", anomaly_result.anomaly_positions);
            println!("      正常范围: ({:.1}, {:.1})", anomaly_result.normal_range.0, anomaly_result.normal_range.1);
        }
    }

    Ok(())
}

/// 趋势分析演示
async fn demo_trend_analysis() -> Result<(), Box<dyn std::error::Error>> {
    let ai_manager = AIIntegrationManager::new(AIConfig::default());
    
    println!("  执行趋势分析...");
    
    // 模拟不同趋势的数据
    let trend_data = vec![
        (vec![1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0], "上升趋势"),
        (vec![5.0, 4.5, 4.0, 3.5, 3.0, 2.5, 2.0], "下降趋势"),
        (vec![2.0, 2.1, 1.9, 2.0, 2.1, 1.9, 2.0], "稳定趋势"),
        (vec![1.0, 3.0, 1.5, 4.0, 2.0, 5.0, 2.5], "波动趋势"),
    ];
    
    for (data, description) in trend_data {
        println!("    分析{}...", description);
        
        let analysis = ai_manager.analyze(AnalysisType::TrendAnalysis, data, "trend_analysis".to_string()).await?;
        
        if let c17_iot::ai_integration::AnalysisResults::Trend(trend_result) = analysis.results {
            println!("      趋势方向: {:?}", trend_result.direction);
            println!("      趋势强度: {:.2}", trend_result.strength);
            println!("      变化率: {:.2}", trend_result.change_rate);
            println!("      预测值: {:?}", trend_result.forecast_values);
            println!("      置信区间: ({:.1}, {:.1})", trend_result.confidence_interval.0, trend_result.confidence_interval.1);
        }
    }

    Ok(())
}

/// 模式识别演示
async fn demo_pattern_recognition() -> Result<(), Box<dyn std::error::Error>> {
    let ai_manager = AIIntegrationManager::new(AIConfig::default());
    
    println!("  执行模式识别...");
    
    // 模拟包含模式的数据
    let pattern_data = vec![
        1.0, 2.0, 3.0, 1.0, 2.0, 3.0, 1.0, 2.0, 3.0, // 重复模式
        0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5, // 线性增长
        2.0, 1.5, 1.0, 0.5, 1.0, 1.5, 2.0, 1.5, 1.0, // 周期性模式
    ];
    
    let analysis = ai_manager.analyze(AnalysisType::PatternRecognition, pattern_data, "pattern_recognition".to_string()).await?;
    
    if let c17_iot::ai_integration::AnalysisResults::Pattern(pattern_result) = analysis.results {
        println!("    识别到的模式数量: {}", pattern_result.pattern_count);
        println!("    模式质量: {:.2}", pattern_result.pattern_quality);
        
        for (i, pattern) in pattern_result.patterns.iter().enumerate() {
            println!("      模式 {}: {}", i + 1, pattern.description);
            println!("        类型: {}", pattern.pattern_type);
            println!("        强度: {:.2}", pattern.strength);
            println!("        位置: {:?}", pattern.positions);
        }
    }

    Ok(())
}

/// 批量处理演示
async fn demo_batch_processing() -> Result<(), Box<dyn std::error::Error>> {
    let ai_manager = AIIntegrationManager::new(AIConfig::default());
    
    // 注册批量预测模型
    let model_config = AIModelConfig {
        model_type: AIModelType::Prediction,
        name: "batch_predictor".to_string(),
        version: "1.0".to_string(),
        model_path: "/models/batch_predictor".to_string(),
        input_features: 3,
        output_dimensions: 1,
        enable_gpu: true,
        batch_size: 10,
        confidence_threshold: 0.8,
        custom_params: HashMap::new(),
    };
    
    ai_manager.register_model(model_config).await?;
    
    println!("  执行批量预测...");
    
    // 准备批量数据
    let batch_data = vec![
        vec![1.0, 2.0, 3.0],
        vec![2.0, 3.0, 4.0],
        vec![3.0, 4.0, 5.0],
        vec![4.0, 5.0, 6.0],
        vec![5.0, 6.0, 7.0],
    ];
    
    println!("    批量数据大小: {}", batch_data.len());
    
    let start_time = std::time::Instant::now();
    let predictions = ai_manager.batch_predict("batch_predictor", batch_data).await?;
    let batch_time = start_time.elapsed();
    
    println!("    批量预测完成，耗时: {:?}", batch_time);
    println!("    预测结果数量: {}", predictions.len());
    
    for (i, prediction) in predictions.iter().enumerate() {
        println!("      预测 {}: 值={:.2}, 置信度={:.2}%", 
                i + 1, 
                prediction.prediction[0], 
                prediction.confidence * 100.0);
    }

    Ok(())
}

/// 实时分析演示
async fn demo_realtime_analysis() -> Result<(), Box<dyn std::error::Error>> {
    let ai_manager = AIIntegrationManager::new(AIConfig::default());
    
    println!("  执行实时分析...");
    
    // 模拟实时数据流
    let realtime_data = vec![
        0.8, 0.75, 0.82, 0.78, 0.85, 0.88, 0.92, 0.95, 0.98, 1.0, // 系统负载上升
    ];
    
    let analysis = ai_manager.analyze(AnalysisType::RealTimeAnalysis, realtime_data, "realtime_monitor".to_string()).await?;
    
    if let c17_iot::ai_integration::AnalysisResults::RealTime(realtime_result) = analysis.results {
        println!("    实时指标:");
        for (metric, value) in &realtime_result.metrics {
            println!("      {}: {:.2}", metric, value);
        }
        
        println!("    实时状态: {:?}", realtime_result.status);
        println!("    告警数量: {}", realtime_result.alerts.len());
        println!("    建议数量: {}", realtime_result.suggestions.len());
        
        for (i, suggestion) in realtime_result.suggestions.iter().enumerate() {
            println!("      建议 {}: {}", i + 1, suggestion);
        }
    }

    Ok(())
}

/// AI统计和报告演示
async fn demo_ai_statistics() -> Result<(), Box<dyn std::error::Error>> {
    let ai_manager = AIIntegrationManager::new(AIConfig::default());
    
    println!("  生成AI统计报告...");
    
    // 执行一些操作以生成统计数据
    let model_config = AIModelConfig {
        model_type: AIModelType::Prediction,
        name: "stats_model".to_string(),
        version: "1.0".to_string(),
        model_path: "/models/stats_model".to_string(),
        input_features: 2,
        output_dimensions: 1,
        enable_gpu: false,
        batch_size: 1,
        confidence_threshold: 0.8,
        custom_params: HashMap::new(),
    };
    
    ai_manager.register_model(model_config).await?;
    
    // 执行一些预测
    for i in 0..5 {
        let features = vec![i as f64, (i + 1) as f64];
        let _ = ai_manager.predict("stats_model", features).await?;
    }
    
    // 执行一些分析
    for i in 0..3 {
        let data = vec![i as f64, (i + 1) as f64, (i + 2) as f64];
        let _ = ai_manager.analyze(AnalysisType::TrendAnalysis, data, "stats_analysis".to_string()).await?;
    }
    
    // 获取统计信息
    let stats = ai_manager.get_stats().await;
    println!("  AI统计报告:");
    println!("    总预测数: {}", stats.total_predictions);
    println!("    总分析数: {}", stats.total_analyses);
    println!("    平均预测时间: {:?}", stats.avg_prediction_time);
    println!("    平均分析时间: {:?}", stats.avg_analysis_time);
    println!("    预测准确率: {:.2}%", stats.prediction_accuracy * 100.0);
    println!("    分析成功率: {:.2}%", stats.analysis_success_rate * 100.0);
    println!("    最后更新时间: {}", stats.last_updated.format("%Y-%m-%d %H:%M:%S"));
    
    println!("    模型使用统计:");
    for (model_name, usage_count) in &stats.model_usage {
        println!("      {}: {} 次", model_name, usage_count);
    }
    
    // 获取预测历史
    let prediction_history = ai_manager.get_prediction_history(Some(3)).await;
    println!("    最近预测历史 ({} 条):", prediction_history.len());
    for (i, prediction) in prediction_history.iter().enumerate() {
        println!("      {}: {} - 置信度 {:.2}%", 
                i + 1, 
                prediction.model_name, 
                prediction.confidence * 100.0);
    }
    
    // 获取分析历史
    let analysis_history = ai_manager.get_analysis_history(Some(2)).await;
    println!("    最近分析历史 ({} 条):", analysis_history.len());
    for (i, analysis) in analysis_history.iter().enumerate() {
        println!("      {}: {:?} - 处理时间 {:?}", 
                i + 1, 
                analysis.analysis_type, 
                analysis.processing_time);
    }

    Ok(())
}
