# 医疗健康数据处理（Healthcare Data Processing）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [医疗健康数据处理（Healthcare Data Processing）](#医疗健康数据处理healthcare-data-processing)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [应用场景](#应用场景)
    - [1. 电子健康记录（EHR）系统](#1-电子健康记录ehr系统)
    - [2. 医疗数据分析](#2-医疗数据分析)
    - [3. 实时监控系统](#3-实时监控系统)
  - [数据安全](#数据安全)
    - [加密存储](#加密存储)
    - [访问控制](#访问控制)
  - [Rust 实现](#rust-实现)
    - [患者记录管理](#患者记录管理)
    - [实时监控系统](#实时监控系统)
  - [实践示例](#实践示例)
    - [示例 1：医疗数据分析](#示例-1医疗数据分析)
  - [性能优化](#性能优化)
    - [1. 并行数据处理](#1-并行数据处理)
    - [2. 批量操作](#2-批量操作)
  - [参考资料](#参考资料)

---

## 概述

医疗健康数据处理涉及患者信息、医疗记录、诊断数据等敏感信息的处理。Rust 的内存安全和性能特性使其成为构建医疗数据处理系统的理想选择。

## 应用场景

### 1. 电子健康记录（EHR）系统

- 患者信息管理
- 医疗记录存储和检索
- 数据隐私保护

### 2. 医疗数据分析

- 疾病诊断辅助
- 药物效果分析
- 流行病学研究

### 3. 实时监控系统

- 患者生命体征监控
- 异常检测和警报
- 远程医疗支持

## 数据安全

### 加密存储

```rust
use aes_gcm::{
    aead::{Aead, KeyInit},
    Aes256Gcm, Nonce,
};
use rand::RngCore;

pub struct SecureStorage {
    cipher: Aes256Gcm,
}

impl SecureStorage {
    pub fn new(key: &[u8; 32]) -> Self {
        let cipher = Aes256Gcm::new_from_slice(key)
            .expect("密钥长度必须为 32 字节");
        SecureStorage { cipher }
    }

    pub fn encrypt(&self, data: &[u8]) -> Result<Vec<u8>, String> {
        let mut nonce_bytes = [0u8; 12];
        rand::thread_rng().fill_bytes(&mut nonce_bytes);
        let nonce = Nonce::from_slice(&nonce_bytes);

        self.cipher
            .encrypt(nonce, data)
            .map_err(|e| format!("加密失败: {}", e))
    }

    pub fn decrypt(&self, encrypted: &[u8]) -> Result<Vec<u8>, String> {
        if encrypted.len() < 12 {
            return Err("数据太短".to_string());
        }

        let nonce = Nonce::from_slice(&encrypted[..12]);
        self.cipher
            .decrypt(nonce, &encrypted[12..])
            .map_err(|e| format!("解密失败: {}", e))
    }
}
```

### 访问控制

```rust
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Permission {
    Read,
    Write,
    Delete,
    Admin,
}

#[derive(Debug, Clone)]
pub struct User {
    pub id: String,
    pub name: String,
    pub permissions: Vec<Permission>,
}

pub struct AccessControl {
    users: HashMap<String, User>,
}

impl AccessControl {
    pub fn new() -> Self {
        AccessControl {
            users: HashMap::new(),
        }
    }

    pub fn add_user(&mut self, user: User) {
        self.users.insert(user.id.clone(), user);
    }

    pub fn check_permission(&self, user_id: &str, permission: &Permission) -> bool {
        self.users
            .get(user_id)
            .map(|user| user.permissions.contains(permission))
            .unwrap_or(false)
    }

    pub fn can_access(&self, user_id: &str, required_permission: &Permission) -> bool {
        self.check_permission(user_id, required_permission)
            || self.check_permission(user_id, &Permission::Admin)
    }
}
```

## Rust 实现

### 患者记录管理

```rust
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PatientRecord {
    pub patient_id: String,
    pub name: String,
    pub date_of_birth: DateTime<Utc>,
    pub medical_history: Vec<MedicalEvent>,
    pub current_medications: Vec<Medication>,
    pub allergies: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MedicalEvent {
    pub date: DateTime<Utc>,
    pub event_type: EventType,
    pub description: String,
    pub doctor: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EventType {
    Diagnosis,
    Treatment,
    Surgery,
    Checkup,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Medication {
    pub name: String,
    pub dosage: String,
    pub frequency: String,
    pub start_date: DateTime<Utc>,
    pub end_date: Option<DateTime<Utc>>,
}

pub struct PatientRecordManager {
    records: HashMap<String, PatientRecord>,
    access_control: AccessControl,
}

impl PatientRecordManager {
    pub fn new(access_control: AccessControl) -> Self {
        PatientRecordManager {
            records: HashMap::new(),
            access_control,
        }
    }

    pub fn add_record(
        &mut self,
        user_id: &str,
        record: PatientRecord,
    ) -> Result<(), String> {
        if !self.access_control.can_access(user_id, &Permission::Write) {
            return Err("权限不足".to_string());
        }

        self.records.insert(record.patient_id.clone(), record);
        Ok(())
    }

    pub fn get_record(
        &self,
        user_id: &str,
        patient_id: &str,
    ) -> Result<&PatientRecord, String> {
        if !self.access_control.can_access(user_id, &Permission::Read) {
            return Err("权限不足".to_string());
        }

        self.records
            .get(patient_id)
            .ok_or_else(|| "患者记录不存在".to_string())
    }

    pub fn add_medical_event(
        &mut self,
        user_id: &str,
        patient_id: &str,
        event: MedicalEvent,
    ) -> Result<(), String> {
        if !self.access_control.can_access(user_id, &Permission::Write) {
            return Err("权限不足".to_string());
        }

        let record = self.records.get_mut(patient_id)
            .ok_or_else(|| "患者记录不存在".to_string())?;
        record.medical_history.push(event);
        Ok(())
    }
}
```

### 实时监控系统

```rust
use tokio::sync::mpsc;
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct VitalSigns {
    pub patient_id: String,
    pub timestamp: DateTime<Utc>,
    pub heart_rate: f64,
    pub blood_pressure_systolic: f64,
    pub blood_pressure_diastolic: f64,
    pub temperature: f64,
    pub oxygen_saturation: f64,
}

pub struct VitalSignsMonitor {
    threshold: VitalSignsThreshold,
    alert_sender: mpsc::Sender<Alert>,
}

#[derive(Debug, Clone)]
pub struct VitalSignsThreshold {
    pub heart_rate_min: f64,
    pub heart_rate_max: f64,
    pub blood_pressure_systolic_max: f64,
    pub blood_pressure_diastolic_max: f64,
    pub temperature_min: f64,
    pub temperature_max: f64,
    pub oxygen_saturation_min: f64,
}

#[derive(Debug, Clone)]
pub struct Alert {
    pub patient_id: String,
    pub severity: AlertSeverity,
    pub message: String,
    pub timestamp: DateTime<Utc>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AlertSeverity {
    Low,
    Medium,
    High,
    Critical,
}

impl VitalSignsMonitor {
    pub fn new(
        threshold: VitalSignsThreshold,
        alert_sender: mpsc::Sender<Alert>,
    ) -> Self {
        VitalSignsMonitor {
            threshold,
            alert_sender,
        }
    }

    pub async fn process_vital_signs(&self, signs: VitalSigns) -> Result<(), String> {
        let mut alerts = Vec::new();

        // 检查心率
        if signs.heart_rate < self.threshold.heart_rate_min
            || signs.heart_rate > self.threshold.heart_rate_max
        {
            alerts.push(Alert {
                patient_id: signs.patient_id.clone(),
                severity: AlertSeverity::High,
                message: format!("心率异常: {:.1} bpm", signs.heart_rate),
                timestamp: signs.timestamp,
            });
        }

        // 检查血压
        if signs.blood_pressure_systolic > self.threshold.blood_pressure_systolic_max
            || signs.blood_pressure_diastolic > self.threshold.blood_pressure_diastolic_max
        {
            alerts.push(Alert {
                patient_id: signs.patient_id.clone(),
                severity: AlertSeverity::Critical,
                message: format!(
                    "血压异常: {:.0}/{:.0} mmHg",
                    signs.blood_pressure_systolic, signs.blood_pressure_diastolic
                ),
                timestamp: signs.timestamp,
            });
        }

        // 检查体温
        if signs.temperature < self.threshold.temperature_min
            || signs.temperature > self.threshold.temperature_max
        {
            alerts.push(Alert {
                patient_id: signs.patient_id.clone(),
                severity: AlertSeverity::Medium,
                message: format!("体温异常: {:.1}°C", signs.temperature),
                timestamp: signs.timestamp,
            });
        }

        // 检查血氧饱和度
        if signs.oxygen_saturation < self.threshold.oxygen_saturation_min {
            alerts.push(Alert {
                patient_id: signs.patient_id.clone(),
                severity: AlertSeverity::Critical,
                message: format!("血氧饱和度低: {:.1}%", signs.oxygen_saturation),
                timestamp: signs.timestamp,
            });
        }

        // 发送警报
        for alert in alerts {
            self.alert_sender.send(alert).await
                .map_err(|e| format!("发送警报失败: {}", e))?;
        }

        Ok(())
    }
}
```

## 实践示例

### 示例 1：医疗数据分析

```rust
use rayon::prelude::*;

pub struct MedicalDataAnalyzer;

impl MedicalDataAnalyzer {
    pub fn analyze_patient_cohort(
        &self,
        records: &[PatientRecord],
    ) -> CohortAnalysis {
        let total_patients = records.len();

        let avg_age = records
            .par_iter()
            .map(|r| {
                let age = Utc::now().signed_duration_since(r.date_of_birth);
                age.num_days() / 365
            })
            .sum::<i64>() as f64 / total_patients as f64;

        let common_conditions = self.extract_common_conditions(records);
        let medication_usage = self.analyze_medication_usage(records);

        CohortAnalysis {
            total_patients,
            average_age: avg_age,
            common_conditions,
            medication_usage,
        }
    }

    fn extract_common_conditions(&self, records: &[PatientRecord]) -> Vec<(String, usize)> {
        let mut condition_counts: HashMap<String, usize> = HashMap::new();

        for record in records {
            for event in &record.medical_history {
                if let EventType::Diagnosis = event.event_type {
                    *condition_counts.entry(event.description.clone()).or_insert(0) += 1;
                }
            }
        }

        let mut conditions: Vec<(String, usize)> = condition_counts.into_iter().collect();
        conditions.sort_by(|a, b| b.1.cmp(&a.1));
        conditions.into_iter().take(10).collect()
    }

    fn analyze_medication_usage(&self, records: &[PatientRecord]) -> HashMap<String, usize> {
        let mut medication_counts: HashMap<String, usize> = HashMap::new();

        for record in records {
            for medication in &record.current_medications {
                *medication_counts.entry(medication.name.clone()).or_insert(0) += 1;
            }
        }

        medication_counts
    }
}

#[derive(Debug)]
pub struct CohortAnalysis {
    pub total_patients: usize,
    pub average_age: f64,
    pub common_conditions: Vec<(String, usize)>,
    pub medication_usage: HashMap<String, usize>,
}
```

## 性能优化

### 1. 并行数据处理

```rust
use rayon::prelude::*;

pub fn parallel_analyze_records(records: &[PatientRecord]) -> Vec<AnalysisResult> {
    records
        .par_iter()
        .map(|record| {
            // 分析单个记录
            analyze_single_record(record)
        })
        .collect()
}
```

### 2. 批量操作

```rust
impl PatientRecordManager {
    pub fn batch_update(
        &mut self,
        user_id: &str,
        updates: Vec<(String, MedicalEvent)>,
    ) -> Result<(), String> {
        if !self.access_control.can_access(user_id, &Permission::Write) {
            return Err("权限不足".to_string());
        }

        for (patient_id, event) in updates {
            if let Some(record) = self.records.get_mut(&patient_id) {
                record.medical_history.push(event);
            }
        }

        Ok(())
    }
}
```

## 参考资料

- [医疗健康索引](./00_index.md)
- [金融科技索引](../00_index.md)
- [数据安全最佳实践](../../../../crates/c10_networks/)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回金融科技: [`../00_index.md`](../00_index.md)
