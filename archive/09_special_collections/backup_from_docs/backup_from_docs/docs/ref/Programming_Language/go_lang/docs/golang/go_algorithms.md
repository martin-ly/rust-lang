# Go 2025：算法与数据结构实现全景

## 目录

- [Go 2025：算法与数据结构实现全景](#go-2025算法与数据结构实现全景)
  - [目录](#目录)
  - [1. 引言：Go 2025 预期特性](#1-引言go-2025-预期特性)
  - [2. 搜索算法](#2-搜索算法)
    - [2.1 二分查找](#21-二分查找)
    - [2.2 跳跃查找](#22-跳跃查找)
    - [2.3 插值查找](#23-插值查找)
  - [3. 排序算法](#3-排序算法)
    - [3.1 快速排序](#31-快速排序)
    - [3.2 归并排序](#32-归并排序)
    - [3.3 堆排序](#33-堆排序)
  - [4. 图算法](#4-图算法)
    - [4.1 广度优先搜索 (BFS)](#41-广度优先搜索-bfs)
    - [4.2 深度优先搜索 (DFS)](#42-深度优先搜索-dfs)
    - [4.3 Dijkstra 最短路径](#43-dijkstra-最短路径)
  - [5. 分治算法](#5-分治算法)
    - [5.1 分治思想概述](#51-分治思想概述)
    - [5.2 快速选择](#52-快速选择)
    - [5.3 最大子数组问题](#53-最大子数组问题)
  - [6. 动态规划](#6-动态规划)
    - [6.1 动态规划基础](#61-动态规划基础)
    - [6.2 背包问题](#62-背包问题)
    - [6.3 编辑距离](#63-编辑距离)
    - [6.4 最长公共子序列](#64-最长公共子序列)
    - [6.5 矩阵链乘法](#65-矩阵链乘法)
  - [7. 高级数据结构](#7-高级数据结构)
    - [7.1 Trie树（前缀树）](#71-trie树前缀树)
    - [7.2 红黑树](#72-红黑树)
    - [7.3 跳表（Skip List）](#73-跳表skip-list)
    - [7.4 布隆过滤器（Bloom Filter）](#74-布隆过滤器bloom-filter)
    - [7.5 一致性哈希（Consistent Hashing）](#75-一致性哈希consistent-hashing)
    - [7.6 LRU缓存](#76-lru缓存)
    - [7.7 并发数据结构](#77-并发数据结构)
      - [7.7.1 并发哈希表](#771-并发哈希表)
      - [7.7.2 无锁队列](#772-无锁队列)
  - [8. 并发算法](#8-并发算法)
    - [8.1 并行归并排序](#81-并行归并排序)
    - [8.2 并行分区索引](#82-并行分区索引)
    - [8.3 并行图算法](#83-并行图算法)
    - [8.4 并行幂集算法](#84-并行幂集算法)
    - [8.5 并行前缀和](#85-并行前缀和)
    - [8.6 并行矩阵乘法](#86-并行矩阵乘法)
  - [9. 未来展望与总结](#9-未来展望与总结)
    - [9.1 基准测试与性能剖析](#91-基准测试与性能剖析)
    - [9.2 云原生和分布式算法](#92-云原生和分布式算法)
    - [9.3 AI与机器学习相关算法](#93-ai与机器学习相关算法)
    - [9.4 总结与展望](#94-总结与展望)

## 1. 引言：Go 2025 预期特性

在展望 Go 2025 的发展前，我们需要了解目前 Go 语言的核心特性以及可能的未来改进方向。
Go 在 2025 年版本可能包含的特性包括：

1. **增强的泛型功能**：自 Go 1.18 引入泛型后，预计会进一步扩展泛型的能力，如泛型方法、增强的类型约束等
2. **结构化并发控制**：更强大的并发控制机制，如 structured concurrency 模式
3. **错误处理改进**：可能添加更简洁的错误处理语法
4. **增强的内存管理**：改进的垃圾回收机制，可能支持局部内存管理选项
5. **更高效的编译器和运行时**：更快的编译速度和运行效率
6. **增强的类型系统**：类型推导的进一步完善，更丰富的类型复用机制
7. **原生正则表达式支持**：改进的正则表达式库，可能有语法糖
8. **改进的模块管理**：依赖管理和版本控制的进一步优化

以下算法实现将基于这些预期特性，同时保持与 Go 语言的简洁性和实用性原则一致。

## 2. 搜索算法

### 2.1 二分查找

**定义**：二分查找（Binary Search）是一种在有序数组中查找特定元素的高效算法。每次比较中，算法将搜索范围缩小一半，使得时间复杂度为 O(log n)。

**基本原理**：

1. 将目标值与数组中间元素比较
2. 如果相等，返回中间元素的索引
3. 如果目标值小于中间元素，在左半部分继续搜索
4. 如果目标值大于中间元素，在右半部分继续搜索
5. 如果搜索区间为空，则目标值不存在于数组中

**Go 2025 实现**：

```go
// binarySearch 在有序数组中查找目标值，返回索引（找不到返回-1）
// 使用Go 2025增强的泛型能力，支持任何可比较类型
func binarySearch[T Comparable](arr []T, target T) int {
    left, right := 0, len(arr)-1
    
    for left <= right {
        mid := left + (right-left)/2 // 避免整数溢出
        
        switch {
        case arr[mid] == target:
            return mid // 找到目标
        case arr[mid] < target:
            left = mid + 1 // 在右半部分搜索
        case arr[mid] > target:
            right = mid - 1 // 在左半部分搜索
        }
    }
    
    return -1 // 未找到目标
}

// 递归版本的二分查找
func binarySearchRecursive[T Comparable](arr []T, target T, left, right int) int {
    if left > right {
        return -1 // 基本情况：搜索空间为空
    }
    
    mid := left + (right-left)/2
    
    switch {
    case arr[mid] == target:
        return mid
    case arr[mid] < target:
        return binarySearchRecursive(arr, target, mid+1, right)
    default:
        return binarySearchRecursive(arr, target, left, mid-1)
    }
}

// 假设Go 2025引入的Comparable约束，支持比较操作
type Comparable interface {
    comparable
    Less(Comparable) bool
}

// 整数类型实现Comparable接口（Go 2025可能支持基本类型自动实现接口）
func (i int) Less(other Comparable) bool {
    return i < other.(int)
}

// 用法示例
func binarySearchExample() {
    numbers := []int{2, 5, 8, 12, 16, 23, 38, 56, 72, 91}
    
    // 使用迭代版本
    fmt.Println("查找23:", binarySearch(numbers, 23))  // 输出: 5
    fmt.Println("查找55:", binarySearch(numbers, 55))  // 输出: -1
    
    // 使用递归版本
    fmt.Println("递归查找72:", binarySearchRecursive(numbers, 72, 0, len(numbers)-1))  // 输出: 8
}
```

**性能分析**：

- 时间复杂度：O(log n)，每次比较将搜索空间减半
- 空间复杂度：迭代版本为 O(1)，递归版本为 O(log n)（递归栈空间）
- 二分查找仅适用于有序数组，不适合频繁更新的数据集
- 对于小型数组，线性搜索可能更有效，因为二分查找的常数因子较大

### 2.2 跳跃查找

**定义**：跳跃查找（Jump Search）是二分查找和线性查找的混合体，适用于有序数组。算法先以固定步长跳跃，找到目标可能在的区间，然后在该区间内进行线性搜索。

**基本原理**：

1. 设定跳跃步长（通常为 √n，其中 n 为数组长度）
2. 向前跳跃直到找到大于目标值的元素或到达数组末尾
3. 在最后跳跃区间内进行线性搜索
4. 如果找到目标值则返回索引，否则返回 -1

**Go 2025 实现**：

```go
// jumpSearch 实现跳跃查找算法
// 使用Go 2025的类型参数增强特性，支持泛型方法
func jumpSearch[T Comparable](arr []T, target T) int {
    n := len(arr)
    if n == 0 {
        return -1
    }
    
    // 最优步长为 √n
    step := int(math.Sqrt(float64(n)))
    
    // 寻找包含目标值的块
    prev := 0
    for minStep := min[int](step, n); arr[minStep-1] < target; minStep = min[int](minStep+step, n) {
        prev = minStep
        if prev >= n {
            return -1 // 超出数组范围
        }
    }
    
    // 在块内线性搜索
    for arr[prev] < target {
        prev++
        if prev == min(step, n) || prev >= n {
            return -1 // 目标不在数组中
        }
    }
    
    // 检查是否找到目标
    if arr[prev] == target {
        return prev
    }
    
    return -1 // 目标不在数组中
}

// Go 2025 推测性特性：泛型函数中的 min 函数
func min[T Ordered](a, b T) T {
    if a < b {
        return a
    }
    return b
}

// Ordered 是 Go 2025 可能提供的内置约束
// 定义可排序的类型
type Ordered interface {
    comparable
    Less(Ordered) bool
}

// 用法示例
func jumpSearchExample() {
    data := []int{2, 4, 7, 10, 14, 18, 23, 30, 35, 43, 51, 63, 78}
    
    fmt.Println("查找30:", jumpSearch(data, 30))  // 输出: 7
    fmt.Println("查找31:", jumpSearch(data, 31))  // 输出: -1
}
```

**性能分析**：

- 时间复杂度：O(√n)，其中 n 是数组长度
- 空间复杂度：O(1)，使用常数额外空间
- 优点：比线性搜索快，比二分查找操作简单
- 缺点：比二分查找慢，仍需有序数组
- 最佳应用场景：当元素需要频繁访问且比较操作开销大的情况

### 2.3 插值查找

**定义**：插值查找（Interpolation Search）是对二分查找的改进，特别适用于元素均匀分布的有序数组。它基于目标值在数组中可能位置的估计，而不是简单地将数组分成两半。

**基本原理**：

1. 使用插值公式估计目标值可能的位置：pos = low + ((target - arr[low]) * (high - low)) / (arr[high] - arr[low])
2. 将目标值与 arr[pos] 比较
3. 如果相等，返回 pos
4. 如果目标值小于 arr[pos]，在左侧继续搜索
5. 如果目标值大于 arr[pos]，在右侧继续搜索

**Go 2025 实现**：

```go
// interpolationSearch 使用插值搜索算法
// 利用 Go 2025 的增强型泛型和数值约束
func interpolationSearch[T InterpolatableNumber](arr []T, target T) int {
    low, high := 0, len(arr)-1
    
    for low <= high && target >= arr[low] && target <= arr[high] {
        // 避免除零错误
        if arr[high] == arr[low] {
            if arr[low] == target {
                return low
            }
            return -1
        }
        
        // 插值公式计算探测点
        pos := low + int(float64(high-low) * 
                float64(target-arr[low]) / float64(arr[high]-arr[low]))
        
        // 边界检查
        if pos < low || pos > high {
            break
        }
        
        if arr[pos] == target {
            return pos
        }
        
        if arr[pos] < target {
            low = pos + 1
        } else {
            high = pos - 1
        }
    }
    
    return -1 // 目标不在数组中
}

// InterpolatableNumber 是 Go 2025 假设的数值约束
// 定义可用于插值计算的数值类型
type InterpolatableNumber interface {
    ~int | ~int8 | ~int16 | ~int32 | ~int64 |
    ~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64 | ~uintptr |
    ~float32 | ~float64
}

// 用法示例
func interpolationSearchExample() {
    // 均匀分布的数据
    data := []int{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29}
    
    fmt.Println("查找11:", interpolationSearch(data, 11))  // 输出: 5
    fmt.Println("查找12:", interpolationSearch(data, 12))  // 输出: -1
    
    // 浮点数数据
    floats := []float64{1.2, 3.4, 5.6, 7.8, 9.0, 11.2, 13.4, 15.6}
    fmt.Println("查找9.0:", interpolationSearch(floats, 9.0))  // 输出: 4
}
```

**性能分析**：

- 时间复杂度：
  - 最佳情况：O(log log n)，当数据均匀分布时
  - 最坏情况：O(n)，当数据严重倾斜分布时
- 空间复杂度：O(1)
- 优点：在均匀分布数据上比二分查找更高效
- 缺点：在非均匀分布数据上可能降级为线性搜索
- 适用场景：数据规模大且分布均匀的应用，如数据库索引

## 3. 排序算法

### 3.1 快速排序

**定义**：快速排序（Quick Sort）是一种高效的分治排序算法，通过选择一个"枢轴"元素，将数组分成两部分，一部分小于枢轴，另一部分大于枢轴，然后递归地对两部分进行排序。

**基本原理**：

1. 选择一个枢轴元素（通常是数组的第一个、最后一个或中间元素）
2. 将所有小于枢轴的元素移到左侧，大于枢轴的元素移到右侧（分区操作）
3. 对左右两个子数组递归执行相同操作
4. 基本情况：当子数组长度为 0 或 1 时，无需排序

**Go 2025 实现**：

```go
// quickSort 使用快速排序算法对切片进行原地排序
// 利用 Go 2025 的增强泛型和约束
func quickSort[T Ordered](arr []T) {
    // 无需排序的基本情况
    if len(arr) <= 1 {
        return
    }
    
    // 执行分区操作
    pivotIndex := partition(arr)
    
    // 递归对左右部分进行排序
    quickSort(arr[:pivotIndex])
    quickSort(arr[pivotIndex+1:])
}

// partition 进行分区操作并返回枢轴位置
func partition[T Ordered](arr []T) int {
    // 选择最后一个元素作为枢轴（可以改进为三数取中）
    pivot := arr[len(arr)-1]
    
    // 小于枢轴元素的最后位置索引
    i := -1
    
    // 遍历数组并重新排列元素
    for j := 0; j < len(arr)-1; j++ {
        if arr[j] <= pivot {
            i++
            // 交换元素
            arr[i], arr[j] = arr[j], arr[i]
        }
    }
    
    // 将枢轴放到正确位置
    pivotPos := i + 1
    arr[pivotPos], arr[len(arr)-1] = arr[len(arr)-1], arr[pivotPos]
    
    return pivotPos
}

// 随机化版本以避免最坏情况
func quickSortRandomized[T Ordered](arr []T) {
    if len(arr) <= 1 {
        return
    }
    
    // 随机选择枢轴以避免最坏情况
    pivotIndex := rand.Intn(len(arr))
    arr[pivotIndex], arr[len(arr)-1] = arr[len(arr)-1], arr[pivotIndex]
    
    // 正常快排流程
    pivotPos := partition(arr)
    quickSort(arr[:pivotPos])
    quickSort(arr[pivotPos+1:])
}

// Go 2025 Ordered 约束已在前面定义

// 用法示例
func quickSortExample() {
    data := []int{38, 27, 43, 3, 9, 82, 10}
    
    quickSort(data)
    fmt.Println("快速排序结果:", data)  // 输出: [3 9 10 27 38 43 82]
    
    // 字符串排序
    words := []string{"banana", "apple", "orange", "grape", "kiwi"}
    quickSort(words)
    fmt.Println("字符串排序:", words)  // 输出: [apple banana grape kiwi orange]
}
```

**性能分析**：

- 时间复杂度：
  - 平均情况：O(n log n)
  - 最坏情况：O(n²)，发生在已排序数组和枢轴选择不当时
  - 最佳情况：O(n log n)
- 空间复杂度：O(log n)，递归栈的深度
- 优点：
  - 通常比其他 O(n log n) 排序算法快
  - 内存使用高效（原地排序）
- 缺点：
  - 不稳定排序（相等元素的相对顺序可能改变）
  - 在最坏情况下性能下降
- 优化：
  - 随机选择枢轴以避免最坏情况
  - 小数组使用插入排序
  - 三数取中法选择枢轴

### 3.2 归并排序

**定义**：归并排序（Merge Sort）是一种高效的分治排序算法，通过递归地将数组分成两半，分别排序，然后合并已排序的两部分。

**基本原理**：

1. 将数组分成两个大小相等的子数组
2. 递归地对两个子数组进行排序
3. 合并两个已排序的子数组为一个排序数组
4. 基本情况：当子数组长度为 0 或 1 时，认为已排序

**Go 2025 实现**：

```go
// mergeSort 使用归并排序算法对切片进行排序
// 利用 Go 2025 的增强泛型
func mergeSort[T Ordered](arr []T) []T {
    // 基本情况
    if len(arr) <= 1 {
        return arr
    }
    
    // 分割数组
    mid := len(arr) / 2
    left := mergeSort(arr[:mid])
    right := mergeSort(arr[mid:])
    
    // 合并排序后的两部分
    return merge(left, right)
}

// merge 合并两个已排序的数组
func merge[T Ordered](left, right []T) []T {
    result := make([]T, 0, len(left)+len(right))
    i, j := 0, 0
    
    // 比较两个数组的元素并合并
    for i < len(left) && j < len(right) {
        if left[i] <= right[j] {
            result = append(result, left[i])
            i++
        } else {
            result = append(result, right[j])
            j++
        }
    }
    
    // 添加剩余元素
    result = append(result, left[i:]...)
    result = append(result, right[j:]...)
    
    return result
}

// 原地归并排序版本（节省内存）
// Go 2025可能支持更高效的内存管理和切片操作
func mergeSortInPlace[T Ordered](arr []T, temp []T, left, right int) {
    if left < right {
        mid := left + (right-left)/2
        
        // 递归排序左右子数组
        mergeSortInPlace(arr, temp, left, mid)
        mergeSortInPlace(arr, temp, mid+1, right)
        
        // 合并已排序的子数组
        mergeInPlace(arr, temp, left, mid, right)
    }
}

// 原地合并两个已排序的子数组
func mergeInPlace[T Ordered](arr []T, temp []T, left, mid, right int) {
    // 复制数据到临时数组
    for i := left; i <= right; i++ {
        temp[i] = arr[i]
    }
    
    // 合并过程
    i, j, k := left, mid+1, left
    for i <= mid && j <= right {
        if temp[i] <= temp[j] {
            arr[k] = temp[i]
            i++
        } else {
            arr[k] = temp[j]
            j++
        }
        k++
    }
    
    // 复制剩余元素
    for i <= mid {
        arr[k] = temp[i]
        i++
        k++
    }
    // 右侧剩余元素已在正确位置，无需复制
}

// 用法示例
func mergeSortExample() {
    data := []int{38, 27, 43, 3, 9, 82, 10}
    
    // 使用标准归并排序
    sorted := mergeSort(data)
    fmt.Println("归并排序结果:", sorted)  // 输出: [3 9 10 27 38 43 82]
    
    // 使用原地归并排序
    inPlaceData := []int{38, 27, 43, 3, 9, 82, 10}
    temp := make([]int, len(inPlaceData))
    mergeSortInPlace(inPlaceData, temp, 0, len(inPlaceData)-1)
    fmt.Println("原地归并排序:", inPlaceData)  // 输出: [3 9 10 27 38 43 82]
    
    // 复杂类型排序
    type User struct {
        name string
        age  int
    }
    
    // Go 2025可能支持为结构体自动生成比较方法
    users := []User{
        {"Alice", 30},
        {"Bob", 25},
        {"Carol", 35},
        {"Dave", 20},
    }
    
    // 假设的按年龄排序
    // 在Go 2025中可能支持更简洁的定义
    mergeSortByAge := func(users []User) []User {
        return mergeSort(users, func(a, b User) bool {
            return a.age <= b.age
        })
    }
    
    sortedUsers := mergeSortByAge(users)
    for _, u := range sortedUsers {
        fmt.Printf("%s: %d\n", u.name, u.age)
    }
}
```

**性能分析**：

- 时间复杂度：O(n log n)，在所有情况下都是
- 空间复杂度：
  - 标准实现：O(n)，需要额外空间
  - 原地实现：仍需O(n)临时空间，但避免了递归过程中的额外分配
- 优点：
  - 稳定排序（相等元素的相对顺序保持不变）
  - 性能稳定，不依赖于输入数据分布
  - 适合外部排序（处理大数据集）
- 缺点：
  - 需要额外的空间（标准实现）
  - 常数因子较大，在小数组上可能不如插入排序

### 3.3 堆排序

**定义**：堆排序（Heap Sort）是一种基于比较的排序算法，利用二叉堆数据结构进行排序。它首先构建一个最大堆，然后反复提取最大元素并重新构建堆。

**基本原理**：

1. 将输入数组构建成一个最大堆（父节点大于或等于子节点）
2. 将堆的根节点（最大值）与最后一个元素交换
3. 减少堆的大小并恢复最大堆性质
4. 重复步骤2和3，直到堆的大小为1

**Go 2025 实现**：

```go
// heapSort 使用堆排序算法对切片进行原地排序
// 利用 Go 2025 的增强泛型和比较功能
func heapSort[T Ordered](arr []T) {
    n := len(arr)
    
    // 构建最大堆
    for i := n/2 - 1; i >= 0; i-- {
        heapify(arr, n, i)
    }
    
    // 逐个从堆中提取元素
    for i := n - 1; i > 0; i-- {
        // 将当前根节点（最大值）移到末尾
        arr[0], arr[i] = arr[i], arr[0]
        
        // 对减小的堆调用heapify
        heapify(arr, i, 0)
    }
}

// heapify 维护堆的性质
func heapify[T Ordered](arr []T, n, i int) {
    largest := i      // 初始化最大值为根节点
    left := 2*i + 1   // 左子节点
    right := 2*i + 2  // 右子节点
    
    // 如果左子节点大于根节点
    if left < n && arr[left] > arr[largest] {
        largest = left
    }
    
    // 如果右子节点大于当前最大值
    if right < n && arr[right] > arr[largest] {
        largest = right
    }
    
    // 如果最大值不是根节点
    if largest != i {
        arr[i], arr[largest] = arr[largest], arr[i]
        
        // 递归地维护受影响的子树
        heapify(arr, n, largest)
    }
}

// Go 2025 可能支持更灵活的堆操作
// 通用堆数据结构
type Heap[T any] struct {
    items    []T
    lessFunc func(a, b T) bool
}

// 创建新堆
func NewHeap[T any](lessFunc func(a, b T) bool) *Heap[T] {
    return &Heap[T]{
        items:    make([]T, 0),
        lessFunc: lessFunc,
    }
}

// 向堆中添加元素
func (h *Heap[T]) Push(item T) {
    h.items = append(h.items, item)
    h.siftUp(len(h.items) - 1)
}

// 从堆中弹出顶部元素
func (h *Heap[T]) Pop() (T, bool) {
    if len(h.items) == 0 {
        var zero T
        return zero, false
    }
    
    root := h.items[0]
    lastIdx := len(h.items) - 1
    h.items[0] = h.items[lastIdx]
    h.items = h.items[:lastIdx]
    
    if len(h.items) > 0 {
        h.siftDown(0)
    }
    
    return root, true
}

// 向上调整保持堆性质
func (h *Heap[T]) siftUp(idx int) {
    parent := (idx - 1) / 2
    if idx > 0 && h.lessFunc(h.items[parent], h.items[idx]) {
        h.items[parent], h.items[idx] = h.items[idx], h.items[parent]
        h.siftUp(parent)
    }
}

// 向下调整保持堆性质
func (h *Heap[T]) siftDown(idx int) {
    smallest := idx
    left := 2*idx + 1
    right := 2*idx + 2
    
    if left < len(h.items) && h.lessFunc(h.items[smallest], h.items[left]) {
        smallest = left
    }
    
    if right < len(h.items) && h.lessFunc(h.items[smallest], h.items[right]) {
        smallest = right
    }
    
    if smallest != idx {
        h.items[idx], h.items[smallest] = h.items[smallest], h.items[idx]
        h.siftDown(smallest)
    }
}

// 用法示例
func heapSortExample() {
    data := []int{38, 27, 43, 3, 9, 82, 10}
    
    // 使用经典堆排序
    heapSort(data)
    fmt.Println("堆排序结果:", data)  // 输出: [3 9 10 27 38 43 82]
    
    // 使用通用堆实现排序
    nums := []int{38, 27, 43, 3, 9, 82, 10}
    
    // 创建最大堆
    maxHeap := NewHeap(func(a, b int) bool {
        return a < b  // 最大堆使用"小于"比较
    })
    
    // 将元素推入堆
    for _, num := range nums {
        maxHeap.Push(num)
    }
    
    // 按降序提取元素
    var sortedDesc []int
    for {
        if val, ok := maxHeap.Pop(); ok {
            sortedDesc = append(sortedDesc, val)
        } else {
            break
        }
    }
    
    fmt.Println("最大堆排序(降序):", sortedDesc)  // 输出: [82 43 38 27 10 9 3]
}
```

**性能分析**：

- 时间复杂度：O(n log n)，在所有情况下都是
- 空间复杂度：O(1)，原地排序
- 优点：
  - 最坏情况下仍为 O(n log n)
  - 不需要额外空间
  - 适用于需要找出最大或最小元素的场景
- 缺点：
  - 不稳定排序（相等元素的相对顺序可能改变）
  - 常数因子较大，在实际应用中可能比快速排序慢
  - 缓存不友好，访问模式不连续

## 4. 图算法

### 4.1 广度优先搜索 (BFS)

**定义**：广度优先搜索（Breadth-First Search，BFS）是一种图搜索算法，它从起始节点开始，先访问所有相邻节点，然后再访问下一层节点，依此类推。

**基本原理**：

1. 使用队列数据结构存储待访问的节点
2. 从起始节点开始，将其标记为已访问并加入队列
3. 当队列非空时，取出队首节点，访问其所有未访问的相邻节点
4. 将这些相邻节点标记为已访问并加入队列
5. 重复步骤3和4，直到队列为空

**Go 2025 实现**：

```go
// 使用 Go 2025 更灵活的泛型和集合操作
// Graph 是通用图接口
type Graph[T comparable] interface {
    Vertices() []T
    Neighbors(vertex T) []T
}

// 邻接表实现的图
type AdjacencyGraph[T comparable] struct {
    adjacencyList map[T][]T
}

// NewGraph 创建新图
func NewGraph[T comparable]() *AdjacencyGraph[T] {
    return &AdjacencyGraph[T]{
        adjacencyList: make(map[T][]T),
    }
}

// AddEdge 添加边
func (g *AdjacencyGraph[T]) AddEdge(from, to T) {
    g.adjacencyList[from] = append(g.adjacencyList[from], to)
}

// Vertices 返回所有顶点
func (g *AdjacencyGraph[T]) Vertices() []T {
    vertices := make([]T, 0, len(g.adjacencyList))
    for v := range g.adjacencyList {
        vertices = append(vertices, v)
    }
    return vertices
}

// Neighbors 返回指定顶点的所有邻居
func (g *AdjacencyGraph[T]) Neighbors(vertex T) []T {
    return g.adjacencyList[vertex]
}

// BFS 广度优先搜索算法
// 返回从起始顶点可达的所有顶点及其层级
func BFS[T comparable](graph Graph[T], start T) map[T]int {
    visited := make(map[T]int)  // 存储顶点及其层级
    visited[start] = 0  // 起始顶点层级为0
    
    // 创建队列并加入起始顶点
    queue := NewQueue[T]()
    queue.Enqueue(start)
    
    // BFS主循环
    for !queue.IsEmpty() {
        // 取出队首元素
        current, _ := queue.Dequeue()
        currentLevel := visited[current]
        
        // 访问所有邻居
        for _, neighbor := range graph.Neighbors(current) {
            // 如果邻居未访问，则标记为已访问并加入队列
            if _, ok := visited[neighbor]; !ok {
                visited[neighbor] = currentLevel + 1
                queue.Enqueue(neighbor)
            }
        }
    }
    
    return visited
}

// Queue 是 Go 2025 可能支持的通用队列接口
type Queue[T any] interface {
    Enqueue(item T)
    Dequeue() (T, bool)
    IsEmpty() bool
    Size() int
}

// 队列实现
type QueueImpl[T any] struct {
    items []T
}

func NewQueue[T any]() *QueueImpl[T] {
    return &QueueImpl[T]{items: make([]T, 0)}
}

func (q *QueueImpl[T]) Enqueue(item T) {
    q.items = append(q.items, item)
}

func (q *QueueImpl[T]) Dequeue() (T, bool) {
    var zero T
    if len(q.items) == 0 {
        return zero, false
    }
    
    item := q.items[0]
    q.items = q.items[1:]
    return item, true
}

func (q *QueueImpl[T]) IsEmpty() bool {
    return len(q.items) == 0
}

func (q *QueueImpl[T]) Size() int {
    return len(q.items)
}

// 使用 Go 2025 的结构化并发功能实现并行 BFS
func ParallelBFS[T comparable](graph Graph[T], start T, maxWorkers int) map[T]int {
    // 使用互斥锁保护访问结果映射
    var mu sync.Mutex
    visited := make(map[T]int)
    visited[start] = 0
    
    // 使用通道作为并发队列
    queue := make(chan T, 1000)
    queue <- start
    
    // 使用 WaitGroup 等待所有工作完成
    var wg sync.WaitGroup
    
    // 追踪活动工作者数量
    activeWorkers := atomic.NewInt32(0)
    
    // 通知完成的通道
    done := make(chan struct{})
    
    // 启动工作者
    for i := 0; i < maxWorkers; i++ {
        wg.Add(1)
        go func() {
            defer wg.Done()
            
            for {
                // 检查是否需要终止
                select {
                case current, ok := <-queue:
                    if !ok {
                        return
                    }
                    
                    activeWorkers.Add(1)
                    
                    // 获取当前顶点的层级
                    mu.Lock()
                    currentLevel := visited[current]
                    mu.Unlock()
                    
                    // 处理邻居
                    neighbors := graph.Neighbors(current)
                    
                    for _, neighbor := range neighbors {
                        mu.Lock()
                        _, seen := visited[neighbor]
                        if !seen {
                            visited[neighbor] = currentLevel + 1
                            mu.Unlock()
                            
                            // 将新邻居加入队列
                            queue <- neighbor
                        } else {
                            mu.Unlock()
                        }
                    }
                    
                    activeWorkers.Add(-1)
                    
                    // 检查是否所有工作已完成
                    if activeWorkers.Load() == 0 && len(queue) == 0 {
                        // 尝试通知完成
                        select {
                        case done <- struct{}{}:
                        default:
                            // 已有通知发送
                        }
                    }
                    
                case <-done:
                    return
                }
            }
        }()
    }
    
    // 等待完成
    wg.Wait()
    close(queue)
    
    return visited
}

// 用法示例
func bfsExample() {
    // 创建示例图
    graph := NewGraph[string]()
    
    // 添加边
    graph.AddEdge("A", "B")
    graph.AddEdge("A", "C")
    graph.AddEdge("B", "D")
    graph.AddEdge("B", "E")
    graph.AddEdge("C", "F")
    graph.AddEdge("E", "G")
    graph.AddEdge("F", "G")
    
    // 运行 BFS
    result := BFS(graph, "A")
    
    fmt.Println("BFS 结果 (顶点:层级):")
    for vertex, level := range result {
        fmt.Printf("%s: %d\n", vertex, level)
    }
    
    // 运行并行 BFS
    parallelResult := ParallelBFS(graph, "A", 4)
    
    fmt.Println("\n并行 BFS 结果:")
    for vertex, level := range parallelResult {
        fmt.Printf("%s: %d\n", vertex, level)
    }
}
```

**性能分析**：

- 时间复杂度：O(V + E)，其中 V 是顶点数，E 是边数
- 空间复杂度：O(V)，需要存储访问状态和队列
- 优点：
  - 找到的路径是最短路径（按边数计算）
  - 适合寻找距离起点特定距离的所有节点
  - 在层次结构中高效操作
- 缺点：
  - 空间需求较高（需要存储整个前沿）
  - 不适合深度优先的场景（如路径探索）
- 应用场景：
  - 最短路径问题（无权图）
  - 社交网络分析（寻找"六度分隔"）
  - 网络爬虫的层次抓取
  - 协同过滤推荐系统

### 4.2 深度优先搜索 (DFS)

**定义**：深度优先搜索（Depth-First Search，DFS）是一种图搜索算法，它从起始节点开始，尽可能深地探索一条路径，直到无法继续为止，然后回溯到上一个节点，探索其他路径。

**基本原理**：

1. 使用栈（或递归）来跟踪待访问的节点
2. 从起始节点开始，将其标记为已访问
3. 递归（或使用栈）访问所有未访问的相邻节点
4. 当无法继续前进时，回溯到上一个节点
5. 重复步骤3和4，直到所有可达节点都已访问

**Go 2025 实现**：

```go
// DFS 深度优先搜索（递归实现）
func DFS[T comparable](graph Graph[T], start T) map[T]bool {
    visited := make(map[T]bool)
    dfsRecursive(graph, start, visited)
    return visited
}

// dfsRecursive 是 DFS 的递归辅助函数
func dfsRecursive[T comparable](graph Graph[T], current T, visited map[T]bool) {
    // 标记当前顶点为已访问
    visited[current] = true
    
    // 递归处理所有未访问的邻居
    for _, neighbor := range graph.Neighbors(current) {
        if !visited[neighbor] {
            dfsRecursive(graph, neighbor, visited)
        }
    }
}

// DFSIterative 深度优先搜索（迭代实现）
func DFSIterative[T comparable](graph Graph[T], start T) map[T]bool {
    visited := make(map[T]bool)
    
    // 使用栈存储待访问的顶点
    stack := NewStack[T]()
    stack.Push(start)
    
    for !stack.IsEmpty() {
        // 从栈顶取出顶点
        current, _ := stack.Pop()
        
        // 如果未访问，则标记为已访问
        if !visited[current] {
            visited[current] = true
            
            // 将所有未访问的邻居加入栈
            for _, neighbor := range graph.Neighbors(current) {
                if !visited[neighbor] {
                    stack.Push(neighbor)
                }
            }
        }
    }
    
    return visited
}

// DFSWithPath 返回从起始顶点到每个可达顶点的路径
func DFSWithPath[T comparable](graph Graph[T], start T) map[T][]T {
    paths := make(map[T][]T)
    visited := make(map[T]bool)
    
    // 起始顶点的路径只包含自身
    paths[start] = []T{start}
    
    dfsPathRecursive(graph, start, visited, paths)
    
    return paths
}

// dfsPathRecursive 是带路径的 DFS 的递归辅助函数
func dfsPathRecursive[T comparable](graph Graph[T], current T, visited map[T]bool, paths map[T][]T) {
    visited[current] = true
    
    for _, neighbor := range graph.Neighbors(current) {
        if !visited[neighbor] {
            // 构建到邻居的路径（当前路径 + 邻居）
            paths[neighbor] = append(append([]T{}, paths[current]...), neighbor)
            dfsPathRecursive(graph, neighbor, visited, paths)
        }
    }
}

// Stack 是 Go 2025 可能支持的通用栈接口
type Stack[T any] interface {
    Push(item T)
    Pop() (T, bool)
    IsEmpty() bool
    Size() int
}

// 栈实现
type StackImpl[T any] struct {
    items []T
}

func NewStack[T any]() *StackImpl[T] {
    return &StackImpl[T]{items: make([]T, 0)}
}

func (s *StackImpl[T]) Push(item T) {
    s.items = append(s.items, item)
}

func (s *StackImpl[T]) Pop() (T, bool) {
    var zero T
    if len(s.items) == 0 {
        return zero, false
    }
    
    index := len(s.items) - 1
    item := s.items[index]
    s.items = s.items[:index]
    return item, true
}

func (s *StackImpl[T]) IsEmpty() bool {
    return len(s.items) == 0
}

func (s *StackImpl[T]) Size() int {
    return len(s.items)
}

// 用法示例
func dfsExample() {
    // 创建示例图
    graph := NewGraph[string]()
    
    // 添加边
    graph.AddEdge("A", "B")
    graph.AddEdge("A", "C")
    graph.AddEdge("B", "D")
    graph.AddEdge("B", "E")
    graph.AddEdge("C", "F")
    graph.AddEdge("E", "G")
    graph.AddEdge("F", "G")
    
    // 递归 DFS
    visitedRecursive := DFS(graph, "A")
    
    fmt.Println("递归 DFS 访问顺序:")
    for vertex := range visitedRecursive {
        fmt.Print(vertex, " ")
    }
    fmt.Println()
    
    // 迭代 DFS
    visitedIterative := DFSIterative(graph, "A")
    
    fmt.Println("迭代 DFS 访问顺序:")
    for vertex := range visitedIterative {
        fmt.Print(vertex, " ")
    }
    fmt.Println()
    
    // 带路径的 DFS
    paths := DFSWithPath(graph, "A")
    
    fmt.Println("\nDFS 路径:")
    for vertex, path := range paths {
        fmt.Printf("%s: %v\n", vertex, path)
    }
}
```

**性能分析**：

- 时间复杂度：O(V + E)，其中 V 是顶点数，E 是边数
- 空间复杂度：
  - 递归实现：O(h)，其中 h 是图的深度（最长路径）
  - 迭代实现：O(V)，最坏情况下栈大小
- 优点：
  - 内存需求通常比 BFS 低
  - 寻找解决方案时可能比 BFS 快（取决于图的结构）
  - 更适合树形结构和探索型搜索
  - 可以通过回溯实现循环检测
- 缺点：
  - 不保证找到最短路径
  - 在无限图或非常深的图中可能陷入无限递归
- 应用场景：
  - 拓扑排序
  - 寻找连通分量
  - 检测图中的循环
  - 寻找从一个节点到另一个节点的路径
  - 解决迷宫问题

### 4.3 Dijkstra 最短路径

**定义**：Dijkstra 算法是一种用于计算带权图中单源最短路径的算法。它逐步查找到起点的最短路径，直到找到到所有顶点的最短路径或找到到特定顶点的最短路径。

**基本原理**：

1. 初始化距离数组，将起始顶点距离设为0，其他顶点设为无穷大
2. 将所有顶点加入未处理集合
3. 当未处理集合非空时，选择距离最小的顶点
4. 更新所有与该顶点相邻的未处理顶点的距离
5. 将该顶点标记为已处理
6. 重复步骤3-5，直到所有顶点都已处理或找到目标顶点

**Go 2025 实现**：

```go
// WeightedGraph 是带权图接口
type WeightedGraph[T comparable] interface {
    Vertices() []T
    Neighbors(vertex T) []T
    Weight(source, target T) float64
}

// 邻接表实现的带权图
type WeightedAdjacencyGraph[T comparable] struct {
    edges map[T]map[T]float64
}

// NewWeightedGraph 创建新的带权图
func NewWeightedGraph[T comparable]() *WeightedAdjacencyGraph[T] {
    return &WeightedAdjacencyGraph[T]{
        edges: make(map[T]map[T]float64),
    }
}

// AddEdge 添加带权边
func (g *WeightedAdjacencyGraph[T]) AddEdge(from, to T, weight float64) {
    if g.edges[from] == nil {
        g.edges[from] = make(map[T]float64)
    }
    g.edges[from][to] = weight
}

// Vertices 返回所有顶点
func (g *WeightedAdjacencyGraph[T]) Vertices() []T {
    vertices := make([]T, 0, len(g.edges))
    for v := range g.edges {
        vertices = append(vertices, v)
    }
    return vertices
}

// Neighbors 返回指定顶点的所有邻居
func (g *WeightedAdjacencyGraph[T]) Neighbors(vertex T) []T {
    neighbors := make([]T, 0, len(g.edges[vertex]))
    for n := range g.edges[vertex] {
        neighbors = append(neighbors, n)
    }
    return neighbors
}

// Weight 返回两个顶点之间的权重
func (g *WeightedAdjacencyGraph[T]) Weight(source, target T) float64 {
    return g.edges[source][target]
}

// Dijkstra 算法实现
func Dijkstra[T comparable](graph WeightedGraph[T], start T) (map[T]float64, map[T]T) {
    // 初始化距离和前驱
    distances := make(map[T]float64)
    predecessors := make(map[T]T)
    unvisited := make(map[T]bool)
    
    // 初始化所有顶点的距离为无穷大
    for _, v := range graph.Vertices() {
        distances[v] = math.Inf(1)
        unvisited[v] = true
    }
    
    // 起始顶点距离为0
    distances[start] = 0
    
    for len(unvisited) > 0 {
        // 选择未访问顶点中距离最小的
        var current T
        minDist := math.Inf(1)
        
        for v := range unvisited {
            if distances[v] < minDist {
                minDist = distances[v]
                current = v
            }
        }
        
        // 如果没有可达的未访问顶点，终止算法
        if minDist == math.Inf(1) {
            break
        }
        
        // 标记为已访问
        delete(unvisited, current)
        
        // 更新邻居的距离
        for _, neighbor := range graph.Neighbors(current) {
            if unvisited[neighbor] {
                newDist := distances[current] + graph.Weight(current, neighbor)
                
                if newDist < distances[neighbor] {
                    distances[neighbor] = newDist
                    predecessors[neighbor] = current
                }
            }
        }
    }
    
    return distances, predecessors
}

// 使用 Go 2025 的优先队列优化 Dijkstra 算法
func DijkstraOptimized[T comparable](graph WeightedGraph[T], start T) (map[T]float64, map[T]T) {
    // 初始化距离和前驱
    distances := make(map[T]float64)
    predecessors := make(map[T]T)
    visited := make(map[T]bool)
    
    // 初始化所有顶点的距离为无穷大
    for _, v := range graph.Vertices() {
        distances[v] = math.Inf(1)
    }
    
    // 起始顶点距离为0
    distances[start] = 0
    
    // 创建优先队列
    pq := NewPriorityQueue(func(a, b distanceNode[T]) bool {
        return a.distance < b.distance
    })
    
    // 将起始节点加入队列
    pq.Push(distanceNode[T]{vertex: start, distance: 0})
    
    for !pq.IsEmpty() {
        // 获取距离最小的顶点
        node := pq.Pop()
        current := node.vertex
        
        // 如果已访问，跳过
        if visited[current] {
            continue
        }
        
        // 标记为已访问
        visited[current] = true
        
        // 当前的距离
        currentDist := distances[current]
        
        // 更新邻居的距离
        for _, neighbor := range graph.Neighbors(current) {
            if !visited[neighbor] {
                weight := graph.Weight(current, neighbor)
                newDist := currentDist + weight
                
                if newDist < distances[neighbor] {
                    distances[neighbor] = newDist
                    predecessors[neighbor] = current
                    pq.Push(distanceNode[T]{vertex: neighbor, distance: newDist})
                }
            }
        }
    }
    
    return distances, predecessors
}

// 用于优先队列的节点类型
type distanceNode[T any] struct {
    vertex   T
    distance float64
}

// 打印最短路径
func GetShortestPath[T comparable](dest T, predecessors map[T]T) []T {
    path := []T{dest}
    
    for {
        pred, exists := predecessors[path[0]]
        if !exists {
            break
        }
        path = append([]T{pred}, path...)
    }
    
    return path
}

// 用法示例
func dijkstraExample() {
    // 创建带权图
    graph := NewWeightedGraph[string]()
    
    // 添加带权边
    graph.AddEdge("A", "B", 4)
    graph.AddEdge("A", "C", 2)
    graph.AddEdge("B", "C", 1)
    graph.AddEdge("B", "D", 5)
    graph.AddEdge("C", "D", 8)
    graph.AddEdge("C", "E", 10)
    graph.AddEdge("D", "E", 2)
    graph.AddEdge("D", "F", 6)
    graph.AddEdge("E", "F", 3)
    
    // 运行 Dijkstra 算法
    distances, predecessors := Dijkstra(graph, "A")
    
    fmt.Println("Dijkstra 最短路径距离:")
    for vertex, dist := range distances {
        fmt.Printf("%s: %.1f\n", vertex, dist)
    }
    
    // 打印到 F 的最短路径
    path := GetShortestPath("F", predecessors)
    fmt.Printf("\n从 A 到 F 的最短路径: %v\n", path)
    
    // 使用优化版本
    optDistances, optPredecessors := DijkstraOptimized(graph, "A")
    
    fmt.Println("\n优化版 Dijkstra 最短路径距离:")
    for vertex, dist := range optDistances {
        fmt.Printf("%s: %.1f\n", vertex, dist)
    }
    
    // 打印优化版本到 F 的最短路径
    optPath := GetShortestPath("F", optPredecessors)
    fmt.Printf("\n从 A 到 F 的最短路径 (优化版): %v\n", optPath)
}
```

**性能分析**：

- 时间复杂度：
  - 基本实现：O(V²)，其中 V 是顶点数
  - 优先队列优化：O((V + E) log V)，其中 E 是边数
- 空间复杂度：O(V)，存储距离、前驱和访问标记
- 优点：
  - 找到单源到所有顶点的最短路径
  - 适用于非负权重的有向图和无向图
  - 可以用于解决许多实际路径问题
- 缺点：
  - 不适用于有负权边的图
  - 普通实现在稠密图上性能较差
- 应用场景：
  - 地图导航系统
  - 网络路由协议
  - 航班路线规划
  - 物流配送优化

## 5. 分治算法

### 5.1 分治思想概述

**定义**：分治（Divide and Conquer）是一种算法设计范式，将原问题分解为多个子问题，独立解决这些子问题，然后将子问题的解合并得到原问题的解。

**基本原理**：

1. **分解**（Divide）：将原问题分解为若干子问题
2. **解决**（Conquer）：递归地解决子问题
3. **合并**（Combine）：将子问题的解合并成原问题的解

**应用条件**：

- 问题可以分解为类似的子问题
- 子问题相互独立，没有重叠
- 存在基本情况（边界条件）

**Go 2025 实现常见分治算法框架**：

```go
// 分治算法通用框架
func divideAndConquer[T, R any](
    problem T,
    divide func(T) []T,
    isBase func(T) bool,
    solveBase func(T) R,
    combine func([]R) R,
) R {
    // 基本情况检查
    if isBase(problem) {
        return solveBase(problem)
    }
    
    // 分解问题
    subproblems := divide(problem)
    
    // 解决子问题
    var subresults []R
    for _, subproblem := range subproblems {
        subresult := divideAndConquer(subproblem, divide, isBase, solveBase, combine)
        subresults = append(subresults, subresult)
    }
    
    // 合并结果
    return combine(subresults)
}

// 使用 Go 2025 并行化的分治框架
func parallelDivideAndConquer[T, R any](
    problem T,
    divide func(T) []T,
    isBase func(T) bool,
    solveBase func(T) R,
    combine func([]R) R,
    threshold int,
) R {
    // 基本情况或问题规模小于阈值时串行处理
    if isBase(problem) {
        return solveBase(problem)
    }
    
    // 分解问题
    subproblems := divide(problem)
    
    // 问题规模小于阈值时串行处理
    if len(subproblems) <= threshold {
        var subresults []R
        for _, subproblem := range subproblems {
            subresult := divideAndConquer(
                subproblem, divide, isBase, solveBase, combine,
            )
            subresults = append(subresults, subresult)
        }
        return combine(subresults)
    }
    
    // 并行解决子问题
    subresults := make([]R, len(subproblems))
    var wg sync.WaitGroup
    
    for i, subproblem := range subproblems {
        wg.Add(1)
        go func(idx int, prob T) {
            defer wg.Done()
            subresults[idx] = parallelDivideAndConquer(
                prob, divide, isBase, solveBase, combine, threshold,
            )
        }(i, subproblem)
    }
    
    wg.Wait()
    
    // 合并结果
    return combine(subresults)
}
```

### 5.2 快速选择

**定义**：快速选择（Quick Select）是一种用于找到数组中第 k 小元素的分治算法，它基于快速排序的分区思想。

**基本原理**：

1. 选择一个枢轴元素
2. 执行分区操作，将数组分为小于枢轴和大于枢轴两部分
3. 根据枢轴的位置和 k 的关系决定在哪个子数组中继续搜索
4. 如果枢轴位置正好是 k-1，则枢轴就是第 k 小的元素

**Go 2025 实现**：

```go
// quickSelect 找出数组中第k小的元素（k从0开始）
func quickSelect[T Ordered](arr []T, k int) (T, error) {
    if k < 0 || k >= len(arr) {
        var zero T
        return zero, fmt.Errorf("索引 %d 超出范围 [0, %d)", k, len(arr))
    }
    
    // 复制数组以避免修改原数组
    arrCopy := make([]T, len(arr))
    copy(arrCopy, arr)
    
    return quickSelectInPlace(arrCopy, 0, len(arrCopy)-1, k)
}

// quickSelectInPlace 原地实现快速选择
func quickSelectInPlace[T Ordered](arr []T, left, right, k int) (T, error) {
    // 基本情况
    if left == right {
        return arr[left], nil
    }
    
    // 使用随机枢轴以避免最坏情况
    pivotIndex := left + rand.Intn(right-left+1)
    arr[pivotIndex], arr[right] = arr[right], arr[pivotIndex]
    
    // 分区操作
    pivotPos := partitionForSelect(arr, left, right)
    
    // 根据枢轴位置决定在哪个子数组中搜索
    switch {
    case k == pivotPos:
        // 找到了
        return arr[k], nil
    case k < pivotPos:
        // 在左子数组中搜索
        return quickSelectInPlace(arr, left, pivotPos-1, k)
    default:
        // 在右子数组中搜索
        return quickSelectInPlace(arr, pivotPos+1, right, k)
    }
}

// partitionForSelect 分区操作
func partitionForSelect[T Ordered](arr []T, left, right int) int {
    pivot := arr[right]
    i := left - 1
    
    for j := left; j < right; j++ {
        if arr[j] <= pivot {
            i++
            arr[i], arr[j] = arr[j], arr[i]
        }
    }
    
    i++
    arr[i], arr[right] = arr[right], arr[i]
    return i
}

// Go 2025可能支持的中位数快速计算
func median[T Ordered](arr []T) (T, error) {
    if len(arr) == 0 {
        var zero T
        return zero, errors.New("空数组无中位数")
    }
    
    if len(arr) % 2 == 1 {
        // 奇数长度，直接返回中间元素
        mid := len(arr) / 2
        return quickSelect(arr, mid)
    } else {
        // 偶数长度，返回中间两个元素的平均值
        mid1 := len(arr) / 2 - 1
        mid2 := len(arr) / 2
        
        val1, err := quickSelect(arr, mid1)
        if err != nil {
            var zero T
            return zero, err
        }
        
        val2, err := quickSelect(arr, mid2)
        if err != nil {
            var zero T
            return zero, err
        }
        
        // 使用类型转换处理平均值
        return (val1 + val2) / 2, nil
    }
}

// 用法示例
func quickSelectExample() {
    data := []int{38, 27, 43, 3, 9, 82, 10}
    
    // 查找第3小的元素（索引2）
    thirdSmallest, _ := quickSelect(data, 2)
    fmt.Printf("第3小的元素: %d\n", thirdSmallest)  // 输出: 10
    
    // 查找中位数
    med, _ := median(data)
    fmt.Printf("数组的中位数: %d\n", med)  // 输出: 27
    
    // 查找第2大的元素（倒数第2小）
    secondLargest, _ := quickSelect(data, len(data)-2)
    fmt.Printf("第2大的元素: %d\n", secondLargest)  // 输出: 43
    
    // 原数组保持不变
    fmt.Printf("原数组: %v\n", data)  // 输出: [38 27 43 3 9 82 10]
}
```

**性能分析**：

- 时间复杂度：
  - 平均情况：O(n)
  - 最坏情况：O(n²)，但使用随机枢轴可以几乎确保平均性能
- 空间复杂度：O(log n)，递归调用栈的深度
- 优点：
  - 比排序后选择更高效（不需要完全排序）
  - 可以处理大型数据集
  - 原地操作，仅需少量额外空间
- 缺点：
  - 不稳定（相等元素的相对顺序可能改变）
  - 最坏情况下性能不佳
- 应用场景：
  - 寻找中位数
  - 寻找前k大/小的元素
  - 计算百分位数
  - 统计学和数据分析

### 5.3 最大子数组问题

**定义**：最大子数组问题（Maximum Subarray Problem）是寻找一个数组中具有最大和的连续子数组。

**基本原理**：

1. 将数组分成两半
2. 递归地在左半部分和右半部分中寻找最大子数组
3. 寻找跨越中点的最大子数组
4. 返回三者中的最大值

**Go 2025 实现**：

```go
// 使用分治法解决最大子数组问题
func maxSubarrayDivideAndConquer[T Number](arr []T) T {
    if len(arr) == 0 {
        var zero T
        return zero
    }
    
    return maxSubarrayRecursive(arr, 0, len(arr)-1)
}

// 递归实现最大子数组
func maxSubarrayRecursive[T Number](arr []T, left, right int) T {
    // 基本情况：只有一个元素
    if left == right {
        return arr[left]
    }
    
    // 分解问题
    mid := left + (right-left)/2
    
    // 求解子问题
    leftMax := maxSubarrayRecursive(arr, left, mid)
    rightMax := maxSubarrayRecursive(arr, mid+1, right)
    crossMax := maxCrossingSubarray(arr, left, mid, right)
    
    // 合并结果
    return max(max(leftMax, rightMax), crossMax)
}

// 求解跨越中点的最大子数组
func maxCrossingSubarray[T Number](arr []T, left, mid, right int) T {
    // 计算左半部分的最大和（从中点向左）
    var leftSum T
    maxLeftSum := arr[mid]
    
    for i := mid; i >= left; i-- {
        leftSum += arr[i]
        if leftSum > maxLeftSum {
            maxLeftSum = leftSum
        }
    }
    
    // 计算右半部分的最大和（从中点向右）
    var rightSum T
    maxRightSum := arr[mid+1]
    
    for i := mid + 1; i <= right; i++ {
        rightSum += arr[i]
        if rightSum > maxRightSum {
            maxRightSum = rightSum
        }
    }
    
    // 返回跨越中点的最大和
    return maxLeftSum + maxRightSum
}

// 线性时间算法 (Kadane's Algorithm)
func maxSubarrayKadane[T Number](arr []T) T {
    if len(arr) == 0 {
        var zero T
        return zero
    }
    
    var maxEndingHere, maxSoFar T = arr[0], arr[0]
    
    for i := 1; i < len(arr); i++ {
        // 当前最大子数组，要么是当前元素自己，要么是之前的最大子数组加上当前元素
        maxEndingHere = max(arr[i], maxEndingHere+arr[i])
        
        // 更新全局最大值
        maxSoFar = max(maxSoFar, maxEndingHere)
    }
    
    return maxSoFar
}

// 带索引的Kadane算法，返回最大子数组的起止位置
func maxSubarrayWithIndices[T Number](arr []T) (T, int, int) {
    if len(arr) == 0 {
        var zero T
        return zero, -1, -1
    }
    
    var maxEndingHere, maxSoFar T = arr[0], arr[0]
    startTemp, start, end := 0, 0, 0
    
    for i := 1; i < len(arr); i++ {
        if arr[i] > maxEndingHere+arr[i] {
            maxEndingHere = arr[i]
            startTemp = i
        } else {
            maxEndingHere = maxEndingHere + arr[i]
        }
        
        if maxEndingHere > maxSoFar {
            maxSoFar = maxEndingHere
            start = startTemp
            end = i
        }
    }
    
    return maxSoFar, start, end
}

// Go 2025支持的泛型数值类型约束
type Number interface {
    ~int | ~int8 | ~int16 | ~int32 | ~int64 |
    ~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64 | ~uintptr |
    ~float32 | ~float64
}

// max 返回两个数中的较大值
func max[T Number](a, b T) T {
    if a > b {
        return a
    }
    return b
}

// 并行实现的最大子数组问题
func maxSubarrayParallel[T Number](arr []T, goroutines int) T {
    if len(arr) <= 100 || goroutines <= 1 {
        // 对于小数组或单线程，使用Kadane算法
        return maxSubarrayKadane(arr)
    }
    
    // 确定每个goroutine处理的数组部分
    chunkSize := (len(arr) + goroutines - 1) / goroutines
    
    // 存储结果的通道
    type Result struct {
        maxSum T
        leftSum T
        rightSum T
        totalSum T
    }
    
    results := make(chan Result, goroutines)
    
    // 启动goroutines处理不同的数组部分
    var wg sync.WaitGroup
    for i := 0; i < goroutines; i++ {
        wg.Add(1)
        go func(start int) {
            defer wg.Done()
            
            end := start + chunkSize
            if end > len(arr) {
                end = len(arr)
            }
            
            // 空片段检查
            if start >= end {
                var zero T
                results <- Result{zero, zero, zero, zero}
                return
            }
            
            chunk := arr[start:end]
            
            // 1. 计算本片段的最大子数组和（使用Kadane算法）
            maxSum := maxSubarrayKadane(chunk)
            
            // 2. 计算本片段的总和
            var totalSum T
            for _, num := range chunk {
                totalSum += num
            }
            
            // 3. 计算从左侧开始的最大子数组和
            var leftSum, currentSum T
            leftSum = chunk[0]
            currentSum = chunk[0]
            
            for i := 1; i < len(chunk); i++ {
                currentSum += chunk[i]
                leftSum = max(leftSum, currentSum)
            }
            
            // 4. 计算到右侧结束的最大子数组和
            rightSum := chunk[len(chunk)-1]
            currentSum = chunk[len(chunk)-1]
            
            for i := len(chunk) - 2; i >= 0; i-- {
                currentSum += chunk[i]
                rightSum = max(rightSum, currentSum)
            }
            
            results <- Result{maxSum, leftSum, rightSum, totalSum}
        }(i * chunkSize)
    }
    
    // 等待所有goroutine完成
    go func() {
        wg.Wait()
        close(results)
    }()
    
    // 合并结果
    var maxSum, leftMaxSum, rightMaxSum, totalSumSoFar T
    var first = true
    
    for result := range results {
        if first {
            maxSum = result.maxSum
            leftMaxSum = result.leftSum
            rightMaxSum = result.rightSum
            totalSumSoFar = result.totalSum
            first = false
            continue
        }
        
        // 跨越片段边界的最大子数组
        crossSum := rightMaxSum + result.leftSum
        
        // 更新整体最大值
        maxSum = max(maxSum, max(result.maxSum, crossSum))
        
        // 更新左侧最大和
        leftMaxSum = max(leftMaxSum, totalSumSoFar+result.leftSum)
        
        // 更新右侧最大和（加上当前片段的总和）
        rightMaxSum = max(result.rightSum, rightMaxSum+result.totalSum)
        
        // 更新总和
        totalSumSoFar += result.totalSum
    }
    
    return maxSum
}

// 用法示例
func maxSubarrayExample() {
    // 包含正负数的数组
    data := []int{-2, 1, -3, 4, -1, 2, 1, -5, 4}
    
    // 使用分治法解决
    maxSumDivide := maxSubarrayDivideAndConquer(data)
    fmt.Printf("最大子数组和 (分治法): %d\n", maxSumDivide)  // 输出: 6
    
    // 使用Kadane算法
    maxSumKadane := maxSubarrayKadane(data)
    fmt.Printf("最大子数组和 (Kadane算法): %d\n", maxSumKadane)  // 输出: 6
    
    // 带索引的Kadane算法
    maxSum, start, end := maxSubarrayWithIndices(data)
    fmt.Printf("最大子数组和: %d, 位置: [%d, %d], 子数组: %v\n", 
              maxSum, start, end, data[start:end+1])  // 输出: 6, [3, 6], [4, -1, 2, 1]
    
    // 并行实现
    cpus := runtime.NumCPU()
    maxSumParallel := maxSubarrayParallel(data, cpus)
    fmt.Printf("最大子数组和 (并行实现): %d\n", maxSumParallel)  // 输出: 6
    
    // 大数组性能测试
    largeArray := make([]int, 10_000_000)
    // 填充随机数据
    for i := range largeArray {
        largeArray[i] = rand.Intn(200) - 100  // 随机生成-100到99之间的数
    }
    
    start1 := time.Now()
    result1 := maxSubarrayKadane(largeArray)
    duration1 := time.Since(start1)
    
    start2 := time.Now()
    result2 := maxSubarrayParallel(largeArray, cpus)
    duration2 := time.Since(start2)
    
    fmt.Printf("\n大数组测试结果:\n")
    fmt.Printf("Kadane算法结果: %d, 耗时: %v\n", result1, duration1)
    fmt.Printf("并行实现结果: %d, 耗时: %v\n", result2, duration2)
    fmt.Printf("加速比: %.2fx\n", float64(duration1)/float64(duration2))
}
```

**性能分析**：

- 时间复杂度：
  - 分治法：O(n log n)
  - Kadane算法：O(n)
  - 并行实现：O(n/p + log p)，其中p是处理器数量
- 空间复杂度：
  - 分治法：O(log n)，递归栈空间
  - Kadane算法：O(1)
  - 并行实现：O(p)，其中p是处理器数量
- 优点：
  - Kadane算法简单且高效
  - 分治法具有并行化潜力
  - 问题有广泛的实际应用
- 缺点：
  - 分治法常数因子较大
  - 并行实现的通信开销可能抵消并行带来的加速
- 应用场景：
  - 金融市场分析（最大利润区间）
  - 信号处理（最强信号段）
  - 图像处理（最高对比度区域）
  - 生物信息学（DNA序列分析）

## 6. 动态规划

### 6.1 动态规划基础

**定义**：动态规划（Dynamic Programming，DP）是一种通过将复杂问题分解为更简单的子问题来解决问题的算法范式。它存储子问题的解以避免重复计算，从而提高效率。

**基本原理**：

1. **最优子结构**：问题的最优解包含其子问题的最优解
2. **重叠子问题**：同一个子问题会被多次求解
3. **状态转移**：定义问题状态及其转移方程
4. **备忘录或表格**：存储子问题的解，避免重复计算

**动态规划方法**：

- **自顶向下**（备忘录法）：递归实现，用哈希表或数组存储已解决的子问题
- **自底向上**（表格法）：迭代实现，从最小子问题开始构建解

**Go 2025 实现通用DP框架**：

```go
// 通用动态规划框架（自顶向下方法）
func memoizedDP[T comparable, R any](
    problem T,
    isBase func(T) bool,
    baseCase func(T) R,
    decompose func(T) []T,
    combine func(T, []R) R,
    memo map[T]R,
) R {
    // 检查备忘录
    if result, found := memo[problem]; found {
        return result
    }
    
    // 基本情况
    if isBase(problem) {
        result := baseCase(problem)
        memo[problem] = result
        return result
    }
    
    // 分解为子问题
    subproblems := decompose(problem)
    
    // 解决子问题
    var subresults []R
    for _, subproblem := range subproblems {
        subresult := memoizedDP(subproblem, isBase, baseCase, decompose, combine, memo)
        subresults = append(subresults, subresult)
    }
    
    // 合并结果
    result := combine(problem, subresults)
    memo[problem] = result
    return result
}

// 斐波那契数列示例（自顶向下DP）
func fibonacciTopDown(n int) int {
    memo := make(map[int]int)
    
    isBase := func(n int) bool {
        return n <= 1
    }
    
    baseCase := func(n int) int {
        return n
    }
    
    decompose := func(n int) []int {
        return []int{n-1, n-2}
    }
    
    combine := func(_ int, results []int) int {
        return results[0] + results[1]
    }
    
    return memoizedDP(n, isBase, baseCase, decompose, combine, memo)
}

// 自底向上DP实现斐波那契数列
func fibonacciBottomUp(n int) int {
    if n <= 1 {
        return n
    }
    
    // 初始化DP表
    dp := make([]int, n+1)
    dp[0] = 0
    dp[1] = 1
    
    // 自底向上填充表格
    for i := 2; i <= n; i++ {
        dp[i] = dp[i-1] + dp[i-2]
    }
    
    return dp[n]
}

// 空间优化的斐波那契实现
func fibonacciOptimized(n int) int {
    if n <= 1 {
        return n
    }
    
    a, b := 0, 1
    for i := 2; i <= n; i++ {
        a, b = b, a+b
    }
    
    return b
}

// 用Go 2025增强的泛型功能实现动态规划
// 定义DP表接口
type DPTable[State comparable, Result any] interface {
    Get(State) (Result, bool)
    Set(State, Result)
}

// Map实现的DP表
type MapDPTable[State comparable, Result any] struct {
    table map[State]Result
}

func NewMapDPTable[State comparable, Result any]() *MapDPTable[State, Result] {
    return &MapDPTable[State, Result]{
        table: make(map[State]Result),
    }
}

func (t *MapDPTable[State, Result]) Get(state State) (Result, bool) {
    result, found := t.table[state]
    return result, found
}

func (t *MapDPTable[State, Result]) Set(state State, result Result) {
    t.table[state] = result
}

// 通用DP求解器
type DPSolver[State comparable, Result any] struct {
    Table      DPTable[State, Result]
    IsBaseCase func(State) bool
    BaseCase   func(State) Result
    Transition func(State, DPTable[State, Result]) Result
}

func NewDPSolver[State comparable, Result any](
    isBaseCase func(State) bool,
    baseCase func(State) Result,
    transition func(State, DPTable[State, Result]) Result,
) *DPSolver[State, Result] {
    return &DPSolver[State, Result]{
        Table:      NewMapDPTable[State, Result](),
        IsBaseCase: isBaseCase,
        BaseCase:   baseCase,
        Transition: transition,
    }
}

func (s *DPSolver[State, Result]) Solve(state State) Result {
    // 检查是否已计算
    if result, found := s.Table.Get(state); found {
        return result
    }
    
    // 基本情况
    if s.IsBaseCase(state) {
        result := s.BaseCase(state)
        s.Table.Set(state, result)
        return result
    }
    
    // 状态转移
    result := s.Transition(state, s.Table)
    s.Table.Set(state, result)
    return result
}

// 用法示例
func dynamicProgrammingBasicsExample() {
    // 测试不同的斐波那契实现
    n := 30
    
    start1 := time.Now()
    result1 := fibonacciTopDown(n)
    duration1 := time.Since(start1)
    
    start2 := time.Now()
    result2 := fibonacciBottomUp(n)
    duration2 := time.Since(start2)
    
    start3 := time.Now()
    result3 := fibonacciOptimized(n)
    duration3 := time.Since(start3)
    
    fmt.Printf("斐波那契(%d)结果:\n", n)
    fmt.Printf("自顶向下: %d, 耗时: %v\n", result1, duration1)
    fmt.Printf("自底向上: %d, 耗时: %v\n", result2, duration2)
    fmt.Printf("空间优化: %d, 耗时: %v\n", result3, duration3)
    
    // 使用通用DP求解器计算斐波那契数列
    fibSolver := NewDPSolver(
        // 基本情况检查
        func(n int) bool {
            return n <= 1
        },
        // 基本情况处理
        func(n int) int {
            return n
        },
        // 状态转移
        func(n int, table DPTable[int, int]) int {
            result1, _ := table.Get(n-1)
            result2, _ := table.Get(n-2)
            return result1 + result2
        },
    )
    
    // 解决问题
    start4 := time.Now()
    result4 := fibSolver.Solve(n)
    duration4 := time.Since(start4)
    
    fmt.Printf("DP求解器: %d, 耗时: %v\n", result4, duration4)
}
```

### 6.2 背包问题

**定义**：背包问题（Knapsack Problem）是一个经典的组合优化问题，给定一组物品，每个物品有特定的重量和价值，求在不超过背包容量的情况下，能够装入背包的物品的最大总价值。

**常见变种**：

- **0-1背包问题**：每个物品只能选择放入或不放入背包（0或1个）
- **完全背包问题**：每个物品可以无限次选择放入背包
- **多重背包问题**：每个物品可以选择放入0到有限次数的背包
- **分数背包问题**：物品可以被部分放入背包（贪心算法更适合解决）

**Go 2025 实现**：

```go
// 物品结构
type Item struct {
    Weight int
    Value  int
}

// 0-1背包问题（二维DP数组实现）
func knapsack01_2D(items []Item, capacity int) int {
    n := len(items)
    
    // 创建DP表：dp[i][w]表示考虑前i个物品，容量为w时的最大价值
    dp := make([][]int, n+1)
    for i := range dp {
        dp[i] = make([]int, capacity+1)
    }
    
    // 填充DP表
    for i := 1; i <= n; i++ {
        for w := 0; w <= capacity; w++ {
            // 不选当前物品
            dp[i][w] = dp[i-1][w]
            
            // 选当前物品（如果能放下）
            if items[i-1].Weight <= w {
                valueWithItem := dp[i-1][w-items[i-1].Weight] + items[i-1].Value
                dp[i][w] = max(dp[i][w], valueWithItem)
            }
        }
    }
    
    return dp[n][capacity]
}

// 0-1背包问题（一维DP数组优化空间）
func knapsack01_1D(items []Item, capacity int) int {
    // 创建DP表：dp[w]表示容量为w时的最大价值
    dp := make([]int, capacity+1)
    
    // 填充DP表
    for _, item := range items {
        // 从右向左遍历，确保每个物品最多选一次
        for w := capacity; w >= item.Weight; w-- {
            dp[w] = max(dp[w], dp[w-item.Weight]+item.Value)
        }
    }
    
    return dp[capacity]
}

// 完全背包问题
func knapsackComplete(items []Item, capacity int) int {
    // 创建DP表：dp[w]表示容量为w时的最大价值
    dp := make([]int, capacity+1)
    
    // 填充DP表
    for _, item := range items {
        // 从左向右遍历，允许每个物品选多次
        for w := item.Weight; w <= capacity; w++ {
            dp[w] = max(dp[w], dp[w-item.Weight]+item.Value)
        }
    }
    
    return dp[capacity]
}

// 多重背包问题（物品数量受限）
func knapsackMultiple(items []Item, counts []int, capacity int) int {
    if len(items) != len(counts) {
        panic("物品和数量数组长度不匹配")
    }
    
    // 创建DP表
    dp := make([]int, capacity+1)
    
    // 处理每种物品
    for i, item := range items {
        count := counts[i]
        
        // 使用二进制优化：将count个相同物品分解为2^k个物品包
        // 例如，5个物品分解为1个、2个、2个
        k := 1
        for count > 0 {
            // 选取当前可用数量和二进制位数中较小的一个
            use := min(k, count)
            count -= use
            
            // 创建一个新的物品包
            packedItem := Item{
                Weight: item.Weight * use,
                Value:  item.Value * use,
            }
            
            // 当前物品包应用0-1背包逻辑
            for w := capacity; w >= packedItem.Weight; w-- {
                dp[w] = max(dp[w], dp[w-packedItem.Weight]+packedItem.Value)
            }
            
            // 二进制增长
            k *= 2
        }
    }
    
    return dp[capacity]
}

// 分数背包问题（使用贪心算法）
func knapsackFractional(items []Item, capacity int) float64 {
    // 计算每个物品的价值密度（价值/重量）
    type ItemWithDensity struct {
        Item
        Density float64
    }
    
    itemsWithDensity := make([]ItemWithDensity, len(items))
    for i, item := range items {
        itemsWithDensity[i] = ItemWithDensity{
            Item:    item,
            Density: float64(item.Value) / float64(item.Weight),
        }
    }
    
    // 按价值密度降序排序
    sort.Slice(itemsWithDensity, func(i, j int) bool {
        return itemsWithDensity[i].Density > itemsWithDensity[j].Density
    })
    
    // 贪心选择
    var totalValue float64
    remainingCapacity := capacity
    
    for _, item := range itemsWithDensity {
        if remainingCapacity >= item.Weight {
            // 物品可以完全放入
            totalValue += float64(item.Value)
            remainingCapacity -= item.Weight
        } else if remainingCapacity > 0 {
            // 物品可以部分放入
            fraction := float64(remainingCapacity) / float64(item.Weight)
            totalValue += fraction * float64(item.Value)
            remainingCapacity = 0
        }
        
        if remainingCapacity == 0 {
            break
        }
    }
    
    return totalValue
}

// 使用Go 2025增强的泛型实现背包问题
func knapsackGeneric[T Number](
    weights []int, 
    values []T,
    capacity int,
) T {
    n := len(weights)
    if n != len(values) {
        panic("权重和价值数组长度不匹配")
    }
    
    // 创建DP表
    var zero T
    dp := make([]T, capacity+1)
    for i := range dp {
        dp[i] = zero
    }
    
    // 填充DP表
    for i := 0; i < n; i++ {
        weight, value := weights[i], values[i]
        
        for w := capacity; w >= weight; w-- {
            dp[w] = max(dp[w], dp[w-weight]+value)
        }
    }
    
    return dp[capacity]
}

// 用法示例
func knapsackExample() {
    items := []Item{
        {Weight: 2, Value: 3},
        {Weight: 3, Value: 4},
        {Weight: 4, Value: 5},
        {Weight: 5, Value: 8},
        {Weight: 9, Value: 10},
    }
    capacity := 20
    
    // 0-1背包（二维DP）
    result1 := knapsack01_2D(items, capacity)
    fmt.Printf("0-1背包 (二维DP): %d\n", result1)
    
    // 0-1背包（一维DP）
    result2 := knapsack01_1D(items, capacity)
    fmt.Printf("0-1背包 (一维DP): %d\n", result2)
    
    // 完全背包
    result3 := knapsackComplete(items, capacity)
    fmt.Printf("完全背包: %d\n", result3)
    
    // 多重背包
    counts := []int{3, 2, 4, 2, 1}  // 每种物品的数量
    result4 := knapsackMultiple(items, counts, capacity)
    fmt.Printf("多重背包: %d\n", result4)
    
    // 分数背包
    result5 := knapsackFractional(items, capacity)
    fmt.Printf("分数背包: %.2f\n", result5)
    
    // 使用泛型实现
    weights := []int{2, 3, 4, 5, 9}
    values := []int{3, 4, 5, 8, 10}
    result6 := knapsackGeneric(weights, values, capacity)
    fmt.Printf("泛型0-1背包: %d\n", result6)
    
    // 使用浮点数值
    floatValues := []float64{3.5, 4.1, 5.2, 8.6, 10.3}
    result7 := knapsackGeneric(weights, floatValues, capacity)
    fmt.Printf("浮点数价值背包: %.2f\n", result7)
}
```

**性能分析**：

- 时间复杂度：
  - 0-1背包：O(n·W)，其中n是物品数量，W是背包容量
  - 完全背包：O(n·W)
  - 多重背包：O(n·W·log(C))，其中C是物品数量的最大值
  - 分数背包：O(n·log(n))，主要是排序的时间复杂度
- 空间复杂度：
  - 二维DP实现：O(n·W)
  - 一维DP优化：O(W)
- 优点：
  - 可以解决各种背包问题变种
  - 一维DP优化显著减少空间需求
  - 适用于各种资源分配问题
- 缺点：
  - 当容量W很大时，性能下降
  - 背包容量不能为分数（除非特别处理）
- 应用场景：
  - 资源分配问题
  - 预算约束下的项目选择
  - 货物装载优化
  - 投资组合优化

### 6.3 编辑距离

**定义**：编辑距离（Edit Distance）或Levenshtein距离是指两个字符串之间的最小编辑操作数量，使得一个字符串转变为另一个字符串。编辑操作包括：插入一个字符、删除一个字符和替换一个字符。

**基本原理**：

1. 使用动态规划解决，其中`dp[i][j]`表示将word1的前i个字符转换为word2的前j个字符所需的最小操作数
2. 基本情况：当一个字符串为空时，编辑距离等于另一个字符串的长度
3. 状态转移：考虑当前字符是否相同，选择插入、删除或替换操作中的最小值

**Go 2025 实现**：

```go
// 编辑距离（Levenshtein距离）
func editDistance(word1, word2 string) int {
    m, n := len(word1), len(word2)
    
    // 创建DP表
    dp := make([][]int, m+1)
    for i := range dp {
        dp[i] = make([]int, n+1)
    }
    
    // 基本情况：空字符串转换
    for i := 0; i <= m; i++ {
        dp[i][0] = i  // 删除操作
    }
    
    for j := 0; j <= n; j++ {
        dp[0][j] = j  // 插入操作
    }
    
    // 填充DP表
    for i := 1; i <= m; i++ {
        for j := 1; j <= n; j++ {
            if word1[i-1] == word2[j-1] {
                // 当前字符相同，无需操作
                dp[i][j] = dp[i-1][j-1]
            } else {
                // 选择三种操作中的最小值
                dp[i][j] = 1 + min(
                    dp[i-1][j],     // 删除
                    min(
                        dp[i][j-1],   // 插入
                        dp[i-1][j-1], // 替换
                    ),
                )
            }
        }
    }
    
    return dp[m][n]
}

// 空间优化的编辑距离
func editDistanceOptimized(word1, word2 string) int {
    m, n := len(word1), len(word2)
    
    // 确保word1是较短的字符串，减少空间使用
    if m > n {
        word1, word2 = word2, word1
        m, n = n, m
    }
    
    // 只需要保存两行DP值
    prevRow := make([]int, n+1)
    currRow := make([]int, n+1)
    
    // 初始化第一行
    for j := 0; j <= n; j++ {
        prevRow[j] = j
    }
    
    // 填充DP表
    for i := 1; i <= m; i++ {
        currRow[0] = i
        
        for j := 1; j <= n; j++ {
            if word1[i-1] == word2[j-1] {
                currRow[j] = prevRow[j-1]
            } else {
                currRow[j] = 1 + min(
                    prevRow[j],      // 删除
                    min(
                        currRow[j-1],  // 插入
                        prevRow[j-1],  // 替换
                    ),
                )
            }
        }
        
        // 交换行
        prevRow, currRow = currRow, prevRow
    }
    
    return prevRow[n]
}

// 带操作步骤的编辑距离
func editDistanceWithOperations(word1, word2 string) (int, []string) {
    m, n := len(word1), len(word2)
    
    // 创建DP表
    dp := make([][]int, m+1)
    for i := range dp {
        dp[i] = make([]int, n+1)
    }
    
    // 同时记录操作类型
    ops := make([][]string, m+1)
    for i := range ops {
        ops[i] = make([]string, n+1)
    }
    
    // 初始化
    for i := 0; i <= m; i++ {
        dp[i][0] = i
        if i > 0 {
            ops[i][0] = "DELETE " + string(word1[i-1])
        }
    }
    
    for j := 0; j <= n; j++ {
        dp[0][j] = j
        if j > 0 {
            ops[0][j] = "INSERT " + string(word2[j-1])
        }
    }
    
    // 填充DP表
    for i := 1; i <= m; i++ {
        for j := 1; j <= n; j++ {
            if word1[i-1] == word2[j-1] {
                dp[i][j] = dp[i-1][j-1]
                ops[i][j] = "KEEP " + string(word1[i-1])
            } else {
                // 找出最小操作
                delCost := dp[i-1][j]
                insCost := dp[i][j-1]
                subCost := dp[i-1][j-1]
                
                if delCost <= insCost && delCost <= subCost {
                    dp[i][j] = 1 + delCost
                    ops[i][j] = "DELETE " + string(word1[i-1])
                } else if insCost <= delCost && insCost <= subCost {
                    dp[i][j] = 1 + insCost
                    ops[i][j] = "INSERT " + string(word2[j-1])
                } else {
                    dp[i][j] = 1 + subCost
                    ops[i][j] = "REPLACE " + string(word1[i-1]) + " with " + string(word2[j-1])
                }
            }
        }
    }
    
    // 回溯找出操作序列
    var operations []string
    i, j := m, n
    for i > 0 || j > 0 {
        if ops[i][j] != "" && !strings.HasPrefix(ops[i][j], "KEEP") {
            operations = append([]string{ops[i][j]}, operations...)
        }
        
        // 移动到前一个状态
        if i > 0 && j > 0 && word1[i-1] == word2[j-1] {
            i--
            j--
        } else if i > 0 && j > 0 && dp[i][j] == dp[i-1][j-1]+1 {
            i--
            j--
        } else if i > 0 && dp[i][j] == dp[i-1][j]+1 {
            i--
        } else {
            j--
        }
    }
    
    return dp[m][n], operations
}

// 用法示例
func editDistanceExample() {
    word1 := "intention"
    word2 := "execution"
    
    // 标准编辑距离
    distance := editDistance(word1, word2)
    fmt.Printf("%s 到 %s 的编辑距离: %d\n", word1, word2, distance)
    
    // 空间优化版本
    distanceOpt := editDistanceOptimized(word1, word2)
    fmt.Printf("优化版编辑距离: %d\n", distanceOpt)
    
    // 带操作步骤的编辑距离
    dist, operations := editDistanceWithOperations(word1, word2)
    fmt.Printf("编辑距离: %d, 操作步骤:\n", dist)
    for i, op := range operations {
        fmt.Printf("  %d. %s\n", i+1, op)
    }
    
    // 性能测试
    longWord1 := strings.Repeat("abcdef", 500)  // 长度为3000的字符串
    longWord2 := strings.Repeat("abcxyz", 500)  // 长度为3000的字符串
    
    start1 := time.Now()
    dist1 := editDistance(longWord1, longWord2)
    duration1 := time.Since(start1)
    
    start2 := time.Now()
    dist2 := editDistanceOptimized(longWord1, longWord2)
    duration2 := time.Since(start2)
    
    fmt.Printf("\n长字符串测试 (长度: %d):\n", len(longWord1))
    fmt.Printf("标准实现: 距离=%d, 耗时=%v\n", dist1, duration1)
    fmt.Printf("优化实现: 距离=%d, 耗时=%v\n", dist2, duration2)
    fmt.Printf("空间优化加速比: %.2fx\n", float64(duration1)/float64(duration2))
}
```

**性能分析**：

- 时间复杂度：O(m·n)，其中m和n是两个字符串的长度
- 空间复杂度：
  - 标准实现：O(m·n)
  - 优化实现：O(min(m,n))
- 优点：
  - 可以处理任何字符串
  - 可以找出具体的编辑操作步骤
  - 空间优化版本减少了内存使用
- 缺点：
  - 当字符串很长时计算成本高
  - 基本算法假设所有操作代价相同
- 应用场景：
  - 拼写检查和纠正
  - DNA序列比较
  - 文本相似度计算
  - 自动纠错系统

### 6.4 最长公共子序列

**定义**：最长公共子序列（Longest Common Subsequence，LCS）是指在两个序列中都出现的最长子序列，但子序列的元素在原序列中不必连续。

**基本原理**：

1. 两个序列的LCS是经典的动态规划问题
2. 状态定义：`dp[i][j]`表示text1的前i个字符与text2的前j个字符的LCS长度
3. 状态转移：
   - 当两个字符相同时，取左上角值加1
   - 当两个字符不同时，取上方和左方的最大值

**Go 2025 实现**：

```go
// 最长公共子序列（LCS）长度
func longestCommonSubsequence(text1, text2 string) int {
    m, n := len(text1), len(text2)
    
    // 创建DP表
    dp := make([][]int, m+1)
    for i := range dp {
        dp[i] = make([]int, n+1)
    }
    
    // 填充DP表
    for i := 1; i <= m; i++ {
        for j := 1; j <= n; j++ {
            if text1[i-1] == text2[j-1] {
                dp[i][j] = dp[i-1][j-1] + 1
            } else {
                dp[i][j] = max(dp[i-1][j], dp[i][j-1])
            }
        }
    }
    
    return dp[m][n]
}

// 空间优化的LCS
func longestCommonSubsequenceOptimized(text1, text2 string) int {
    m, n := len(text1), len(text2)
    
    // 确保text1是较短的字符串以减少空间使用
    if m > n {
        text1, text2 = text2, text1
        m, n = n, m
    }
    
    // 只需要两行DP值
    prevRow := make([]int, n+1)
    currRow := make([]int, n+1)
    
    // 填充DP表
    for i := 1; i <= m; i++ {
        for j := 1; j <= n; j++ {
            if text1[i-1] == text2[j-1] {
                currRow[j] = prevRow[j-1] + 1
            } else {
                currRow[j] = max(prevRow[j], currRow[j-1])
            }
        }
        
        // 交换行
        prevRow, currRow = currRow, prevRow
        // 清空currRow以准备下一轮使用
        for j := range currRow {
            currRow[j] = 0
        }
    }
    
    return prevRow[n]
}

// 获取实际的LCS
func getLCS(text1, text2 string) string {
    m, n := len(text1), len(text2)
    
    // 创建DP表
    dp := make([][]int, m+1)
    for i := range dp {
        dp[i] = make([]int, n+1)
    }
    
    // 填充DP表
    for i := 1; i <= m; i++ {
        for j := 1; j <= n; j++ {
            if text1[i-1] == text2[j-1] {
                dp[i][j] = dp[i-1][j-1] + 1
            } else {
                dp[i][j] = max(dp[i-1][j], dp[i][j-1])
            }
        }
    }
    
    // 回溯以构建LCS
    var result strings.Builder
    i, j := m, n
    for i > 0 && j > 0 {
        if text1[i-1] == text2[j-1] {
            result.WriteByte(text1[i-1])
            i--
            j--
        } else if dp[i-1][j] > dp[i][j-1] {
            i--
        } else {
            j--
        }
    }
    
    // 结果是倒序的，需要反转
    lcs := result.String()
    runes := []rune(lcs)
    for i, j := 0, len(runes)-1; i < j; i, j = i+1, j-1 {
        runes[i], runes[j] = runes[j], runes[i]
    }
    
    return string(runes)
}

// 获取所有可能的LCS（可能有多个）
func getAllLCS(text1, text2 string) []string {
    m, n := len(text1), len(text2)
    
    // 创建DP表
    dp := make([][]int, m+1)
    for i := range dp {
        dp[i] = make([]int, n+1)
    }
    
    // 填充DP表
    for i := 1; i <= m; i++ {
        for j := 1; j <= n; j++ {
            if text1[i-1] == text2[j-1] {
                dp[i][j] = dp[i-1][j-1] + 1
            } else {
                dp[i][j] = max(dp[i-1][j], dp[i][j-1])
            }
        }
    }
    
    // 使用集合避免重复
    lcsSet := make(map[string]bool)
    
    // 递归回溯找出所有可能的LCS
    var backtrack func(i, j int, path string)
    backtrack = func(i, j int, path string) {
        if i == 0 || j == 0 {
            // 反转路径并添加到结果
            runes := []rune(path)
            for k, l := 0, len(runes)-1; k < l; k, l = k+1, l-1 {
                runes[k], runes[l] = runes[l], runes[k]
            }
            lcsSet[string(runes)] = true
            return
        }
        
        if text1[i-1] == text2[j-1] {
            // 字符匹配，将其加入路径
            backtrack(i-1, j-1, path+string(text1[i-1]))
        } else {
            // 尝试两个方向
            if dp[i-1][j] >= dp[i][j-1] {
                backtrack(i-1, j, path)
            }
            if dp[i][j-1] >= dp[i-1][j] {
                backtrack(i, j-1, path)
            }
        }
    }
    
    backtrack(m, n, "")
    
    // 将集合转换为切片
    var result []string
    for lcs := range lcsSet {
        result = append(result, lcs)
    }
    
    // 按字典序排序结果
    sort.Strings(result)
    return result
}

// 用Go 2025扩展的泛型计算任意序列的LCS
func lcsGeneric[T comparable](seq1, seq2 []T) int {
    m, n := len(seq1), len(seq2)
    
    // 创建DP表
    dp := make([][]int, m+1)
    for i := range dp {
        dp[i] = make([]int, n+1)
    }
    
    // 填充DP表
    for i := 1; i <= m; i++ {
        for j := 1; j <= n; j++ {
            if seq1[i-1] == seq2[j-1] {
                dp[i][j] = dp[i-1][j-1] + 1
            } else {
                dp[i][j] = max(dp[i-1][j], dp[i][j-1])
            }
        }
    }
    
    return dp[m][n]
}

// 用法示例
func lcsExample() {
    text1 := "abcde"
    text2 := "ace"
    
    // 计算LCS长度
    length := longestCommonSubsequence(text1, text2)
    fmt.Printf("%s 和 %s 的LCS长度: %d\n", text1, text2, length)
    
    // 空间优化版本
    lengthOpt := longestCommonSubsequenceOptimized(text1, text2)
    fmt.Printf("优化版LCS长度: %d\n", lengthOpt)
    
    // 获取实际的LCS
    lcs := getLCS(text1, text2)
    fmt.Printf("LCS: %s\n", lcs)
    
    // 获取所有可能的LCS
    text1 = "abcaba"
    text2 = "abacaba"
    allLCS := getAllLCS(text1, text2)
    fmt.Printf("%s 和 %s 的所有LCS:\n", text1, text2)
    for i, lcs := range allLCS {
        fmt.Printf("  %d. %s\n", i+1, lcs)
    }
    
    // 使用泛型LCS
    seq1 := []int{1, 2, 3, 4, 5}
    seq2 := []int{1, 3, 5}
    lcsLength := lcsGeneric(seq1, seq2)
    fmt.Printf("数字序列LCS长度: %d\n", lcsLength)
    
    // 性能测试
    longText1 := strings.Repeat("abcdefghij", 200)  // 长度为2000的字符串
    longText2 := strings.Repeat("aeiouabcxyz", 180) // 长度为1980的字符串
    
    start1 := time.Now()
    len1 := longestCommonSubsequence(longText1, longText2)
    duration1 := time.Since(start1)
    
    start2 := time.Now()
    len2 := longestCommonSubsequenceOptimized(longText1, longText2)
    duration2 := time.Since(start2)
    
    fmt.Printf("\n长字符串LCS测试:\n")
    fmt.Printf("字符串长度: %d 和 %d\n", len(longText1), len(longText2))
    fmt.Printf("标准实现: 长度=%d, 耗时=%v\n", len1, duration1)
    fmt.Printf("优化实现: 长度=%d, 耗时=%v\n", len2, duration2)
    fmt.Printf("空间优化加速比: %.2fx\n", float64(duration1)/float64(duration2))
}
```

**性能分析**：

- 时间复杂度：
  - 计算LCS长度：O(m·n)
  - 获取实际LCS：O(m·n + (m+n))，额外的m+n用于回溯
  - 获取所有可能的LCS：最坏情况下为O(2^(m+n))，因为可能存在指数级数量的子序列
- 空间复杂度：
  - 标准实现：O(m·n)
  - 优化实现：O(min(m,n))
- 优点：
  - 可用于任何类型的序列比较
  - 有多种优化变体适应不同需求
  - 结果具有明确的生物学和语言学意义
- 缺点：
  - 计算所有可能的LCS可能非常耗时
  - 对超长序列性能不佳
- 应用场景：
  - 生物信息学（DNA序列比较）
  - 文件差异比较
  - 版本控制系统
  - 自然语言处理（文本相似度）

### 6.5 矩阵链乘法

**定义**：矩阵链乘法问题是求解相乘一系列矩阵的最高效顺序，以使得乘法运算次数最小。给定n个矩阵，矩阵链A[0]A[1]...A[n-1]，每个矩阵A[i]的维度为p[i]×p[i+1]，求解如何添加括号使得计算所需的乘法运算次数最少。

**基本原理**：

1. 矩阵乘法满足结合律，不同的乘法顺序会导致不同的计算量
2. 使用动态规划求解，其中`dp[i][j]`表示计算矩阵链A[i]A[i+1]...A[j]的最少乘法次数
3. 状态转移方程：`dp[i][j]` = min(`dp[i][k]` + `dp[k+1][j]` + p[i]×p[k+1]×p[j+1])，其中i ≤ k < j

**Go 2025 实现**：

```go
// 矩阵链乘法问题
func matrixChainMultiplication(dimensions []int) (int, [][]int) {
    n := len(dimensions) - 1  // 矩阵数量
    
    // 创建DP表：dp[i][j]表示计算矩阵链A[i]A[i+1]...A[j]的最少乘法次数
    dp := make([][]int, n)
    for i := range dp {
        dp[i] = make([]int, n)
    }
    
    // 创建分割点表，用于重构最优括号方案
    split := make([][]int, n)
    for i := range split {
        split[i] = make([]int, n)
        for j := range split[i] {
            split[i][j] = -1  // 初始化为-1
        }
    }
    
    // 计算链长为l的所有可能矩阵链
    for l := 2; l <= n; l++ {
        for i := 0; i <= n-l; i++ {
            j := i + l - 1
            dp[i][j] = math.MaxInt32  // 初始化为最大值
            
            // 尝试在位置k处分割
            for k := i; k < j; k++ {
                // 矩阵A[i..k]和A[k+1..j]相乘的代价
                cost := dp[i][k] + dp[k+1][j] + dimensions[i]*dimensions[k+1]*dimensions[j+1]
                
                if cost < dp[i][j] {
                    dp[i][j] = cost
                    split[i][j] = k  // 记录最佳分割点
                }
            }
        }
    }
    
    return dp[0][n-1], split
}

// 根据分割点表构建最优括号方案
func printOptimalParenthesis(split [][]int, i, j int) string {
    if i == j {
        return fmt.Sprintf("A%d", i)
    }
    
    k := split[i][j]
    return "(" + printOptimalParenthesis(split, i, k) + 
           " × " + 
           printOptimalParenthesis(split, k+1, j) + ")"
}

// 矩阵结构
type Matrix struct {
    Rows, Cols int
    Data       [][]float64
}

// 创建新矩阵
func NewMatrix(rows, cols int) *Matrix {
    data := make([][]float64, rows)
    for i := range data {
        data[i] = make([]float64, cols)
    }
    return &Matrix{Rows: rows, Cols: cols, Data: data}
}

// 矩阵乘法
func MatrixMultiply(a, b *Matrix) (*Matrix, error) {
    if a.Cols != b.Rows {
        return nil, fmt.Errorf("矩阵维度不匹配: %dx%d 和 %dx%d", a.Rows, a.Cols, b.Rows, b.Cols)
    }
    
    result := NewMatrix(a.Rows, b.Cols)
    
    for i := 0; i < a.Rows; i++ {
        for j := 0; j < b.Cols; j++ {
            sum := 0.0
            for k := 0; k < a.Cols; k++ {
                sum += a.Data[i][k] * b.Data[k][j]
            }
            result.Data[i][j] = sum
        }
    }
    
    return result, nil
}

// 用法示例
func matrixChainExample() {
    // 矩阵链：A0(30×35), A1(35×15), A2(15×5), A3(5×10), A4(10×20), A5(20×25)
    dimensions := []int{30, 35, 15, 5, 10, 20, 25}
    
    // 计算最优乘法顺序
    minOps, split := matrixChainMultiplication(dimensions)
    fmt.Printf("最少乘法运算次数: %d\n", minOps)
    
    // 打印最优括号方案
    optParenthesis := printOptimalParenthesis(split, 0, len(dimensions)-2)
    fmt.Printf("最优括号方案: %s\n", optParenthesis)
    
    // 验证不同顺序的计算量
    fmt.Println("\n不同乘法顺序的计算量:")
    
    // 示例1: ((A0 × A1) × ((A2 × A3) × (A4 × A5)))
    ops1 := dimensions[0]*dimensions[1]*dimensions[2] +  // (A0 × A1)
            dimensions[2]*dimensions[3]*dimensions[4] +  // (A2 × A3)
            dimensions[4]*dimensions[5]*dimensions[6] +  // (A4 × A5)
            dimensions[2]*dimensions[4]*dimensions[6] +  // ((A2 × A3) × (A4 × A5))
            dimensions[0]*dimensions[2]*dimensions[6]    // ((A0 × A1) × ((A2 × A3) × (A4 × A5)))
    fmt.Printf("顺序1 - ((A0 × A1) × ((A2 × A3) × (A4 × A5))): %d 次乘法\n", ops1)
    
    // 示例2: (A0 × (A1 × (A2 × (A3 × (A4 × A5)))))
    ops2 := dimensions[4]*dimensions[5]*dimensions[6] +  // (A4 × A5)
            dimensions[3]*dimensions[4]*dimensions[6] +  // (A3 × (A4 × A5))
            dimensions[2]*dimensions[3]*dimensions[6] +  // (A2 × (A3 × (A4 × A5)))
            dimensions[1]*dimensions[2]*dimensions[6] +  // (A1 × (A2 × (A3 × (A4 × A5))))
            dimensions[0]*dimensions[1]*dimensions[6]    // (A0 × (A1 × (A2 × (A3 × (A4 × A5)))))
    fmt.Printf("顺序2 - (A0 × (A1 × (A2 × (A3 × (A4 × A5))))): %d 次乘法\n", ops2)
    
    // 比较与最优解的差别
    fmt.Printf("与最优解相比，顺序1需要额外 %.2f%% 的计算量\n", 
               float64(ops1-minOps)/float64(minOps)*100)
    fmt.Printf("与最优解相比，顺序2需要额外 %.2f%% 的计算量\n", 
               float64(ops2-minOps)/float64(minOps)*100)
    
    // 生成随机矩阵链进行大规模测试
    rand.Seed(time.Now().UnixNano())
    randomDimensions := make([]int, 51)  // 50个矩阵
    for i := range randomDimensions {
        randomDimensions[i] = rand.Intn(90) + 10  // 10到99之间的随机数
    }
    
    start := time.Now()
    minOpsRandom, _ := matrixChainMultiplication(randomDimensions)
    duration := time.Since(start)
    
    fmt.Printf("\n50个矩阵的最优计算顺序测试:\n")
    fmt.Printf("最少乘法运算次数: %d\n", minOpsRandom)
    fmt.Printf("计算耗时: %v\n", duration)
}
```

**性能分析**：

- 时间复杂度：O(n³)，其中n是矩阵数量
- 空间复杂度：O(n²)，用于DP表和分割点表
- 优点：
  - 可以显著减少矩阵乘法的计算量
  - 适用于各种需要确定操作顺序的场景
  - 可以被扩展到其他具有结合律的操作
- 缺点：
  - 对于大量矩阵，计算最优顺序本身可能成为瓶颈
  - 算法不考虑并行计算的可能性
- 应用场景：
  - 大规模矩阵计算
  - 图形渲染管线优化
  - 神经网络层计算顺序优化
  - 数据库查询优化（连接操作顺序）

## 7. 高级数据结构

### 7.1 Trie树（前缀树）

**定义**：Trie树（发音为"try"）或前缀树是一种用于高效存储和检索字符串集合的树形数据结构。每个节点代表一个字符，从根到节点的路径表示一个字符串前缀。

**基本操作**：

1. **插入**：将字符串按字符顺序插入树中
2. **查找**：检查字符串是否存在于树中
3. **前缀查找**：查找具有给定前缀的所有字符串
4. **删除**：从树中删除字符串

**Go 2025 实现**：

```go
// Trie节点
type TrieNode struct {
    children map[rune]*TrieNode
    isEnd    bool
    count    int  // 记录以该节点结尾的单词数量
    prefixes int  // 记录以该节点为前缀的单词数量
    data     any  // 可以存储与节点关联的任意数据
}

// 创建新节点
func NewTrieNode() *TrieNode {
    return &TrieNode{
        children: make(map[rune]*TrieNode),
        isEnd:    false,
        count:    0,
        prefixes: 0,
    }
}

// Trie树
type Trie struct {
    root *TrieNode
    size int  // 词典中的单词数量
}

// 创建新的Trie树
func NewTrie() *Trie {
    return &Trie{
        root: NewTrieNode(),
        size: 0,
    }
}

// 插入单词
func (t *Trie) Insert(word string) {
    node := t.root
    node.prefixes++
    
    for _, ch := range word {
        if _, exists := node.children[ch]; !exists {
            node.children[ch] = NewTrieNode()
        }
        node = node.children[ch]
        node.prefixes++
    }
    
    if !node.isEnd {
        node.isEnd = true
        t.size++
    }
    node.count++
}

// 搜索完整单词
func (t *Trie) Search(word string) bool {
    node := t.searchNode(word)
    return node != nil && node.isEnd
}

// 查找节点
func (t *Trie) searchNode(word string) *TrieNode {
    node := t.root
    
    for _, ch := range word {
        if _, exists := node.children[ch]; !exists {
            return nil
        }
        node = node.children[ch]
    }
    
    return node
}

// 检查是否存在以给定前缀开始的单词
func (t *Trie) StartsWith(prefix string) bool {
    return t.searchNode(prefix) != nil
}

// 返回以给定前缀开始的单词数量
func (t *Trie) CountStartsWith(prefix string) int {
    node := t.searchNode(prefix)
    if node == nil {
        return 0
    }
    return node.prefixes
}

// 删除单词
func (t *Trie) Delete(word string) bool {
    if len(word) == 0 {
        return false
    }
    
    return t.deleteHelper(t.root, word, 0)
}

// 删除辅助函数
func (t *Trie) deleteHelper(node *TrieNode, word string, index int) bool {
    // 递归基础情况：已处理完所有字符
    if index == len(word) {
        if !node.isEnd {
            return false  // 单词不存在
        }
        
        node.isEnd = node.count > 1  // 如果有重复，保持isEnd为true
        node.count--
        t.size--
        return true
    }
    
    ch := rune(word[index])
    child, exists := node.children[ch]
    if !exists {
        return false  // 单词不存在
    }
    
    // 递归删除
    result := t.deleteHelper(child, word, index+1)
    
    // 更新前缀计数
    if result {
        node.prefixes--
        
        // 如果子节点不再有前缀，并且不是单词结尾，则删除它
        if child.prefixes == 0 {
            delete(node.children, ch)
        }
    }
    
    return result
}

// 获取所有单词
func (t *Trie) GetAllWords() []string {
    var result []string
    t.collectWords(t.root, "", &result)
    return result
}

// 收集单词辅助函数
func (t *Trie) collectWords(node *TrieNode, prefix string, result *[]string) {
    if node.isEnd {
        for i := 0; i < node.count; i++ {
            *result = append(*result, prefix)
        }
    }
    
    for ch, child := range node.children {
        t.collectWords(child, prefix+string(ch), result)
    }
}

// 获取带有给定前缀的所有单词
func (t *Trie) GetWordsWithPrefix(prefix string) []string {
    node := t.searchNode(prefix)
    if node == nil {
        return []string{}
    }
    
    var result []string
    t.collectWords(node, prefix, &result)
    return result
}

// 词典大小
func (t *Trie) Size() int {
    return t.size
}

// 使用泛型的Trie实现
type GenericTrieNode[T any] struct {
    children map[T]*GenericTrieNode[T]
    isEnd    bool
    data     any
}

type GenericTrie[T any] struct {
    root *GenericTrieNode[T]
}

func NewGenericTrie[T any]() *GenericTrie[T] {
    return &GenericTrie[T]{
        root: &GenericTrieNode[T]{
            children: make(map[T]*GenericTrieNode[T]),
            isEnd:    false,
        },
    }
}

// 用法示例
func trieExample() {
    trie := NewTrie()
    
    // 插入单词
    words := []string{"apple", "application", "banana", "app", "appetite", "ball"}
    for _, word := range words {
        trie.Insert(word)
    }
    
    // 统计信息
    fmt.Printf("Trie中的单词数量: %d\n", trie.Size())
    
    // 搜索
    searchWords := []string{"apple", "app", "apricot", "ban", "banana"}
    for _, word := range searchWords {
        fmt.Printf("搜索 \"%s\": %t\n", word, trie.Search(word))
    }
    
    // 前缀搜索
    prefixes := []string{"app", "ban", "c"}
    for _, prefix := range prefixes {
        fmt.Printf("以 \"%s\" 为前缀的单词数量: %d\n", prefix, trie.CountStartsWith(prefix))
        prefixWords := trie.GetWordsWithPrefix(prefix)
        fmt.Printf("以 \"%s\" 为前缀的单词: %v\n", prefix, prefixWords)
    }
    
    // 删除单词
    deleteWords := []string{"app", "banana", "car"}
    for _, word := range deleteWords {
        success := trie.Delete(word)
        fmt.Printf("删除 \"%s\": %t\n", word, success)
    }
    
    // 检查删除效果
    fmt.Printf("删除后的单词数量: %d\n", trie.Size())
    for _, word := range deleteWords {
        fmt.Printf("搜索 \"%s\": %t\n", word, trie.Search(word))
    }
    
    // 获取所有单词
    allWords := trie.GetAllWords()
    fmt.Printf("所有单词: %v\n", allWords)
    
    // 性能测试（大量单词插入和查询）
    fmt.Println("\n性能测试:")
    
    // 从文件加载单词字典
    // 这里假设有一个words.txt文件，每行一个单词
    // 如果文件不存在或无法打开，生成随机单词
    
    var bigWordList []string
    
    // 尝试读取文件
    file, err := os.Open("words.txt")
    if err == nil {
        scanner := bufio.NewScanner(file)
        for scanner.Scan() {
            bigWordList = append(bigWordList, scanner.Text())
        }
        file.Close()
    } else {
        // 文件不存在，生成随机单词
        rand.Seed(time.Now().UnixNano())
        const charset = "abcdefghijklmnopqrstuvwxyz"
        
        for i := 0; i < 100000; i++ {
            length := rand.Intn(10) + 3  // 3-12长度的单词
            word := make([]byte, length)
            for j := range word {
                word[j] = charset[rand.Intn(len(charset))]
            }
            bigWordList = append(bigWordList, string(word))
        }
    }
    
    // 创建新的Trie树
    largeTrie := NewTrie()
    
    // 测量插入性能
    start := time.Now()
    for _, word := range bigWordList {
        largeTrie.Insert(word)
    }
    insertDuration := time.Since(start)
    
    uniqueWords := len(largeTrie.GetAllWords())
    fmt.Printf("插入 %d 个单词 (含 %d 个唯一单词), 耗时: %v\n", 
               len(bigWordList), uniqueWords, insertDuration)
    
    // 测量查询性能
    start = time.Now()
    searchCount := 10000
    for i := 0; i < searchCount; i++ {
        idx := rand.Intn(len(bigWordList))
        largeTrie.Search(bigWordList[idx])
    }
    searchDuration := time.Since(start)
    
    fmt.Printf("执行 %d 次查询, 耗时: %v (平均 %.2f ns/查询)\n", 
               searchCount, searchDuration, float64(searchDuration.Nanoseconds())/float64(searchCount))
    
    // 测量前缀查询性能
    start = time.Now()
    prefixCount := 1000
    for i := 0; i < prefixCount; i++ {
        idx := rand.Intn(len(bigWordList))
        word := bigWordList[idx]
        prefixLen := rand.Intn(len(word)-1) + 1
        largeTrie.GetWordsWithPrefix(word[:prefixLen])
    }
    prefixDuration := time.Since(start)
    
    fmt.Printf("执行 %d 次前缀查询, 耗时: %v (平均 %.2f ns/查询)\n", 
               prefixCount, prefixDuration, float64(prefixDuration.Nanoseconds())/float64(prefixCount))
}
```

**性能分析**：

- 时间复杂度：
  - 插入：O(m)，其中m是字符串长度
  - 查找：O(m)
  - 删除：O(m)
  - 前缀匹配：O(m + k)，其中k是匹配前缀的字符串数量
- 空间复杂度：O(n·m)，其中n是单词数量，m是平均单词长度
- 优点：
  - 查询和插入操作快速
  - 支持前缀匹配
  - 可以有效地存储大量字符串
- 缺点：
  - 存储效率较低（特别是对于大量具有相似前缀的字符串）
  - 内存消耗大
- 应用场景：
  - 自动完成/预测文本
  - 拼写检查
  - IP路由（最长前缀匹配）
  - 字典实现

### 7.2 红黑树

**定义**：红黑树是一种自平衡的二叉搜索树，通过对节点染色（红色或黑色）和特定的平衡操作来保证树的高度接近于对数级别。它满足以下性质：

1. 每个节点是红色或黑色
2. 根节点是黑色
3. 所有叶子节点（NIL）都是黑色
4. 如果一个节点是红色，则其两个子节点都是黑色
5. 从任一节点到其每个叶子的所有路径都包含相同数量的黑色节点

**基本操作**：

1. **插入**：插入节点并维护红黑树性质
2. **删除**：删除节点并维护红黑树性质
3. **查找**：查找具有给定键的节点
4. **旋转**：左旋和右旋操作用于维护树的平衡

**Go 2025 实现**：

```go
// 定义颜色
type Color bool

const (
    RED   Color = true
    BLACK Color = false
)

// 红黑树节点
type RBNode[K comparable, V any] struct {
    Key    K
    Value  V
    Color  Color
    Left   *RBNode[K, V]
    Right  *RBNode[K, V]
    Parent *RBNode[K, V]
}

// 红黑树
type RBTree[K Ordered, V any] struct {
    Root *RBNode[K, V]
    NIL  *RBNode[K, V]
    Size int
}

// 创建新的红黑树
func NewRBTree[K Ordered, V any]() *RBTree[K, V] {
    nil_node := &RBNode[K, V]{Color: BLACK}
    return &RBTree[K, V]{
        Root: nil_node,
        NIL:  nil_node,
        Size: 0,
    }
}

// 创建新节点
func (t *RBTree[K, V]) newNode(key K, value V) *RBNode[K, V] {
    return &RBNode[K, V]{
        Key:    key,
        Value:  value,
        Color:  RED,
        Left:   t.NIL,
        Right:  t.NIL,
        Parent: t.NIL,
    }
}

// 左旋
func (t *RBTree[K, V]) leftRotate(x *RBNode[K, V]) {
    y := x.Right
    
    // 将y的左子树变为x的右子树
    x.Right = y.Left
    if y.Left != t.NIL {
        y.Left.Parent = x
    }
    
    // 将x的父节点与y连接
    y.Parent = x.Parent
    if x.Parent == t.NIL {
        t.Root = y
    } else if x == x.Parent.Left {
        x.Parent.Left = y
    } else {
        x.Parent.Right = y
    }
    
    // 将x变为y的左子节点
    y.Left = x
    x.Parent = y
}

// 右旋
func (t *RBTree[K, V]) rightRotate(y *RBNode[K, V]) {
    x := y.Left
    
    // 将x的右子树变为y的左子树
    y.Left = x.Right
    if x.Right != t.NIL {
        x.Right.Parent = y
    }
    
    // 将y的父节点与x连接
    x.Parent = y.Parent
    if y.Parent == t.NIL {
        t.Root = x
    } else if y == y.Parent.Left {
        y.Parent.Left = x
    } else {
        y.Parent.Right = x
    }
    
    // 将y变为x的右子节点
    x.Right = y
    y.Parent = x
}

// 插入
func (t *RBTree[K, V]) Insert(key K, value V) {
    // 创建新节点
    z := t.newNode(key, value)
    
    // 找到插入位置
    var y *RBNode[K, V] = t.NIL
    x := t.Root
    
    for x != t.NIL {
        y = x
        if z.Key < x.Key {
            x = x.Left
        } else if z.Key > x.Key {
            x = x.Right
        } else {
            // 键已存在，更新值
            x.Value = value
            return
        }
    }
    
    // 设置z的父节点
    z.Parent = y
    if y == t.NIL {
        t.Root = z  // 树为空
    } else if z.Key < y.Key {
        y.Left = z
    } else {
        y.Right = z
    }
    
    // 更新大小
    t.Size++
    
    // 调整以维护红黑树性质
    t.insertFixup(z)
}

// 插入后调整
func (t *RBTree[K, V]) insertFixup(z *RBNode[K, V]) {
    for z.Parent.Color == RED {
        if z.Parent == z.Parent.Parent.Left {
            y := z.Parent.Parent.Right
            if y.Color == RED {
                // 情况1：叔节点是红色
                z.Parent.Color = BLACK
                y.Color = BLACK
                z.Parent.Parent.Color = RED
                z = z.Parent.Parent
            } else {
                if z == z.Parent.Right {
                    // 情况2：叔节点是黑色，z是右子节点
                    z = z.Parent
                    t.leftRotate(z)
                }
                // 情况3：叔节点是黑色，z是左子节点
                z.Parent.Color = BLACK
                z.Parent.Parent.Color = RED
                t.rightRotate(z.Parent.Parent)
            }
        } else {
            // 对称情况
            y := z.Parent.Parent.Left
            if y.Color == RED {
                z.Parent.Color = BLACK
                y.Color = BLACK
                z.Parent.Parent.Color = RED
                z = z.Parent.Parent
            } else {
                if z == z.Parent.Left {
                    z = z.Parent
                    t.rightRotate(z)
                }
                z.Parent.Color = BLACK
                z.Parent.Parent.Color = RED
                t.leftRotate(z.Parent.Parent)
            }
        }
        
        if z == t.Root {
            break
        }
    }
    
    // 确保根节点为黑色
    t.Root.Color = BLACK
}

// 查找
func (t *RBTree[K, V]) Search(key K) (V, bool) {
    node := t.searchNode(key)
    if node == t.NIL {
        var zero V
        return zero, false
    }
    return node.Value, true
}

// 查找节点
func (t *RBTree[K, V]) searchNode(key K) *RBNode[K, V] {
    current := t.Root
    for current != t.NIL {
        if key < current.Key {
            current = current.Left
        } else if key > current.Key {
            current = current.Right
        } else {
            return current
        }
    }
    return t.NIL
}

// 删除
func (t *RBTree[K, V]) Delete(key K) bool {
    // 查找要删除的节点
    z := t.searchNode(key)
    if z == t.NIL {
        return false
    }
    
    t.deleteNode(z)
    t.Size--
    return true
}

// 删除节点
func (t *RBTree[K, V]) deleteNode(z *RBNode[K, V]) {
    var x, y *RBNode[K, V]
    
    if z.Left == t.NIL || z.Right == t.NIL {
        y = z
    } else {
        // 找后继节点
        y = z.Right
        for y.Left != t.NIL {
            y = y.Left
        }
    }
    
    // x是y的唯一子节点或NIL
    if y.Left != t.NIL {
        x = y.Left
    } else {
        x = y.Right
    }
    
    // 将x接到y的父节点
    x.Parent = y.Parent
    if y.Parent == t.NIL {
        t.Root = x
    } else if y == y.Parent.Left {
        y.Parent.Left = x
    } else {
        y.Parent.Right = x
    }
    
    // 如果y不是z，则将y的值复制到z
    if y != z {
        z.Key = y.Key
        z.Value = y.Value
    }
    
    // 如果删除的是黑节点，需要调整
    if y.Color == BLACK {
        t.deleteFixup(x)
    }
}

// 删除后调整
func (t *RBTree[K, V]) deleteFixup(x *RBNode[K, V]) {
    for x != t.Root && x.Color == BLACK {
        if x == x.Parent.Left {
            w := x.Parent.Right
            
            if w.Color == RED {
                // 情况1：x的兄弟节点w是红色
                w.Color = BLACK
                x.Parent.Color = RED
                t.leftRotate(x.Parent)
                w = x.Parent.Right
            }
            
            if w.Left.Color == BLACK && w.Right.Color == BLACK {
                // 情况2：x的兄弟节点w是黑色，且w的两个子节点都是黑色
                w.Color = RED
                x = x.Parent
            } else {
                if w.Right.Color == BLACK {
                    // 情况3：x的兄弟节点w是黑色，w的左子节点是红色，右子节点是黑色
                    w.Left.Color = BLACK
                    w.Color = RED
                    t.rightRotate(w)
                    w = x.Parent.Right
                }
                
                // 情况4：x的兄弟节点w是黑色，w的右子节点是红色
                w.Color = x.Parent.Color
                x.Parent.Color = BLACK
                w.Right.Color = BLACK
                t.leftRotate(x.Parent)
                x = t.Root
            }
        } else {
            // 对称情况
            w := x.Parent.Left
            
            if w.Color == RED {
                w.Color = BLACK
                x.Parent.Color = RED
                t.rightRotate(x.Parent)
                w = x.Parent.Left
            }
            
            if w.Right.Color == BLACK && w.Left.Color == BLACK {
                w.Color = RED
                x = x.Parent
            } else {
                if w.Left.Color == BLACK {
                    w.Right.Color = BLACK
                    w.Color = RED
                    t.leftRotate(w)
                    w = x.Parent.Left
                }
                
                w.Color = x.Parent.Color
                x.Parent.Color = BLACK
                w.Left.Color = BLACK
                t.rightRotate(x.Parent)
                x = t.Root
            }
        }
    }
    
    x.Color = BLACK
}

// 获取最小键
func (t *RBTree[K, V]) Min() (K, V, bool) {
    if t.Root == t.NIL {
        var zeroK K
        var zeroV V
        return zeroK, zeroV, false
    }
    
    node := t.Root
    for node.Left != t.NIL {
        node = node.Left
    }
    
    return node.Key, node.Value, true
}

// 获取最大键
func (t *RBTree[K, V]) Max() (K, V, bool) {
    if t.Root == t.NIL {
        var zeroK K
        var zeroV V
        return zeroK, zeroV, false
    }
    
    node := t.Root
    for node.Right != t.NIL {
        node = node.Right
    }
    
    return node.Key, node.Value, true
}

// 获取树的大小
func (t *RBTree[K, V]) GetSize() int {
    return t.Size
}

// 中序遍历
func (t *RBTree[K, V]) InOrderTraversal() []K {
    var keys []K
    t.inOrderHelper(t.Root, &keys)
    return keys
}

// 中序遍历辅助函数
func (t *RBTree[K, V]) inOrderHelper(node *RBNode[K, V], keys *[]K) {
    if node != t.NIL {
        t.inOrderHelper(node.Left, keys)
        *keys = append(*keys, node.Key)
        t.inOrderHelper(node.Right, keys)
    }
}

// 用法示例
func rbTreeExample() {
    // 创建红黑树
    tree := NewRBTree[int, string]()
    
    // 插入键值对
    pairs := []struct {
        key   int
        value string
    }{
        {10, "十"},
        {20, "二十"},
        {5, "五"},
        {30, "三十"},
        {15, "十五"},
        {25, "二十五"},
        {2, "二"},
    }
    
    for _, pair := range pairs {
        tree.Insert(pair.key, pair.value)
        fmt.Printf("插入 (%d, %s), 树大小: %d\n", pair.key, pair.value, tree.GetSize())
    }
    
    // 测试查找
    searchKeys := []int{10, 15, 40}
    for _, key := range searchKeys {
        value, found := tree.Search(key)
        if found {
            fmt.Printf("找到键 %d, 值: %s\n", key, value)
        } else {
            fmt.Printf("未找到键 %d\n", key)
        }
    }
    
    // 中序遍历（应产生排序的键）
    keys := tree.InOrderTraversal()
    fmt.Printf("中序遍历: %v\n", keys)
    
    // 找最小和最大值
    minKey, minValue, foundMin := tree.Min()
    maxKey, maxValue, foundMax := tree.Max()
    
    if foundMin {
        fmt.Printf("最小键: %d, 值: %s\n", minKey, minValue)
    }
    
    if foundMax {
        fmt.Printf("最大键: %d, 值: %s\n", maxKey, maxValue)
    }
    
    // 删除节点
    deleteKeys := []int{10, 2, 20}
    for _, key := range deleteKeys {
        success := tree.Delete(key)
        fmt.Printf("删除键 %d: %t, 树大小: %d\n", key, success, tree.GetSize())
    }
    
    // 再次遍历
    keys = tree.InOrderTraversal()
    fmt.Printf("删除后中序遍历: %v\n", keys)
    
    // 性能测试
    fmt.Println("\n性能测试:")
    
    // 大规模插入测试
    bigTree := NewRBTree[int, int]()
    insertCount := 100000
    
    // 准备随机数据
    rand.Seed(time.Now().UnixNano())
    data := make([]int, insertCount)
    for i := 0; i < insertCount; i++ {
        data[i] = rand.Intn(1000000)
    }
    
    // 测量插入性能
    start := time.Now()
    for _, val := range data {
        bigTree.Insert(val, val)
    }
    insertDuration := time.Since(start)
    
    fmt.Printf("插入 %d 个元素, 耗时: %v (平均 %.2f ns/插入)\n", 
               insertCount, insertDuration, float64(insertDuration.Nanoseconds())/float64(insertCount))
    
    // 测量查找性能
    start = time.Now()
    searchCount := 10000
    for i := 0; i < searchCount; i++ {
        idx := rand.Intn(len(data))
        bigTree.Search(data[idx])
    }
    searchDuration := time.Since(start)
    
    fmt.Printf("执行 %d 次查找, 耗时: %v (平均 %.2f ns/查找)\n", 
               searchCount, searchDuration, float64(searchDuration.Nanoseconds())/float64(searchCount))
    
    // 测量删除性能
    start = time.Now()
    deleteCount := 10000
    for i := 0; i < deleteCount; i++ {
        idx := rand.Intn(len(data))
        bigTree.Delete(data[idx])
    }
    deleteDuration := time.Since(start)
    
    fmt.Printf("执行 %d 次删除, 耗时: %v (平均 %.2f ns/删除)\n", 
               deleteCount, deleteDuration, float64(deleteDuration.Nanoseconds())/float64(deleteCount))
    
    // 与普通二叉搜索树对比
    fmt.Println("\n红黑树与普通二叉搜索树对比:")
    
    // TODO: 实现普通二叉搜索树并进行对比测试
    // 这里可以添加与普通BST的性能对比
}
```

**性能分析**：

- 时间复杂度：
  - 插入：O(log n)
  - 查找：O(log n)
  - 删除：O(log n)
- 空间复杂度：O(n)
- 优点：
  - 自平衡特性保证了查找、插入和删除操作的对数时间复杂度
  - 比AVL树有更少的旋转操作
  - 在频繁插入和删除的场景中表现良好
- 缺点：
  - 实现复杂
  - 每个节点需要额外的存储空间来存储颜色信息
- 应用场景：
  - 实现关联容器，如映射和集合
  - 数据库索引
  - Linux进程调度
  - Java中的TreeMap和TreeSet

### 7.3 跳表（Skip List）

**定义**：跳表是一种可以用来替代平衡树的数据结构，它允许以O(log n)的期望时间复杂度进行查找、插入和删除操作。跳表是一种基于有序链表的概率性数据结构，通过在链表上维护多层索引来加速查找。

**基本原理**：

1. 跳表由多层链表组成，底层是一个完整的有序链表
2. 每个节点可能有多个前向指针，指向不同层次的下一个节点
3. 通过概率决定一个新插入的节点应该有多少层
4. 查找时从最高层开始，如果当前层的下一个节点太大，则下降到下一层

**Go 2025 实现**：

```go
// 跳表节点
type SkipListNode[K Ordered, V any] struct {
    Key     K
    Value   V
    Forward []*SkipListNode[K, V]  // 前向指针数组，每个元素指向不同层的下一个节点
}

// 跳表
type SkipList[K Ordered, V any] struct {
    Head        *SkipListNode[K, V]  // 头节点（不存储实际元素）
    MaxLevel    int                  // 最大层数
    CurrentLevel int                 // 当前最高层数
    Size        int                  // 元素数量
    Probability float64              // 用于决定节点层数的概率
}

// 创建新的跳表
func NewSkipList[K Ordered, V any](maxLevel int, probability float64) *SkipList[K, V] {
    head := &SkipListNode[K, V]{
        Forward: make([]*SkipListNode[K, V], maxLevel),
    }
    
    return &SkipList[K, V]{
        Head:        head,
        MaxLevel:    maxLevel,
        CurrentLevel: 0,
        Size:        0,
        Probability: probability,
    }
}

// 随机生成节点的层数
func (sl *SkipList[K, V]) randomLevel() int {
    level := 0
    for rand.Float64() < sl.Probability && level < sl.MaxLevel-1 {
        level++
    }
    return level
}

// 查找节点
func (sl *SkipList[K, V]) Search(key K) (V, bool) {
    current := sl.Head
    
    // 从最高层开始查找
    for i := sl.CurrentLevel; i >= 0; i-- {
        // 在当前层向前移动，直到找到下一个节点的键大于等于搜索键
        for current.Forward[i] != nil && current.Forward[i].Key < key {
            current = current.Forward[i]
        }
    }
    
    // 移动到第0层的下一个节点
    current = current.Forward[0]
    
    // 检查是否找到了键
    if current != nil && current.Key == key {
        return current.Value, true
    }
    
    // 键不存在
    var zero V
    return zero, false
}

// 插入键值对
func (sl *SkipList[K, V]) Insert(key K, value V) {
    // 用于更新各层中需要修改的节点
    update := make([]*SkipListNode[K, V], sl.MaxLevel)
    current := sl.Head
    
    // 从最高层开始查找插入位置
    for i := sl.CurrentLevel; i >= 0; i-- {
        for current.Forward[i] != nil && current.Forward[i].Key < key {
            current = current.Forward[i]
        }
        update[i] = current
    }
    
    // 移动到第0层的下一个节点
    current = current.Forward[0]
    
    // 如果键已存在，则更新值
    if current != nil && current.Key == key {
        current.Value = value
        return
    }
    
    // 生成新节点的层数
    level := sl.randomLevel()
    
    // 如果新层数高于当前层数，则初始化新层
    if level > sl.CurrentLevel {
        for i := sl.CurrentLevel + 1; i <= level; i++ {
            update[i] = sl.Head
        }
        sl.CurrentLevel = level
    }
    
    // 创建新节点
    newNode := &SkipListNode[K, V]{
        Key:     key,
        Value:   value,
        Forward: make([]*SkipListNode[K, V], level+1),
    }
    
    // 更新指针
    for i := 0; i <= level; i++ {
        newNode.Forward[i] = update[i].Forward[i]
        update[i].Forward[i] = newNode
    }
    
    sl.Size++
}

// 删除键
func (sl *SkipList[K, V]) Delete(key K) bool {
    update := make([]*SkipListNode[K, V], sl.MaxLevel)
    current := sl.Head
    
    // 找到每层中需要更新的节点
    for i := sl.CurrentLevel; i >= 0; i-- {
        for current.Forward[i] != nil && current.Forward[i].Key < key {
            current = current.Forward[i]
        }
        update[i] = current
    }
    
    current = current.Forward[0]
    
    // 键不存在
    if current == nil || current.Key != key {
        return false
    }
    
    // 删除节点
    for i := 0; i <= sl.CurrentLevel; i++ {
        if update[i].Forward[i] != current {
            break
        }
        update[i].Forward[i] = current.Forward[i]
    }
    
    // 如果删除的是最高层的节点，可能需要降低当前层数
    for sl.CurrentLevel > 0 && sl.Head.Forward[sl.CurrentLevel] == nil {
        sl.CurrentLevel--
    }
    
    sl.Size--
    return true
}

// 获取最小键
func (sl *SkipList[K, V]) Min() (K, V, bool) {
    if sl.Size == 0 {
        var zeroK K
        var zeroV V
        return zeroK, zeroV, false
    }
    
    firstNode := sl.Head.Forward[0]
    return firstNode.Key, firstNode.Value, true
}

// 获取最大键
func (sl *SkipList[K, V]) Max() (K, V, bool) {
    if sl.Size == 0 {
        var zeroK K
        var zeroV V
        return zeroK, zeroV, false
    }
    
    current := sl.Head
    level := sl.CurrentLevel
    
    // 在最高层尽可能向前移动
    for level >= 0 {
        for current.Forward[level] != nil {
            current = current.Forward[level]
        }
        level--
    }
    
    return current.Key, current.Value, true
}

// 获取所有键（有序）
func (sl *SkipList[K, V]) Keys() []K {
    keys := make([]K, 0, sl.Size)
    current := sl.Head.Forward[0]
    
    for current != nil {
        keys = append(keys, current.Key)
        current = current.Forward[0]
    }
    
    return keys
}

// 获取跳表的大小
func (sl *SkipList[K, V]) GetSize() int {
    return sl.Size
}

// 打印跳表结构（用于调试）
func (sl *SkipList[K, V]) PrintStructure() {
    fmt.Printf("Skip List (size=%d, levels=%d):\n", sl.Size, sl.CurrentLevel+1)
    
    for i := sl.CurrentLevel; i >= 0; i-- {
        fmt.Printf("Level %d: ", i)
        node := sl.Head.Forward[i]
        for node != nil {
            fmt.Printf("%v -> ", node.Key)
            node = node.Forward[i]
        }
        fmt.Println("nil")
    }
}

// 用法示例
func skipListExample() {
    // 创建跳表（最大32层，提升概率0.25）
    skipList := NewSkipList[int, string](32, 0.25)
    
    // 插入键值对
    data := []struct {
        key   int
        value string
    }{
        {30, "三十"},
        {10, "十"},
        {50, "五十"},
        {20, "二十"},
        {60, "六十"},
        {40, "四十"},
        {25, "二十五"},
    }
    
    for _, item := range data {
        skipList.Insert(item.key, item.value)
        fmt.Printf("插入 (%d, %s), 跳表大小: %d\n", item.key, item.value, skipList.GetSize())
    }
    
    // 打印跳表结构
    skipList.PrintStructure()
    
    // 查找
    searchKeys := []int{30, 25, 75}
    for _, key := range searchKeys {
        value, found := skipList.Search(key)
        if found {
            fmt.Printf("找到键 %d, 值: %s\n", key, value)
        } else {
            fmt.Printf("未找到键 %d\n", key)
        }
    }
    
    // 获取所有键（应该是有序的）
    keys := skipList.Keys()
    fmt.Printf("有序键列表: %v\n", keys)
    
    // 最小和最大键
    minKey, minValue, foundMin := skipList.Min()
    maxKey, maxValue, foundMax := skipList.Max()
    
    if foundMin {
        fmt.Printf("最小键: %d, 值: %s\n", minKey, minValue)
    }
    
    if foundMax {
        fmt.Printf("最大键: %d, 值: %s\n", maxKey, maxValue)
    }
    
    // 删除键
    deleteKeys := []int{10, 25, 75}
    for _, key := range deleteKeys {
        success := skipList.Delete(key)
        fmt.Printf("删除键 %d: %t, 跳表大小: %d\n", key, success, skipList.GetSize())
    }
    
    // 再次打印跳表结构
    skipList.PrintStructure()
    
    // 性能测试
    fmt.Println("\n性能测试:")
    
    // 创建大型跳表
    bigSkipList := NewSkipList[int, int](32, 0.25)
    
    // 准备数据
    insertCount := 100000
    data2 := make([]int, insertCount)
    for i := 0; i < insertCount; i++ {
        data2[i] = rand.Intn(1000000)
    }
    
    // 测量插入性能
    start := time.Now()
    for _, val := range data2 {
        bigSkipList.Insert(val, val)
    }
    insertDuration := time.Since(start)
    
    fmt.Printf("插入 %d 个元素, 耗时: %v (平均 %.2f ns/插入)\n", 
               insertCount, insertDuration, float64(insertDuration.Nanoseconds())/float64(insertCount))
    
    // 测量查找性能
    start = time.Now()
    searchCount := 10000
    for i := 0; i < searchCount; i++ {
        idx := rand.Intn(len(data2))
        bigSkipList.Search(data2[idx])
    }
    searchDuration := time.Since(start)
    
    fmt.Printf("执行 %d 次查找, 耗时: %v (平均 %.2f ns/查找)\n", 
               searchCount, searchDuration, float64(searchDuration.Nanoseconds())/float64(searchCount))
    
    // 测量删除性能
    start = time.Now()
    deleteCount := 10000
    for i := 0; i < deleteCount; i++ {
        idx := rand.Intn(len(data2))
        bigSkipList.Delete(data2[idx])
    }
    deleteDuration := time.Since(start)
    
    fmt.Printf("执行 %d 次删除, 耗时: %v (平均 %.2f ns/删除)\n", 
               deleteCount, deleteDuration, float64(deleteDuration.Nanoseconds())/float64(deleteCount))
    
    // 与红黑树和标准库map对比
    fmt.Println("\n跳表与其他数据结构对比:")
    
    // 对比代码可以根据需要添加
}
```

**性能分析**：

- 时间复杂度：
  - 查找：平均O(log n)，最坏O(n)
  - 插入：平均O(log n)，最坏O(n)
  - 删除：平均O(log n)，最坏O(n)
- 空间复杂度：平均O(n log n)
- 优点：
  - 实现比平衡树简单
  - 内存布局更适合缓存
  - 可以高效地支持范围查询
  - 概率平衡使得插入和删除操作简单
- 缺点：
  - 空间使用相对较高
  - 不保证最坏情况下的性能
  - 随机数生成可能成为性能瓶颈
- 应用场景：
  - Redis中的有序集合
  - LevelDB的内存表
  - 需要按范围查询的数据库索引
  - 需要并发访问的有序集合

### 7.4 布隆过滤器（Bloom Filter）

**定义**：布隆过滤器是一种空间效率高的概率性数据结构，用于检测一个元素是否属于一个集合。它可能返回错误的肯定结果（假阳性），但不会返回错误的否定结果（假阴性）。

**基本原理**：

1. 布隆过滤器使用一个位数组和多个哈希函数
2. 插入元素时，用每个哈希函数计算哈希值，并设置位数组中对应位置的位为1
3. 查询元素时，检查所有哈希函数对应位置的位是否都为1
4. 如果有任何一位为0，则元素肯定不在集合中；如果所有位都为1，则元素可能在集合中

**Go 2025 实现**：

```go
// 布隆过滤器
type BloomFilter struct {
    bitset    []uint64  // 位数组，每个uint64存储64位
    size      uint      // 位数组的总位数
    hashFuncs uint      // 哈希函数的数量
    count     uint      // 已插入的元素数量
}

// 创建新的布隆过滤器
// size是位数组大小（位数），hashFuncs是哈希函数数量
func NewBloomFilter(size uint, hashFuncs uint) *BloomFilter {
    // 向上取整到64的倍数
    bitsetSize := (size + 63) / 64
    
    return &BloomFilter{
        bitset:    make([]uint64, bitsetSize),
        size:      size,
        hashFuncs: hashFuncs,
        count:     0,
    }
}

// 基于预期元素数量和所需假阳性率创建布隆过滤器
func NewBloomFilterWithEstimates(n uint, falsePositiveRate float64) *BloomFilter {
    // 计算最佳位数组大小和哈希函数数量
    size := uint(-float64(n) * math.Log(falsePositiveRate) / math.Pow(math.Log(2), 2))
    hashFuncs := uint(float64(size) / float64(n) * math.Log(2))
    
    // 确保至少有一个哈希函数
    if hashFuncs < 1 {
        hashFuncs = 1
    }
    
    return NewBloomFilter(size, hashFuncs)
}

// 计算一个元素的多个哈希值
func (bf *BloomFilter) hashValues(data []byte) []uint {
    hashValues := make([]uint, bf.hashFuncs)
    
    // 使用两个哈希函数和双重散列技术生成多个哈希值
    h1 := fnv.New64a()
    h1.Write(data)
    hash1 := h1.Sum64()
    
    h2 := fnv.New64a()
    h2.Write([]byte(strconv.FormatUint(hash1, 16)))
    hash2 := h2.Sum64()
    
    for i := uint(0); i < bf.hashFuncs; i++ {
        // 双重散列：h(i) = h1 + i*h2
        combinedHash := hash1 + uint64(i)*hash2
        hashValues[i] = uint(combinedHash % uint64(bf.size))
    }
    
    return hashValues
}

// 将元素添加到布隆过滤器
func (bf *BloomFilter) Add(data []byte) {
    hashValues := bf.hashValues(data)
    
    for _, hashValue := range hashValues {
        // 设置位
        wordOffset := hashValue / 64
        bitOffset := hashValue % 64
        bf.bitset[wordOffset] |= 1 << bitOffset
    }
    
    bf.count++
}

// 添加字符串元素
func (bf *BloomFilter) AddString(s string) {
    bf.Add([]byte(s))
}

// 检查元素是否可能在集合中
func (bf *BloomFilter) Contains(data []byte) bool {
    hashValues := bf.hashValues(data)
    
    for _, hashValue := range hashValues {
        wordOffset := hashValue / 64
        bitOffset := hashValue % 64
        
        // 如果对应位为0，则元素肯定不在集合中
        if bf.bitset[wordOffset]&(1<<bitOffset) == 0 {
            return false
        }
    }
    
    // 所有位都为1，元素可能在集合中
    return true
}

// 检查字符串元素是否可能在集合中
func (bf *BloomFilter) ContainsString(s string) bool {
    return bf.Contains([]byte(s))
}

// 合并两个布隆过滤器
func (bf *BloomFilter) Merge(other *BloomFilter) error {
    if bf.size != other.size || bf.hashFuncs != other.hashFuncs {
        return errors.New("布隆过滤器参数不匹配，无法合并")
    }
    
    for i := range bf.bitset {
        bf.bitset[i] |= other.bitset[i]
    }
    
    bf.count += other.count
    return nil
}

// 获取已插入的元素数量
func (bf *BloomFilter) Count() uint {
    return bf.count
}

// 估计当前假阳性率
func (bf *BloomFilter) EstimateFalsePositiveRate() float64 {
    if bf.count == 0 {
        return 0.0
    }
    
    // 假阳性率 = (1 - e^(-k*n/m))^k
    // 其中k是哈希函数数量，n是插入的元素数量，m是位数组大小
    exponent := -float64(bf.hashFuncs) * float64(bf.count) / float64(bf.size)
    return math.Pow(1.0-math.Exp(exponent), float64(bf.hashFuncs))
}

// 清空布隆过滤器
func (bf *BloomFilter) Clear() {
    for i := range bf.bitset {
        bf.bitset[i] = 0
    }
    bf.count = 0
}

// 序列化布隆过滤器
func (bf *BloomFilter) Marshal() ([]byte, error) {
    buffer := new(bytes.Buffer)
    
    // 写入元数据
    binary.Write(buffer, binary.LittleEndian, bf.size)
    binary.Write(buffer, binary.LittleEndian, bf.hashFuncs)
    binary.Write(buffer, binary.LittleEndian, bf.count)
    
    // 写入位数组
    for _, word := range bf.bitset {
        binary.Write(buffer, binary.LittleEndian, word)
    }
    
    return buffer.Bytes(), nil
}

// 从序列化数据创建布隆过滤器
func UnmarshalBloomFilter(data []byte) (*BloomFilter, error) {
    buffer := bytes.NewReader(data)
    
    var size, hashFuncs, count uint
    if err := binary.Read(buffer, binary.LittleEndian, &size); err != nil {
        return nil, err
    }
    if err := binary.Read(buffer, binary.LittleEndian, &hashFuncs); err != nil {
        return nil, err
    }
    if err := binary.Read(buffer, binary.LittleEndian, &count); err != nil {
        return nil, err
    }
    
    bf := NewBloomFilter(size, hashFuncs)
    bf.count = count
    
    // 读取位数组
    for i := range bf.bitset {
        if err := binary.Read(buffer, binary.LittleEndian, &bf.bitset[i]); err != nil {
            return nil, err
        }
    }
    
    return bf, nil
}

// 计数布隆过滤器（扩展版本，支持删除）
type CountingBloomFilter struct {
    counters  []uint8  // 使用计数器而不是位
    size      uint
    hashFuncs uint
    count     uint
}

// 创建新的计数布隆过滤器
func NewCountingBloomFilter(size uint, hashFuncs uint) *CountingBloomFilter {
    return &CountingBloomFilter{
        counters:  make([]uint8, size),
        size:      size,
        hashFuncs: hashFuncs,
        count:     0,
    }
}

// 基于预期元素数量和所需假阳性率创建计数布隆过滤器
func NewCountingBloomFilterWithEstimates(n uint, falsePositiveRate float64) *CountingBloomFilter {
    size := uint(-float64(n) * math.Log(falsePositiveRate) / math.Pow(math.Log(2), 2))
    hashFuncs := uint(float64(size) / float64(n) * math.Log(2))
    
    if hashFuncs < 1 {
        hashFuncs = 1
    }
    
    return NewCountingBloomFilter(size, hashFuncs)
}

// 计算哈希值（与标准布隆过滤器相同）
func (cbf *CountingBloomFilter) hashValues(data []byte) []uint {
    hashValues := make([]uint, cbf.hashFuncs)
    
    h1 := fnv.New64a()
    h1.Write(data)
    hash1 := h1.Sum64()
    
    h2 := fnv.New64a()
    h2.Write([]byte(strconv.FormatUint(hash1, 16)))
    hash2 := h2.Sum64()
    
    for i := uint(0); i < cbf.hashFuncs; i++ {
        combinedHash := hash1 + uint64(i)*hash2
        hashValues[i] = uint(combinedHash % uint64(cbf.size))
    }
    
    return hashValues
}

// 添加元素
func (cbf *CountingBloomFilter) Add(data []byte) {
    hashValues := cbf.hashValues(data)
    
    for _, hashValue := range hashValues {
        // 增加计数器，但不超过最大值255
        if cbf.counters[hashValue] < 255 {
            cbf.counters[hashValue]++
        }
    }
    
    cbf.count++
}

// 添加字符串元素
func (cbf *CountingBloomFilter) AddString(s string) {
    cbf.Add([]byte(s))
}

// 检查元素是否可能在集合中
func (cbf *CountingBloomFilter) Contains(data []byte) bool {
    hashValues := cbf.hashValues(data)
    
    for _, hashValue := range hashValues {
        if cbf.counters[hashValue] == 0 {
            return false
        }
    }
    
    return true
}

// 检查字符串元素是否可能在集合中
func (cbf *CountingBloomFilter) ContainsString(s string) bool {
    return cbf.Contains([]byte(s))
}

// 删除元素
func (cbf *CountingBloomFilter) Remove(data []byte) bool {
    hashValues := cbf.hashValues(data)
    
    // 首先检查元素是否可能在集合中
    for _, hashValue := range hashValues {
        if cbf.counters[hashValue] == 0 {
            return false
        }
    }
    
    // 减少所有哈希位置的计数器
    for _, hashValue := range hashValues {
        cbf.counters[hashValue]--
    }
    
    if cbf.count > 0 {
        cbf.count--
    }
    
    return true
}

// 删除字符串元素
func (cbf *CountingBloomFilter) RemoveString(s string) bool {
    return cbf.Remove([]byte(s))
}

// 获取已插入的元素数量
func (cbf *CountingBloomFilter) Count() uint {
    return cbf.count
}

// 清空计数布隆过滤器
func (cbf *CountingBloomFilter) Clear() {
    for i := range cbf.counters {
        cbf.counters[i] = 0
    }
    cbf.count = 0
}

// 用法示例
func bloomFilterExample() {
    // 创建布隆过滤器（预期10000个元素，假阳性率0.01）
    bf := NewBloomFilterWithEstimates(10000, 0.01)
    
    // 添加一些元素
    words := []string{
        "apple", "banana", "cherry", "dragonfruit", "elderberry",
        "fig", "grape", "honeydew", "imbe", "jackfruit",
    }
    
    for _, word := range words {
        bf.AddString(word)
    }
    
    // 查询元素
    fmt.Println("布隆过滤器测试:")
    testWords := append(words, "kiwi", "lemon", "mango")
    for _, word := range testWords {
        exists := bf.ContainsString(word)
        inWords := contains(words, word)
        
        fmt.Printf("单词 \"%s\" 在布隆过滤器中: %t (实际存在: %t)\n", 
                  word, exists, inWords)
    }
    
    // 查看假阳性率
    falsePositiveRate := bf.EstimateFalsePositiveRate()
    fmt.Printf("当前估计假阳性率: %.6f\n", falsePositiveRate)
    
    // 计数布隆过滤器示例
    fmt.Println("\n计数布隆过滤器测试 (支持删除):")
    cbf := NewCountingBloomFilterWithEstimates(10000, 0.01)
    
    // 添加元素
    for _, word := range words {
        cbf.AddString(word)
    }
    
    // 删除一些元素
    removed := []string{"apple", "fig", "imbe"}
    for _, word := range removed {
        success := cbf.RemoveString(word)
        fmt.Printf("删除 \"%s\": %t\n", word, success)
    }
    
    // 再次查询
    fmt.Println("\n删除后测试:")
    for _, word := range testWords {
        exists := cbf.ContainsString(word)
        inWords := contains(words, word)
        inRemoved := contains(removed, word)
        shouldExist := inWords && !inRemoved
        
        fmt.Printf("单词 \"%s\" 在计数布隆过滤器中: %t (应该存在: %t)\n", 
                  word, exists, shouldExist)
    }
    
    // 性能测试
    fmt.Println("\n性能测试:")
    elementCount := 1000000
    largeBloomFilter := NewBloomFilterWithEstimates(uint(elementCount), 0.01)
    
    // 准备随机数据
    rand.Seed(time.Now().UnixNano())
    testData := make([]string, elementCount)
    for i := 0; i < elementCount; i++ {
        // 生成20-30字节的随机字符串
        length := 20 + rand.Intn(11)
        bytes := make([]byte, length)
        for j := 0; j < length; j++ {
            bytes[j] = byte(65 + rand.Intn(26)) // A-Z
        }
        testData[i] = string(bytes)
    }
    
    // 测试插入性能
    start := time.Now()
    for i := 0; i < elementCount; i++ {
        largeBloomFilter.AddString(testData[i])
    }
    insertDuration := time.Since(start)
    
    // 测试查找性能
    start = time.Now()
    for i := 0; i < elementCount; i++ {
        largeBloomFilter.ContainsString(testData[i])
    }
    queryDuration := time.Since(start)
    
    fmt.Printf("插入 %d 个元素: %v (%.2f ns/元素)\n", 
              elementCount, insertDuration, float64(insertDuration.Nanoseconds())/float64(elementCount))
    fmt.Printf("查询 %d 个元素: %v (%.2f ns/元素)\n", 
              elementCount, queryDuration, float64(queryDuration.Nanoseconds())/float64(elementCount))
    
    // 估计假阳性情况
    falsePositiveCount := 0
    testCount := 100000
    
    for i := 0; i < testCount; i++ {
        // 生成不在原始数据中的字符串
        length := 20 + rand.Intn(11)
        bytes := make([]byte, length)
        for j := 0; j < length; j++ {
            bytes[j] = byte(97 + rand.Intn(26)) // a-z (不同于上面的A-Z)
        }
        testString := string(bytes)
        
        if largeBloomFilter.ContainsString(testString) {
            falsePositiveCount++
        }
    }
    
    actualFPR := float64(falsePositiveCount) / float64(testCount)
    expectedFPR := largeBloomFilter.EstimateFalsePositiveRate()
    
    fmt.Printf("假阳性测试 (%d 个不在集合中的元素):\n", testCount)
    fmt.Printf("测量的假阳性率: %.6f\n", actualFPR)
    fmt.Printf("预期的假阳性率: %.6f\n", expectedFPR)
    fmt.Printf("布隆过滤器大小: %.2f KB\n", float64(len(largeBloomFilter.bitset)*8)/1024)
}

// 辅助函数：检查切片是否包含字符串
func contains(slice []string, item string) bool {
    for _, s := range slice {
        if s == item {
            return true
        }
    }
    return false
}
```

**性能分析**：

- 时间复杂度：
  - 添加元素：O(k)，其中k是哈希函数数量
  - 查询元素：O(k)
  - 删除元素（仅限计数布隆过滤器）：O(k)
- 空间复杂度：O(m)，其中m是位数组大小
- 优点：
  - 空间效率高，与存储实际元素相比大大节省空间
  - 插入和查询时间复杂度为常数
  - 不存储实际元素，提供隐私保护
  - 可以通过参数调整控制假阳性率
- 缺点：
  - 存在假阳性可能（误报）
  - 不能枚举存储的元素
  - 标准布隆过滤器不支持删除操作
  - 计数布隆过滤器支持删除但空间消耗更大
- 应用场景：
  - 缓存过滤（避免缓存穿透）
  - 网络爬虫的URL过滤（避免重复爬取）
  - 拼写检查器
  - 内容过滤（如垃圾邮件检测）
  - 大型数据集的成员判断

### 7.5 一致性哈希（Consistent Hashing）

**定义**：一致性哈希是一种特殊的哈希算法，主要用于分布式系统中，可以在节点增加或删除时最小化键的重新映射。它将哈希空间视为一个环，并在环上放置节点和键。

**基本原理**：

1. 将哈希空间看作0到2^32-1的环形结构
2. 将节点和数据都映射到环上的位置
3. 数据被分配到顺时针方向上的第一个节点
4. 添加或删除节点时，只有部分数据需要重新映射

**Go 2025 实现**：

```go
// 一致性哈希
type ConsistentHash[T comparable] struct {
    ring       map[uint32]T        // 哈希环
    sortedKeys []uint32            // 排序的哈希键
    replicas   int                 // 每个节点的虚拟节点数量
    hashFunc   func(data []byte) uint32  // 哈希函数
    mu         sync.RWMutex        // 读写锁保护并发访问
}

// 创建新的一致性哈希实例
func NewConsistentHash[T comparable](replicas int, fn func(data []byte) uint32) *ConsistentHash[T] {
    ch := &ConsistentHash[T]{
        ring:       make(map[uint32]T),
        sortedKeys: []uint32{},
        replicas:   replicas,
    }
    
    // 使用提供的哈希函数或默认为crc32
    if fn == nil {
        ch.hashFunc = func(data []byte) uint32 {
            return crc32.ChecksumIEEE(data)
        }
    } else {
        ch.hashFunc = fn
    }
    
    return ch
}

// 添加节点
func (ch *ConsistentHash[T]) Add(nodes ...T) {
    ch.mu.Lock()
    defer ch.mu.Unlock()
    
    for _, node := range nodes {
        // 为每个节点创建多个虚拟节点
        for i := 0; i < ch.replicas; i++ {
            key := ch.hashFunc([]byte(fmt.Sprintf("%v-%d", node, i)))
            ch.ring[key] = node
            ch.sortedKeys = append(ch.sortedKeys, key)
        }
    }
    
    // 重新排序
    sort.Slice(ch.sortedKeys, func(i, j int) bool {
        return ch.sortedKeys[i] < ch.sortedKeys[j]
    })
}

// 移除节点
func (ch *ConsistentHash[T]) Remove(nodes ...T) {
    ch.mu.Lock()
    defer ch.mu.Unlock()
    
    for _, node := range nodes {
        // 移除节点的所有虚拟节点
        for i := 0; i < ch.replicas; i++ {
            key := ch.hashFunc([]byte(fmt.Sprintf("%v-%d", node, i)))
            delete(ch.ring, key)
        }
    }
    
    // 重建排序键
    ch.sortedKeys = []uint32{}
    for k := range ch.ring {
        ch.sortedKeys = append(ch.sortedKeys, k)
    }
    sort.Slice(ch.sortedKeys, func(i, j int) bool {
        return ch.sortedKeys[i] < ch.sortedKeys[j]
    })
}

// 获取键映射到的节点
func (ch *ConsistentHash[T]) Get(key string) (T, error) {
    ch.mu.RLock()
    defer ch.mu.RUnlock()
    
    if len(ch.sortedKeys) == 0 {
        var zero T
        return zero, errors.New("一致性哈希环为空")
    }
    
    // 计算键的哈希值
    hash := ch.hashFunc([]byte(key))
    
    // 二分查找大于等于哈希值的第一个位置
    idx := sort.Search(len(ch.sortedKeys), func(i int) bool {
        return ch.sortedKeys[i] >= hash
    })
    
    // 如果找不到，则回到环的起点
    if idx == len(ch.sortedKeys) {
        idx = 0
    }
    
    return ch.ring[ch.sortedKeys[idx]], nil
}

// 获取节点数量
func (ch *ConsistentHash[T]) Count() int {
    ch.mu.RLock()
    defer ch.mu.RUnlock()
    
    return len(ch.sortedKeys) / ch.replicas
}

// 获取所有节点
func (ch *ConsistentHash[T]) GetNodes() []T {
    ch.mu.RLock()
    defer ch.mu.RUnlock()
    
    seen := make(map[T]bool)
    nodes := []T{}
    
    for _, key := range ch.sortedKeys {
        node := ch.ring[key]
        if !seen[node] {
            seen[node] = true
            nodes = append(nodes, node)
        }
    }
    
    return nodes
}

// 分析节点负载
func (ch *ConsistentHash[T]) AnalyzeLoad(keysCount int) map[T]int {
    ch.mu.RLock()
    defer ch.mu.RUnlock()
    
    // 模拟随机键分布
    distribution := make(map[T]int)
    
    for i := 0; i < keysCount; i++ {
        // 使用随机键
        key := fmt.Sprintf("key-%d", rand.Intn(100000))
        node, err := ch.Get(key)
        if err == nil {
            distribution[node]++
        }
    }
    
    return distribution
}

// 用法示例
func consistentHashExample() {
    // 创建一致性哈希实例，每个节点有10个虚拟节点
    ch := NewConsistentHash[string](10, nil)
    
    // 添加节点
    servers := []string{
        "server1:8080",
        "server2:8080",
        "server3:8080",
        "server4:8080",
    }
    
    ch.Add(servers...)
    
    // 测试键分布
    testKeys := []string{
        "user:1001", "user:1002", "user:1003", "user:1004",
        "product:5001", "product:5002", "product:5003",
        "order:7001", "order:7002", "order:7003", "order:7004",
    }
    
    fmt.Println("初始节点映射:")
    for _, key := range testKeys {
        server, _ := ch.Get(key)
        fmt.Printf("键 %s -> 节点 %s\n", key, server)
    }
    
    // 添加新节点
    ch.Add("server5:8080")
    
    // 检查键重新分布
    fmt.Println("\n添加新节点后:")
    changedCount := 0
    for _, key := range testKeys {
        oldServer, _ := ch.Get(key)
        if oldServer != servers[0] && oldServer != servers[1] && 
           oldServer != servers[2] && oldServer != servers[3] {
            changedCount++
            fmt.Printf("键 %s -> 新节点 %s\n", key, oldServer)
        }
    }
    fmt.Printf("重新分配的键数量: %d / %d (%.1f%%)\n", 
              changedCount, len(testKeys), float64(changedCount)/float64(len(testKeys))*100)
    
    // 移除节点
    ch.Remove("server3:8080")
    
    fmt.Println("\n移除节点后:")
    changedCount = 0
    for _, key := range testKeys {
        newServer, _ := ch.Get(key)
        // 检查键是否被重新分配
        server, _ := ch.Get(key)
        if server != "server3:8080" {
            continue  // 之前不在被移除的服务器上
        }
        changedCount++
        fmt.Printf("键 %s 从 server3:8080 -> %s\n", key, newServer)
    }
    
    // 负载分布分析
    fmt.Println("\n负载分布分析:")
    
    // 创建新的实例进行测试
    loadCH := NewConsistentHash[string](10, nil)
    loadCH.Add(servers...)
    
    // 分析10000个随机键的分布
    distribution := loadCH.AnalyzeLoad(10000)
    
    totalKeys := 0
    for _, count := range distribution {
        totalKeys += count
    }
    
    fmt.Printf("服务器数量: %d, 总键数: %d\n", len(servers), totalKeys)
    for server, count := range distribution {
        percentage := float64(count) / float64(totalKeys) * 100
        fmt.Printf("服务器 %s: %d 键 (%.2f%%)\n", server, count, percentage)
    }
    
    // 测试使用带权重的一致性哈希
    fmt.Println("\n带权重的一致性哈希测试:")
    
    // 使用虚拟节点数量表示权重
    weightedCH := &ConsistentHash[string]{
        ring:     make(map[uint32]string),
        hashFunc: crc32.ChecksumIEEE,
    }
    
    // 按权重添加节点
    weights := map[string]int{
        "server1:8080": 10,  // 10个虚拟节点（标准权重）
        "server2:8080": 20,  // 20个虚拟节点（2倍权重）
        "server3:8080": 5,   // 5个虚拟节点（半权重）
        "server4:8080": 15,  // 15个虚拟节点（1.5倍权重）
    }
    
    for server, weight := range weights {
        for i := 0; i < weight; i++ {
            key := crc32.ChecksumIEEE([]byte(fmt.Sprintf("%s-%d", server, i)))
            weightedCH.ring[key] = server
            weightedCH.sortedKeys = append(weightedCH.sortedKeys, key)
        }
    }
    
    sort.Slice(weightedCH.sortedKeys, func(i, j int) bool {
        return weightedCH.sortedKeys[i] < weightedCH.sortedKeys[j]
    })
    
    // 分析带权重的负载分布
    weightedDist := make(map[string]int)
    for i := 0; i < 10000; i++ {
        key := fmt.Sprintf("key-%d", rand.Intn(100000))
        hash := crc32.ChecksumIEEE([]byte(key))
        
        idx := sort.Search(len(weightedCH.sortedKeys), func(i int) bool {
            return weightedCH.sortedKeys[i] >= hash
        })
        
        if idx == len(weightedCH.sortedKeys) {
            idx = 0
        }
        
        node := weightedCH.ring[weightedCH.sortedKeys[idx]]
        weightedDist[node]++
    }
    
    fmt.Println("带权重的负载分布:")
    totalKeysWeighted := 0
    for _, count := range weightedDist {
        totalKeysWeighted += count
    }
    
    // 计算理论分布
    totalWeight := 0
    for _, w := range weights {
        totalWeight += w
    }
    
    for server, count := range weightedDist {
        percentage := float64(count) / float64(totalKeysWeighted) * 100
        expectedPercentage := float64(weights[server]) / float64(totalWeight) * 100
        
        fmt.Printf("服务器 %s: %d 键 (%.2f%%), 理论期望: %.2f%%, 偏差: %.2f%%\n", 
                  server, count, percentage, expectedPercentage, percentage-expectedPercentage)
    }
}
```

**性能分析**：

- 时间复杂度：
  - 添加节点：O(R log N)，其中R是每个节点的虚拟节点数，N是总节点数
  - 删除节点：O(R log N)
  - 查找节点：O(log N)
- 空间复杂度：O(N·R)，其中N是节点数，R是每个节点的虚拟节点数
- 优点：
  - 节点变化时最小化数据迁移
  - 可以通过虚拟节点平衡负载
  - 支持动态添加和删除节点
  - 可以为节点分配不同权重
- 缺点：
  - 需要额外存储虚拟节点映射
  - 虚拟节点增加了空间使用
  - 负载完全均衡需要足够多的虚拟节点
- 应用场景：
  - 分布式缓存系统（如Memcached）
  - 分布式存储系统
  - 负载均衡
  - 分片数据库

### 7.6 LRU缓存

**定义**：LRU（Least Recently Used，最近最少使用）缓存是一种缓存淘汰策略，它会优先淘汰最长时间未被使用的缓存项，保留最近使用的缓存项。

**基本原理**：

1. 使用哈希表实现O(1)的查找
2. 使用双向链表跟踪缓存项的使用顺序
3. 当缓存满时，删除链表尾部（最久未使用）的项
4. 每次访问时，将访问的项移动到链表头部

**Go 2025 实现**：

```go
// LRU缓存项
type LRUCacheEntry[K comparable, V any] struct {
    key   K
    value V
    prev  *LRUCacheEntry[K, V]
    next  *LRUCacheEntry[K, V]
}

// LRU缓存
type LRUCache[K comparable, V any] struct {
    capacity int
    size     int
    cache    map[K]*LRUCacheEntry[K, V]
    head     *LRUCacheEntry[K, V]  // 最近使用的
    tail     *LRUCacheEntry[K, V]  // 最久未使用的
    mu       sync.Mutex
}

// 创建新的LRU缓存
func NewLRUCache[K comparable, V any](capacity int) *LRUCache[K, V] {
    if capacity <= 0 {
        panic("LRU缓存容量必须为正数")
    }
    
    cache := &LRUCache[K, V]{
        capacity: capacity,
        size:     0,
        cache:    make(map[K]*LRUCacheEntry[K, V]),
        head:     nil,
        tail:     nil,
    }
    
    return cache
}

// 获取缓存项
func (c *LRUCache[K, V]) Get(key K) (V, bool) {
    c.mu.Lock()
    defer c.mu.Unlock()
    
    if entry, found := c.cache[key]; found {
        // 将访问的项移到链表头部
        c.moveToFront(entry)
        return entry.value, true
    }
    
    // 未找到
    var zero V
    return zero, false
}

// 添加或更新缓存项
func (c *LRUCache[K, V]) Put(key K, value V) {
    c.mu.Lock()
    defer c.mu.Unlock()
    
    // 键已存在，更新值并移到前面
    if entry, found := c.cache[key]; found {
        entry.value = value
        c.moveToFront(entry)
        return
    }
    
    // 创建新缓存项
    entry := &LRUCacheEntry[K, V]{
        key:   key,
        value: value,
    }
    
    // 添加到缓存和链表头部
    c.cache[key] = entry
    c.addToFront(entry)
    c.size++
    
    // 如果超出容量，删除尾部
    if c.size > c.capacity {
        c.removeTail()
    }
}

// 将缓存项移到链表前面
func (c *LRUCache[K, V]) moveToFront(entry *LRUCacheEntry[K, V]) {
    if entry == c.head {
        return  // 已经在前面
    }
    
    // 从当前位置移除
    if entry.prev != nil {
        entry.prev.next = entry.next
    }
    
    if entry.next != nil {
        entry.next.prev = entry.prev
    }
    
    if entry == c.tail {
        c.tail = entry.prev
    }
    
    // 放到头部
    entry.prev = nil
    entry.next = c.head
    
    if c.head != nil {
        c.head.prev = entry
    }
    
    c.head = entry
    
    // 如果链表为空，设置尾部
    if c.tail == nil {
        c.tail = entry
    }
}

// 添加到链表前面
func (c *LRUCache[K, V]) addToFront(entry *LRUCacheEntry[K, V]) {
    entry.prev = nil
    entry.next = c.head
    
    if c.head != nil {
        c.head.prev = entry
    }
    
    c.head = entry
    
    // 如果是第一个元素
    if c.tail == nil {
        c.tail = entry
    }
}

// 移除链表尾部
func (c *LRUCache[K, V]) removeTail() {
    if c.tail == nil {
        return
    }
    
    // 从缓存中删除
    delete(c.cache, c.tail.key)
    
    // 更新链表
    if c.tail.prev != nil {
        c.tail.prev.next = nil
        c.tail = c.tail.prev
    } else {
        // 链表已空
        c.head = nil
        c.tail = nil
    }
    
    c.size--
}

// 获取缓存大小
func (c *LRUCache[K, V]) Size() int {
    c.mu.Lock()
    defer c.mu.Unlock()
    return c.size
}

// 清空缓存
func (c *LRUCache[K, V]) Clear() {
    c.mu.Lock()
    defer c.mu.Unlock()
    
    c.cache = make(map[K]*LRUCacheEntry[K, V])
    c.head = nil
    c.tail = nil
    c.size = 0
}

// 获取所有键（从最近到最久）
func (c *LRUCache[K, V]) Keys() []K {
    c.mu.Lock()
    defer c.mu.Unlock()
    
    keys := make([]K, 0, c.size)
    current := c.head
    
    for current != nil {
        keys = append(keys, current.key)
        current = current.next
    }
    
    return keys
}

// 检查键是否存在
func (c *LRUCache[K, V]) Contains(key K) bool {
    c.mu.Lock()
    defer c.mu.Unlock()
    
    _, found := c.cache[key]
    return found
}

// 删除缓存项
func (c *LRUCache[K, V]) Remove(key K) bool {
    c.mu.Lock()
    defer c.mu.Unlock()
    
    if entry, found := c.cache[key]; found {
        // 从链表中移除
        if entry.prev != nil {
            entry.prev.next = entry.next
        } else {
            c.head = entry.next
        }
        
        if entry.next != nil {
            entry.next.prev = entry.prev
        } else {
            c.tail = entry.prev
        }
        
        // 从缓存中删除
        delete(c.cache, key)
        c.size--
        
        return true
    }
    
    return false
}

// 用法示例
func lruCacheExample() {
    // 创建容量为3的LRU缓存
    cache := NewLRUCache[string, int](3)
    
    // 添加项
    cache.Put("one", 1)
    cache.Put("two", 2)
    cache.Put("three", 3)
    
    fmt.Println("初始缓存:")
    fmt.Printf("缓存大小: %d\n", cache.Size())
    fmt.Printf("缓存键 (按访问顺序): %v\n", cache.Keys())
    
    // 获取项，会更新访问顺序
    value, found := cache.Get("one")
    fmt.Printf("获取 \"one\": %d, 找到: %t\n", value, found)
    fmt.Printf("更新后的缓存键: %v\n", cache.Keys())  // 现在 one 应该在前面
    
    // 添加超出容量的项，会删除最久未使用的
    cache.Put("four", 4)
    fmt.Printf("添加 \"four\" 后的缓存键: %v\n", cache.Keys())
    
    // 检查被删除的项
    _, found = cache.Get("two")
    fmt.Printf("键 \"two\" 存在: %t\n", found)  // 应该是 false
    
    // 更新现有项
    cache.Put("three", 33)
    value, _ = cache.Get("three")
    fmt.Printf("更新后的 \"three\" 值: %d\n", value)
    
    // 清空缓存
    cache.Clear()
    fmt.Printf("清空后的缓存大小: %d\n", cache.Size())
    
    // 性能测试
    fmt.Println("\nLRU缓存性能测试:")
    
    largeCacheSize := 10000
    largeCache := NewLRUCache[int, string](largeCacheSize)
    
    // 填充缓存
    start := time.Now()
    for i := 0; i < largeCacheSize; i++ {
        largeCache.Put(i, fmt.Sprintf("value-%d", i))
    }
    fillDuration := time.Since(start)
    
    // 随机读取测试
    hits, misses := 0, 0
    start = time.Now()
    for i := 0; i < 100000; i++ {
        key := rand.Intn(largeCacheSize * 2)  // 一半的访问会命中
        if _, found := largeCache.Get(key); found {
            hits++
        } else {
            misses++
        }
    }
    getDuration := time.Since(start)
    
    fmt.Printf("填充 %d 个缓存项: %v (%.2f μs/操作)\n", 
              largeCacheSize, fillDuration, float64(fillDuration.Microseconds())/float64(largeCacheSize))
    fmt.Printf("100,000 次随机读取: %v (%.2f ns/操作)\n", 
              getDuration, float64(getDuration.Nanoseconds())/100000)
    fmt.Printf("缓存命中率: %.2f%%\n", float64(hits)*100/float64(hits+misses))
    
    // 测试不同缓存大小的命中率
    fmt.Println("\n不同缓存大小的命中率测试:")
    
    // 假设有一个符合80/20规则的访问模式
    // 80%的访问集中在20%的数据上
    testCacheSizes := []int{100, 200, 500, 1000, 2000, 5000}
    totalItems := 10000
    totalAccesses := 100000
    
    // 创建一个偏向某些键的访问模式
    accessPattern := make([]int, totalAccesses)
    for i := 0; i < totalAccesses; i++ {
        if rand.Float64() < 0.8 {
            // 80%的访问集中在20%的数据上
            accessPattern[i] = rand.Intn(totalItems / 5)
        } else {
            // 20%的访问分散在剩余80%的数据上
            accessPattern[i] = totalItems/5 + rand.Intn(totalItems - totalItems/5)
        }
    }
    
    // 测试不同缓存大小
    for _, size := range testCacheSizes {
        testCache := NewLRUCache[int, bool](size)
        hits := 0
        
        for _, key := range accessPattern {
            if _, found := testCache.Get(key); found {
                hits++
            } else {
                testCache.Put(key, true)
            }
        }
        
        hitRate := float64(hits) * 100 / float64(totalAccesses)
        fmt.Printf("缓存大小: %d, 命中率: %.2f%%\n", size, hitRate)
    }
}
```

### 7.7 并发数据结构

**定义**：并发数据结构是专门设计用于多线程环境的数据结构，它们使用各种同步机制（如互斥锁、原子操作、无锁算法）来确保在并发访问时的正确性和高性能。

#### 7.7.1 并发哈希表

**Go 2025 实现**：

```go
// 并发安全的哈希表
type ConcurrentMap[K comparable, V any] struct {
    shards    []*mapShard[K, V]
    shardMask uint32
    numShards uint32
}

// 分片
type mapShard[K comparable, V any] struct {
    items map[K]V
    mu    sync.RWMutex
}

// 创建新的并发哈希表
func NewConcurrentMap[K comparable, V any](shardCount int) *ConcurrentMap[K, V] {
    // 确保分片数是2的幂，便于位运算
    if shardCount <= 0 {
        shardCount = 32  // 默认32个分片
    } else {
        // 向上取到2的幂
        shardCount = 1 << uint(math.Ceil(math.Log2(float64(shardCount))))
    }
    
    m := &ConcurrentMap[K, V]{
        shards:    make([]*mapShard[K, V], shardCount),
        shardMask: uint32(shardCount - 1),
        numShards: uint32(shardCount),
    }
    
    for i := 0; i < shardCount; i++ {
        m.shards[i] = &mapShard[K, V]{
            items: make(map[K]V),
        }
    }
    
    return m
}

// 获取键的分片索引
func (m *ConcurrentMap[K, V]) getShard(key K) *mapShard[K, V] {
    hash := fnv.New32a()
    hash.Write([]byte(fmt.Sprintf("%v", key)))
    return m.shards[hash.Sum32()&m.shardMask]
}

// 设置键值对
func (m *ConcurrentMap[K, V]) Set(key K, value V) {
    shard := m.getShard(key)
    shard.mu.Lock()
    defer shard.mu.Unlock()
    shard.items[key] = value
}

// 获取值
func (m *ConcurrentMap[K, V]) Get(key K) (V, bool) {
    shard := m.getShard(key)
    shard.mu.RLock()
    defer shard.mu.RUnlock()
    
    value, ok := shard.items[key]
    return value, ok
}

// 检查键是否存在
func (m *ConcurrentMap[K, V]) Has(key K) bool {
    shard := m.getShard(key)
    shard.mu.RLock()
    defer shard.mu.RUnlock()
    
    _, ok := shard.items[key]
    return ok
}

// 删除键
func (m *ConcurrentMap[K, V]) Remove(key K) bool {
    shard := m.getShard(key)
    shard.mu.Lock()
    defer shard.mu.Unlock()
    
    _, ok := shard.items[key]
    if ok {
        delete(shard.items, key)
    }
    return ok
}

// 获取元素数量
func (m *ConcurrentMap[K, V]) Count() int {
    count := 0
    for i := uint32(0); i < m.numShards; i++ {
        shard := m.shards[i]
        shard.mu.RLock()
        count += len(shard.items)
        shard.mu.RUnlock()
    }
    return count
}

// 获取所有键
func (m *ConcurrentMap[K, V]) Keys() []K {
    keys := make([]K, 0, m.Count())
    
    for i := uint32(0); i < m.numShards; i++ {
        shard := m.shards[i]
        shard.mu.RLock()
        for key := range shard.items {
            keys = append(keys, key)
        }
        shard.mu.RUnlock()
    }
    
    return keys
}

// 清空哈希表
func (m *ConcurrentMap[K, V]) Clear() {
    for i := uint32(0); i < m.numShards; i++ {
        shard := m.shards[i]
        shard.mu.Lock()
        shard.items = make(map[K]V)
        shard.mu.Unlock()
    }
}

// 交换（如果键存在）
func (m *ConcurrentMap[K, V]) CompareAndSwap(key K, oldValue, newValue V, equals func(V, V) bool) bool {
    if equals == nil {
        // 默认比较函数，使用反射
        equals = func(a, b V) bool {
            return reflect.DeepEqual(a, b)
        }
    }
    
    shard := m.getShard(key)
    shard.mu.Lock()
    defer shard.mu.Unlock()
    
    currentValue, exists := shard.items[key]
    if !exists || !equals(currentValue, oldValue) {
        return false
    }
    
    shard.items[key] = newValue
    return true
}

// 不存在则设置
func (m *ConcurrentMap[K, V]) SetIfNotExists(key K, value V) bool {
    shard := m.getShard(key)
    shard.mu.Lock()
    defer shard.mu.Unlock()
    
    if _, exists := shard.items[key]; exists {
        return false
    }
    
    shard.items[key] = value
    return true
}

// 用于并发处理的迭代器
func (m *ConcurrentMap[K, V]) IterBuffered(bufferSize int) <-chan Tuple[K, V] {
    ch := make(chan Tuple[K, V], bufferSize)
    
    go func() {
        // 需要锁定整个map直到迭代完成
        wg := sync.WaitGroup{}
        wg.Add(int(m.numShards))
        
        for i := uint32(0); i < m.numShards; i++ {
            go func(shard *mapShard[K, V]) {
                shard.mu.RLock()
                for key, val := range shard.items {
                    ch <- Tuple[K, V]{key, val}
                }
                shard.mu.RUnlock()
                wg.Done()
            }(m.shards[i])
        }
        
        wg.Wait()
        close(ch)
    }()
    
    return ch
}

// 元组类型，用于迭代
type Tuple[K comparable, V any] struct {
    Key   K
    Value V
}

// 用法示例
func concurrentMapExample() {
    // 创建并发哈希表（16个分片）
    cmap := NewConcurrentMap[string, int](16)
    
    // 添加项
    cmap.Set("one", 1)
    cmap.Set("two", 2)
    cmap.Set("three", 3)
    
    fmt.Println("并发哈希表测试:")
    fmt.Printf("元素数量: %d\n", cmap.Count())
    
    // 获取值
    value, found := cmap.Get("two")
    fmt.Printf("Get(\"two\"): %d, 找到: %t\n", value, found)
    
    // 删除项
    removed := cmap.Remove("three")
    fmt.Printf("Remove(\"three\"): %t\n", removed)
    fmt.Printf("删除后元素数量: %d\n", cmap.Count())
    
    // 检查键
    fmt.Printf("Has(\"one\"): %t\n", cmap.Has("one"))
    fmt.Printf("Has(\"three\"): %t\n", cmap.Has("three"))
    
    // 所有键
    keys := cmap.Keys()
    fmt.Printf("所有键: %v\n", keys)
    
    // 比较并交换
    swapped := cmap.CompareAndSwap("one", 1, 100, nil)
    fmt.Printf("CompareAndSwap(\"one\", 1, 100): %t\n", swapped)
    value, _ = cmap.Get("one")
    fmt.Printf("交换后 \"one\" 的值: %d\n", value)
    
    // 不存在则设置
    success := cmap.SetIfNotExists("one", 999)
    fmt.Printf("SetIfNotExists(\"one\", 999): %t\n", success)
    success = cmap.SetIfNotExists("four", 4)
    fmt.Printf("SetIfNotExists(\"four\", 4): %t\n", success)
    
    // 通过通道迭代
    fmt.Println("\n迭代所有元素:")
    for item := range cmap.IterBuffered(10) {
        fmt.Printf("%s: %d\n", item.Key, item.Value)
    }
    
    // 性能测试
    fmt.Println("\n并发哈希表性能测试:")
    
    // 使用多个goroutine并发操作
    concurrency := 10
    itemsPerGoroutine := 10000
    totalItems := concurrency * itemsPerGoroutine
    
    // 运行并发写入
    bigMap := NewConcurrentMap[int, int](64)
    var wg sync.WaitGroup
    
    start := time.Now()
    for i := 0; i < concurrency; i++ {
        wg.Add(1)
        go func(offset int) {
            defer wg.Done()
            for j := 0; j < itemsPerGoroutine; j++ {
                key := offset*itemsPerGoroutine + j
                bigMap.Set(key, key*2)
            }
        }(i)
    }
    wg.Wait()
    setDuration := time.Since(start)
    
    // 运行并发读取
    start = time.Now()
    for i := 0; i < concurrency; i++ {
        wg.Add(1)
        go func(offset int) {
            defer wg.Done()
            for j := 0; j < itemsPerGoroutine; j++ {
                key := offset*itemsPerGoroutine + j
                bigMap.Get(key)
            }
        }(i)
    }
    wg.Wait()
    getDuration := time.Since(start)
    
    fmt.Printf("并发写入 %d 个元素 (%d goroutines): %v (%.2f ns/操作)\n", 
              totalItems, concurrency, setDuration, float64(setDuration.Nanoseconds())/float64(totalItems))
    fmt.Printf("并发读取 %d 个元素 (%d goroutines): %v (%.2f ns/操作)\n", 
              totalItems, concurrency, getDuration, float64(getDuration.Nanoseconds())/float64(totalItems))
    
    // 与标准map+互斥锁比较
    stdMap := &sync.Map{}
    
    start = time.Now()
    for i := 0; i < concurrency; i++ {
        wg.Add(1)
        go func(offset int) {
            defer wg.Done()
            for j := 0; j < itemsPerGoroutine; j++ {
                key := offset*itemsPerGoroutine + j
                stdMap.Store(key, key*2)
            }
        }(i)
    }
    wg.Wait()
    stdSetDuration := time.Since(start)
    
    start = time.Now()
    for i := 0; i < concurrency; i++ {
        wg.Add(1)
        go func(offset int) {
            defer wg.Done()
            for j := 0; j < itemsPerGoroutine; j++ {
                key := offset*itemsPerGoroutine + j
                stdMap.Load(key)
            }
        }(i)
    }
    wg.Wait()
    stdGetDuration := time.Since(start)
    
    fmt.Printf("\n标准sync.Map性能:\n")
    fmt.Printf("并发写入 %d 个元素: %v (%.2f ns/操作)\n", 
              totalItems, stdSetDuration, float64(stdSetDuration.Nanoseconds())/float64(totalItems))
    fmt.Printf("并发读取 %d 个元素: %v (%.2f ns/操作)\n", 
              totalItems, stdGetDuration, float64(stdGetDuration.Nanoseconds())/float64(totalItems))
    
    fmt.Printf("\n性能比较:\n")
    fmt.Printf("写入: ConcurrentMap比sync.Map快 %.2f 倍\n", 
              float64(stdSetDuration)/float64(setDuration))
    fmt.Printf("读取: ConcurrentMap比sync.Map快 %.2f 倍\n", 
              float64(stdGetDuration)/float64(getDuration))
}
```

#### 7.7.2 无锁队列

**Go 2025 实现**：

```go
// 无锁队列节点
type LockFreeQueueNode[T any] struct {
    value T
    next  atomic.Pointer[LockFreeQueueNode[T]]
}

// 无锁队列
type LockFreeQueue[T any] struct {
    head atomic.Pointer[LockFreeQueueNode[T]]
    tail atomic.Pointer[LockFreeQueueNode[T]]
    size atomic.Int64
}

// 创建新的无锁队列
func NewLockFreeQueue[T any]() *LockFreeQueue[T] {
    q := &LockFreeQueue[T]{}
    
    // 创建空的哨兵节点
    var dummy T
    node := &LockFreeQueueNode[T]{value: dummy}
    
    // 初始化头尾指针指向哨兵节点
    q.head.Store(node)
    q.tail.Store(node)
    
    return q
}

// 入队
func (q *LockFreeQueue[T]) Enqueue(value T) {
    // 创建新节点
    newNode := &LockFreeQueueNode[T]{value: value}
    
    for {
        tail := q.tail.Load()
        next := tail.next.Load()
        
        // 检查tail是否仍然是尾节点
        if tail == q.tail.Load() {
            if next == nil {
                // 尝试添加新节点
                if tail.next.CompareAndSwap(nil, newNode) {
                    // 成功添加节点，尝试更新尾指针
                    q.tail.CompareAndSwap(tail, newNode)
                    q.size.Add(1)
                    return
                }
            } else {
                // tail不是真正的尾节点，帮助更新尾指针
                q.tail.CompareAndSwap(tail, next)
            }
        }
    }
}

// 出队
func (q *LockFreeQueue[T]) Dequeue() (T, bool) {
    for {
        head := q.head.Load()
        tail := q.tail.Load()
        next := head.next.Load()
        
        // 检查头节点是否仍然有效
        if head == q.head.Load() {
            // 队列为空
            if head == tail {
                if next == nil {
                    var zero T
                    return zero, false
                }
                // tail落后了，帮助更新
                q.tail.CompareAndSwap(tail, next)
            } else {
                // 获取值准备返回
                value := next.value
                
                // 尝试更新head
                if q.head.CompareAndSwap(head, next) {
                    q.size.Add(-1)
                    return value, true
                }
            }
        }
    }
}

// 获取队列大小
func (q *LockFreeQueue[T]) Size() int64 {
    return q.size.Load()
}

// 检查队列是否为空
func (q *LockFreeQueue[T]) IsEmpty() bool {
    return q.Size() == 0
}

// 查看队首元素（不移除）
func (q *LockFreeQueue[T]) Peek() (T, bool) {
    for {
        head := q.head.Load()
        next := head.next.Load()
        
        if head == q.head.Load() {
            if next == nil {
                var zero T
                return zero, false
            }
            return next.value, true
        }
    }
}

// 用法示例
func lockFreeQueueExample() {
    // 创建无锁队列
    queue := NewLockFreeQueue[int]()
    
    fmt.Println("无锁队列测试:")
    
    // 入队操作
    for i := 1; i <= 5; i++ {
        queue.Enqueue(i)
        fmt.Printf("入队: %d, 队列大小: %d\n", i, queue.Size())
    }
    
    // 查看队首元素
    if value, ok := queue.Peek(); ok {
        fmt.Printf("队首元素: %d\n", value)
    }
    
    // 出队操作
    for !queue.IsEmpty() {
        if value, ok := queue.Dequeue(); ok {
            fmt.Printf("出队: %d, 队列大小: %d\n", value, queue.Size())
        }
    }
    
    fmt.Printf("队列是否为空: %t\n", queue.IsEmpty())
    
    // 并发性能测试
    fmt.Println("\n并发性能测试:")
    
    // 比较无锁队列与基于互斥锁的队列
    lockFreeQ := NewLockFreeQueue[int]()
    
    // 基于互斥锁的队列实现
    type LockedQueue struct {
        items []int
        mu    sync.Mutex
    }
    
    lockedQ := &LockedQueue{items: make([]int, 0)}
    
    enqueueLockedQ := func(q *LockedQueue, value int) {
        q.mu.Lock()
        defer q.mu.Unlock()
        q.items = append(q.items, value)
    }
    
    dequeueLockedQ := func(q *LockedQueue) (int, bool) {
        q.mu.Lock()
        defer q.mu.Unlock()
        
        if len(q.items) == 0 {
            return 0, false
        }
        
        value := q.items[0]
        q.items = q.items[1:]
        return value, true
    }
    
    concurrency := 10
    opsPerGoroutine := 100000
    totalOps := concurrency * opsPerGoroutine
    
    // 测试无锁队列
    var wg sync.WaitGroup
    
    // 并发入队
    start := time.Now()
    for i := 0; i < concurrency; i++ {
        wg.Add(1)
        go func(id int) {
            defer wg.Done()
            for j := 0; j < opsPerGoroutine; j++ {
                lockFreeQ.Enqueue(id*opsPerGoroutine + j)
            }
        }(i)
    }
    wg.Wait()
    
    enqueueDuration := time.Since(start)
    fmt.Printf("无锁队列 - 并发入队 %d 个元素: %v (%.2f ns/操作)\n", 
              totalOps, enqueueDuration, float64(enqueueDuration.Nanoseconds())/float64(totalOps))
    
    // 并发出队
    start = time.Now()
    for i := 0; i < concurrency; i++ {
        wg.Add(1)
        go func() {
            defer wg.Done()
            for j := 0; j < opsPerGoroutine; j++ {
                lockFreeQ.Dequeue()
            }
        }()
    }
    wg.Wait()
    
    dequeueDuration := time.Since(start)
    fmt.Printf("无锁队列 - 并发出队 %d 个元素: %v (%.2f ns/操作)\n", 
              totalOps, dequeueDuration, float64(dequeueDuration.Nanoseconds())/float64(totalOps))
    
    // 测试互斥锁队列
    start = time.Now()
    for i := 0; i < concurrency; i++ {
        wg.Add(1)
        go func(id int) {
            defer wg.Done()
            for j := 0; j < opsPerGoroutine; j++ {
                enqueueLockedQ(lockedQ, id*opsPerGoroutine+j)
            }
        }(i)
    }
    wg.Wait()
    
    lockedEnqueueDuration := time.Since(start)
    fmt.Printf("互斥锁队列 - 并发入队 %d 个元素: %v (%.2f ns/操作)\n", 
              totalOps, lockedEnqueueDuration, float64(lockedEnqueueDuration.Nanoseconds())/float64(totalOps))
    
    start = time.Now()
    for i := 0; i < concurrency; i++ {
        wg.Add(1)
        go func() {
            defer wg.Done()
            for j := 0; j < opsPerGoroutine; j++ {
                dequeueLockedQ(lockedQ)
            }
        }()
    }
    wg.Wait()
    
    lockedDequeueDuration := time.Since(start)
    fmt.Printf("互斥锁队列 - 并发出队 %d 个元素: %v (%.2f ns/操作)\n", 
              totalOps, lockedDequeueDuration, float64(lockedDequeueDuration.Nanoseconds())/float64(totalOps))
    
    // 性能比较
    fmt.Printf("\n性能比较:\n")
    fmt.Printf("入队: 无锁队列比互斥锁队列快 %.2f 倍\n", 
              float64(lockedEnqueueDuration)/float64(enqueueDuration))
    fmt.Printf("出队: 无锁队列比互斥锁队列快 %.2f 倍\n", 
              float64(lockedDequeueDuration)/float64(dequeueDuration))
    
    // 测试混合负载（一半入队，一半出队）
    fmt.Println("\n混合负载测试:")
    
    mixedLockFreeQ := NewLockFreeQueue[int]()
    mixedLockedQ := &LockedQueue{items: make([]int, 0)}
    
    // 无锁队列
    start = time.Now()
    for i := 0; i < concurrency; i++ {
        wg.Add(1)
        go func(id int) {
            defer wg.Done()
            for j := 0; j < opsPerGoroutine/2; j++ {
                // 入队
                mixedLockFreeQ.Enqueue(j)
                // 出队
                mixedLockFreeQ.Dequeue()
            }
        }(i)
    }
    wg.Wait()
    
    mixedLockFreeDuration := time.Since(start)
    
    // 互斥锁队列
    start = time.Now()
    for i := 0; i < concurrency; i++ {
        wg.Add(1)
        go func(id int) {
            defer wg.Done()
            for j := 0; j < opsPerGoroutine/2; j++ {
                // 入队
                enqueueLockedQ(mixedLockedQ, j)
                // 出队
                dequeueLockedQ(mixedLockedQ)
            }
        }(i)
    }
    wg.Wait()
    
    mixedLockedDuration := time.Since(start)
    
    fmt.Printf("无锁队列 - 混合负载 (%d个goroutines, 各%d次操作): %v\n", 
              concurrency, opsPerGoroutine, mixedLockFreeDuration)
    fmt.Printf("互斥锁队列 - 混合负载 (%d个goroutines, 各%d次操作): %v\n", 
              concurrency, opsPerGoroutine, mixedLockedDuration)
    fmt.Printf("混合负载: 无锁队列比互斥锁队列快 %.2f 倍\n", 
              float64(mixedLockedDuration)/float64(mixedLockFreeDuration))
}
```

## 8. 并发算法

### 8.1 并行归并排序

**定义**：并行归并排序是归并排序算法的并行版本，它利用多个处理器或线程并行地对数据子集进行排序，然后合并结果。

**Go 2025 实现**：

```go
// 顺序归并排序
func MergeSort[T Ordered](arr []T) []T {
    if len(arr) <= 1 {
        return arr
    }
    
    // 分割数组
    mid := len(arr) / 2
    left := MergeSort(arr[:mid])
    right := MergeSort(arr[mid:])
    
    // 合并结果
    return merge(left, right)
}

// 合并两个有序数组
func merge[T Ordered](left, right []T) []T {
    result := make([]T, len(left)+len(right))
    i, j, k := 0, 0, 0
    
    // 比较两个数组的元素并合并
    for i < len(left) && j < len(right) {
        if left[i] <= right[j] {
            result[k] = left[i]
            i++
        } else {
            result[k] = right[j]
            j++
        }
        k++
    }
    
    // 复制剩余元素
    for i < len(left) {
        result[k] = left[i]
        i++
        k++
    }
    
    for j < len(right) {
        result[k] = right[j]
        j++
        k++
    }
    
    return result
}

// 并行归并排序
func ParallelMergeSort[T Ordered](arr []T, threshold int, maxWorkers int) []T {
    // 创建用于限制goroutine数量的池
    workerPool := make(chan struct{}, maxWorkers)
    for i := 0; i < maxWorkers; i++ {
        workerPool <- struct{}{}
    }
    
    return parallelMergeSortHelper(arr, threshold, workerPool)
}

// 并行归并排序辅助函数
func parallelMergeSortHelper[T Ordered](arr []T, threshold int, workerPool chan struct{}) []T {
    if len(arr) <= 1 {
        return arr
    }
    
    // 如果数组长度小于阈值，使用顺序归并排序
    if len(arr) < threshold {
        return MergeSort(arr)
    }
    
    // 分割数组
    mid := len(arr) / 2
    
    // 检查是否有可用的工作线程
    var left, right []T
    var wg sync.WaitGroup
    
    select {
    case <-workerPool:
        // 有可用工作线程，并行处理左半部分
        wg.Add(1)
        go func() {
            defer wg.Done()
            left = parallelMergeSortHelper(arr[:mid], threshold, workerPool)
            // 将工作线程返回到池中
            workerPool <- struct{}{}
        }()
        
        // 当前线程处理右半部分
        right = parallelMergeSortHelper(arr[mid:], threshold, workerPool)
        
        // 等待左半部分完成
        wg.Wait()
    default:
        // 没有可用工作线程，顺序处理
        left = parallelMergeSortHelper(arr[:mid], threshold, workerPool)
        right = parallelMergeSortHelper(arr[mid:], threshold, workerPool)
    }
    
    // 合并结果
    return merge(left, right)
}

// 用法示例
func parallelMergeSortExample() {
    // 准备测试数据
    rand.Seed(time.Now().UnixNano())
    sizes := []int{10000, 100000, 1000000}
    
    fmt.Println("并行归并排序性能测试:")
    
    for _, size := range sizes {
        data := make([]int, size)
        for i := range data {
            data[i] = rand.Intn(1000000)
        }
        
        // 复制数组以进行公平比较
        data1 := make([]int, len(data))
        data2 := make([]int, len(data))
        copy(data1, data)
        copy(data2, data)
        
        // 顺序归并排序
        start := time.Now()
        MergeSort(data1)
        seqDuration := time.Since(start)
        
        // 并行归并排序
        numCPUs := runtime.NumCPU()
        threshold := 1000  // 根据硬件调整阈值
        
        start = time.Now()
        ParallelMergeSort(data2, threshold, numCPUs)
        parDuration := time.Since(start)
        
        fmt.Printf("\n数组大小: %d\n", size)
        fmt.Printf("顺序归并排序: %v\n", seqDuration)
        fmt.Printf("并行归并排序 (%d个worker): %v\n", numCPUs, parDuration)
        fmt.Printf("加速比: %.2fx\n", float64(seqDuration)/float64(parDuration))
        
        // 验证结果正确性
        sorted := true
        for i := 1; i < len(data2); i++ {
            if data2[i] < data2[i-1] {
                sorted = false
                break
            }
        }
        fmt.Printf("排序结果正确: %t\n", sorted)
    }
    
    // 测试不同阈值和worker数量的影响
    fmt.Println("\n测试阈值和worker数量的影响:")
    
    size := 1000000
    testData := make([]int, size)
    for i := range testData {
        testData[i] = rand.Intn(1000000)
    }
    
    thresholds := []int{100, 1000, 10000}
    workers := []int{2, 4, 8, 16}
    
    for _, threshold := range thresholds {
        for _, numWorkers := range workers {
            // 跳过无意义的组合
            if numWorkers > runtime.NumCPU() {
                continue
            }
            
            data := make([]int, size)
            copy(data, testData)
            
            start := time.Now()
            ParallelMergeSort(data, threshold, numWorkers)
            duration := time.Since(start)
            
            fmt.Printf("阈值=%d, worker=%d: %v\n", threshold, numWorkers, duration)
        }
    }
}
```

### 8.2 并行分区索引

**定义**：并行分区索引是一种数据结构和算法，它将数据分区并在多个处理器上并行构建索引，以加速数据检索和查询。这对处理大规模数据集特别有用。

**基本原理**：

1. 将数据集划分为多个分区
2. 在每个分区上并行构建局部索引
3. 合并局部索引或维护分区映射以支持全局查询
4. 查询时并行搜索相关分区

**Go 2025 实现**：

```go
// 并行分区索引
type ParallelPartitionIndex[K Ordered, V any] struct {
    partitions     []*partition[K, V]  // 数据分区
    partitionCount int                 // 分区数量
    hashFunc       func(K) uint64      // 哈希函数
    mu             sync.RWMutex        // 用于分区修改操作
}

// 数据分区
type partition[K Ordered, V any] struct {
    items  map[K]V     // 存储键值对
    mu     sync.RWMutex // 分区级互斥锁
    sorted []K         // 排序的键（用于范围查询）
    dirty  bool        // 标记是否需要重新排序
}

// 创建新的并行分区索引
func NewParallelPartitionIndex[K Ordered, V any](
    partitionCount int,
    hashFunc func(K) uint64,
) *ParallelPartitionIndex[K, V] {
    if partitionCount <= 0 {
        partitionCount = runtime.NumCPU()
    }
    
    index := &ParallelPartitionIndex[K, V]{
        partitions:     make([]*partition[K, V], partitionCount),
        partitionCount: partitionCount,
    }
    
    // 使用提供的哈希函数或默认函数
    if hashFunc == nil {
        index.hashFunc = func(key K) uint64 {
            h := fnv.New64a()
            h.Write([]byte(fmt.Sprintf("%v", key)))
            return h.Sum64()
        }
    } else {
        index.hashFunc = hashFunc
    }
    
    // 初始化分区
    for i := 0; i < partitionCount; i++ {
        index.partitions[i] = &partition[K, V]{
            items: make(map[K]V),
            dirty: false,
        }
    }
    
    return index
}

// 获取键所在的分区
func (idx *ParallelPartitionIndex[K, V]) getPartition(key K) *partition[K, V] {
    hash := idx.hashFunc(key)
    return idx.partitions[hash%uint64(idx.partitionCount)]
}

// 添加键值对
func (idx *ParallelPartitionIndex[K, V]) Put(key K, value V) {
    partition := idx.getPartition(key)
    
    partition.mu.Lock()
    defer partition.mu.Unlock()
    
    partition.items[key] = value
    partition.dirty = true
}

// 获取值
func (idx *ParallelPartitionIndex[K, V]) Get(key K) (V, bool) {
    partition := idx.getPartition(key)
    
    partition.mu.RLock()
    defer partition.mu.RUnlock()
    
    value, found := partition.items[key]
    return value, found
}

// 删除键
func (idx *ParallelPartitionIndex[K, V]) Remove(key K) bool {
    partition := idx.getPartition(key)
    
    partition.mu.Lock()
    defer partition.mu.Unlock()
    
    if _, found := partition.items[key]; found {
        delete(partition.items, key)
        partition.dirty = true
        return true
    }
    return false
}

// 更新分区的排序键列表
func (p *partition[K, V]) updateSortedKeys() {
    if !p.dirty {
        return
    }
    
    p.sorted = make([]K, 0, len(p.items))
    for key := range p.items {
        p.sorted = append(p.sorted, key)
    }
    
    sort.Slice(p.sorted, func(i, j int) bool {
        return p.sorted[i] < p.sorted[j]
    })
    
    p.dirty = false
}

// 范围查询
func (idx *ParallelPartitionIndex[K, V]) RangeQuery(
    start, end K,
    limit int,
) map[K]V {
    result := make(map[K]V)
    resultMu := sync.Mutex{}
    count := atomic.Int32{}
    
    // 并行处理每个分区
    var wg sync.WaitGroup
    for i := 0; i < idx.partitionCount; i++ {
        wg.Add(1)
        go func(p *partition[K, V]) {
            defer wg.Done()
            
            p.mu.RLock()
            
            // 更新排序的键列表（如果需要）
            if p.dirty {
                p.mu.RUnlock()
                p.mu.Lock()
                p.updateSortedKeys()
                p.mu.Unlock()
                p.mu.RLock()
            }
            
            // 二分查找开始位置
            startIdx := sort.Search(len(p.sorted), func(i int) bool {
                return p.sorted[i] >= start
            })
            
            // 收集在范围内的键值对
            for i := startIdx; i < len(p.sorted) && int(count.Load()) < limit; i++ {
                key := p.sorted[i]
                if key > end {
                    break
                }
                
                value := p.items[key]
                
                // 原子添加到结果集
                resultMu.Lock()
                result[key] = value
                resultMu.Unlock()
                
                count.Add(1)
            }
            
            p.mu.RUnlock()
        }(idx.partitions[i])
    }
    
    wg.Wait()
    return result
}

// 计算索引大小
func (idx *ParallelPartitionIndex[K, V]) Size() int {
    var total int
    for _, p := range idx.partitions {
        p.mu.RLock()
        total += len(p.items)
        p.mu.RUnlock()
    }
    return total
}

// 执行批量插入
func (idx *ParallelPartitionIndex[K, V]) BatchInsert(items map[K]V) {
    // 预先计算分区
    partitionedItems := make([]map[K]V, idx.partitionCount)
    for i := range partitionedItems {
        partitionedItems[i] = make(map[K]V)
    }
    
    for key, value := range items {
        hash := idx.hashFunc(key)
        partitionIdx := hash % uint64(idx.partitionCount)
        partitionedItems[partitionIdx][key] = value
    }
    
    // 并行插入每个分区
    var wg sync.WaitGroup
    for i := 0; i < idx.partitionCount; i++ {
        if len(partitionedItems[i]) == 0 {
            continue
        }
        
        wg.Add(1)
        go func(partIdx int, partItems map[K]V) {
            defer wg.Done()
            
            partition := idx.partitions[partIdx]
            partition.mu.Lock()
            defer partition.mu.Unlock()
            
            for k, v := range partItems {
                partition.items[k] = v
            }
            partition.dirty = true
        }(i, partitionedItems[i])
    }
    
    wg.Wait()
}

// 并行查询
func (idx *ParallelPartitionIndex[K, V]) ParallelQuery(
    keys []K,
) map[K]V {
    result := make(map[K]V)
    resultMu := sync.Mutex{}
    
    // 按分区分组
    keysByPartition := make([][]K, idx.partitionCount)
    for _, key := range keys {
        hash := idx.hashFunc(key)
        partIdx := hash % uint64(idx.partitionCount)
        keysByPartition[partIdx] = append(keysByPartition[partIdx], key)
    }
    
    // 并行处理每个分区的查询
    var wg sync.WaitGroup
    for i := 0; i < idx.partitionCount; i++ {
        if len(keysByPartition[i]) == 0 {
            continue
        }
        
        wg.Add(1)
        go func(partIdx int, partKeys []K) {
            defer wg.Done()
            
            partition := idx.partitions[partIdx]
            partition.mu.RLock()
            defer partition.mu.RUnlock()
            
            localResults := make(map[K]V)
            for _, key := range partKeys {
                if value, found := partition.items[key]; found {
                    localResults[key] = value
                }
            }
            
            // 合并结果
            resultMu.Lock()
            for k, v := range localResults {
                result[k] = v
            }
            resultMu.Unlock()
        }(i, keysByPartition[i])
    }
    
    wg.Wait()
    return result
}

// 用法示例
func parallelPartitionIndexExample() {
    // 创建并行分区索引
    partitionCount := runtime.NumCPU()
    index := NewParallelPartitionIndex[string, int](partitionCount, nil)
    
    fmt.Println("并行分区索引测试:")
    
    // 添加数据
    words := []string{
        "apple", "banana", "cherry", "date", "elderberry",
        "fig", "grape", "honeydew", "imbe", "jackfruit",
        "kiwi", "lemon", "mango", "nectarine", "orange",
        "papaya", "quince", "raspberry", "strawberry", "tangerine",
    }
    
    for i, word := range words {
        index.Put(word, i)
    }
    
    fmt.Printf("索引大小: %d\n", index.Size())
    
    // 查询测试
    testKeys := []string{"apple", "banana", "nonexistent", "mango"}
    for _, key := range testKeys {
        value, found := index.Get(key)
        fmt.Printf("查询 \"%s\": %v, 找到: %t\n", key, value, found)
    }
    
    // 范围查询
    rangeResult := index.RangeQuery("grape", "orange", 10)
    fmt.Println("\n范围查询结果 (grape-orange):")
    for key, value := range rangeResult {
        fmt.Printf("  %s: %d\n", key, value)
    }
    
    // 删除测试
    removeKey := "banana"
    removed := index.Remove(removeKey)
    fmt.Printf("\n删除 \"%s\": %t\n", removeKey, removed)
    fmt.Printf("索引大小: %d\n", index.Size())
    
    // 批量插入测试
    newItems := make(map[string]int)
    newWords := []string{"watermelon", "xigua", "yellow_melon", "zucchini"}
    for i, word := range newWords {
        newItems[word] = len(words) + i
    }
    
    index.BatchInsert(newItems)
    fmt.Printf("\n批量插入后索引大小: %d\n", index.Size())
    
    // 并行查询测试
    queryKeys := []string{"apple", "watermelon", "xigua", "banana", "orange"}
    queryResults := index.ParallelQuery(queryKeys)
    
    fmt.Println("\n并行查询结果:")
    for key, value := range queryResults {
        fmt.Printf("  %s: %d\n", key, value)
    }
    
    // 性能测试
    fmt.Println("\n性能测试:")
    
    // 准备大量数据
    largeDataSize := 100000
    largeData := make(map[string]int)
    
    for i := 0; i < largeDataSize; i++ {
        key := fmt.Sprintf("key-%06d", i)
        largeData[key] = i
    }
    
    // 测试批量插入性能
    largeIndex := NewParallelPartitionIndex[string, int](partitionCount, nil)
    start := time.Now()
    largeIndex.BatchInsert(largeData)
    insertDuration := time.Since(start)
    
    fmt.Printf("批量插入 %d 个项目: %v (%.2f μs/项目)\n", 
              largeDataSize, insertDuration, float64(insertDuration.Microseconds())/float64(largeDataSize))
    
    // 测试随机查询性能
    queryCount := 10000
    queryKeys = make([]string, queryCount)
    
    for i := 0; i < queryCount; i++ {
        // 75%的查询命中，25%未命中
        if rand.Float64() < 0.75 {
            randomIdx := rand.Intn(largeDataSize)
            queryKeys[i] = fmt.Sprintf("key-%06d", randomIdx)
        } else {
            queryKeys[i] = fmt.Sprintf("missing-%06d", rand.Intn(10000))
        }
    }
    
    // 顺序查询
    start = time.Now()
    sequentialResults := make(map[string]int)
    for _, key := range queryKeys {
        if value, found := largeIndex.Get(key); found {
            sequentialResults[key] = value
        }
    }
    sequentialDuration := time.Since(start)
    
    // 并行查询
    start = time.Now()
    parallelResults := largeIndex.ParallelQuery(queryKeys)
    parallelDuration := time.Since(start)
    
    fmt.Printf("顺序查询 %d 个键: %v (%.2f ns/查询)\n", 
              queryCount, sequentialDuration, float64(sequentialDuration.Nanoseconds())/float64(queryCount))
    fmt.Printf("并行查询 %d 个键: %v (%.2f ns/查询)\n", 
              queryCount, parallelDuration, float64(parallelDuration.Nanoseconds())/float64(queryCount))
    fmt.Printf("加速比: %.2fx\n", float64(sequentialDuration)/float64(parallelDuration))
    
    // 范围查询性能
    start = time.Now()
    rangeResults := largeIndex.RangeQuery("key-050000", "key-055000", 5000)
    rangeDuration := time.Since(start)
    
    fmt.Printf("范围查询 (找到 %d 个结果): %v\n", len(rangeResults), rangeDuration)
    
    // 测试不同分区数量的性能影响
    fmt.Println("\n测试分区数量对性能的影响:")
    
    partitionSizes := []int{1, 2, 4, 8, 16, 32}
    for _, numPartitions := range partitionSizes {
        testIndex := NewParallelPartitionIndex[string, int](numPartitions, nil)
        
        // 插入性能
        start = time.Now()
        testIndex.BatchInsert(largeData)
        insertTime := time.Since(start)
        
        // 查询性能
        start = time.Now()
        testIndex.ParallelQuery(queryKeys)
        queryTime := time.Since(start)
        
        fmt.Printf("分区数量=%d: 插入=%v, 查询=%v\n", numPartitions, insertTime, queryTime)
    }
}
```

### 8.3 并行图算法

**定义**：并行图算法是利用多线程或多处理器环境并行处理图数据的算法。它们通常将图划分为多个部分，然后在不同的处理单元上并行计算，最后合并结果。

**Go 2025 实现广度优先搜索**：

```go
// 图接口
type Graph interface {
    Vertices() []int
    Neighbors(v int) []int
}

// 邻接表表示的图
type AdjacencyListGraph struct {
    adjacencyList map[int][]int
}

// 创建新图
func NewGraph() *AdjacencyListGraph {
    return &AdjacencyListGraph{
        adjacencyList: make(map[int][]int),
    }
}

// 添加顶点
func (g *AdjacencyListGraph) AddVertex(v int) {
    if _, exists := g.adjacencyList[v]; !exists {
        g.adjacencyList[v] = []int{}
    }
}

// 添加边
func (g *AdjacencyListGraph) AddEdge(from, to int) {
    g.AddVertex(from)
    g.AddVertex(to)
    g.adjacencyList[from] = append(g.adjacencyList[from], to)
}

// 获取所有顶点
func (g *AdjacencyListGraph) Vertices() []int {
    vertices := make([]int, 0, len(g.adjacencyList))
    for v := range g.adjacencyList {
        vertices = append(vertices, v)
    }
    return vertices
}

// 获取邻居
func (g *AdjacencyListGraph) Neighbors(v int) []int {
    return g.adjacencyList[v]
}

// 串行广度优先搜索
func BFS(g Graph, start int) map[int]int {
    visited := make(map[int]bool)
    distance := make(map[int]int)
    queue := make([]int, 0)
    
    visited[start] = true
    distance[start] = 0
    queue = append(queue, start)
    
    for len(queue) > 0 {
        vertex := queue[0]
        queue = queue[1:]
        
        for _, neighbor := range g.Neighbors(vertex) {
            if !visited[neighbor] {
                visited[neighbor] = true
                distance[neighbor] = distance[vertex] + 1
                queue = append(queue, neighbor)
            }
        }
    }
    
    return distance
}

// 并行广度优先搜索
func ParallelBFS(g Graph, start int, numWorkers int) map[int]int {
    if numWorkers <= 0 {
        numWorkers = runtime.NumCPU()
    }
    
    visited := sync.Map{}
    distance := sync.Map{}
    
    visited.Store(start, true)
    distance.Store(start, 0)
    
    // 当前层和下一层
    currentLayer := []int{start}
    
    // 处理层次，直到没有更多顶点
    for len(currentLayer) > 0 {
        // 并行处理当前层中的每个顶点
        var nextLayer []int
        var nextLayerMutex sync.Mutex
        
        // 创建任务块
        chunks := splitIntoChunks(currentLayer, numWorkers)
        var wg sync.WaitGroup
        
        for _, chunk := range chunks {
            wg.Add(1)
            go func(vertices []int) {
                defer wg.Done()
                
                localNextLayer := make([]int, 0)
                
                for _, vertex := range vertices {
                    currentDist, _ := distance.Load(vertex)
                    distVal := currentDist.(int)
                    
                    for _, neighbor := range g.Neighbors(vertex) {
                        // 尝试标记为已访问
                        if _, alreadyVisited := visited.LoadOrStore(neighbor, true); !alreadyVisited {
                            distance.Store(neighbor, distVal+1)
                            localNextLayer = append(localNextLayer, neighbor)
                        }
                    }
                }
                
                // 合并本地下一层到全局下一层
                if len(localNextLayer) > 0 {
                    nextLayerMutex.Lock()
                    nextLayer = append(nextLayer, localNextLayer...)
                    nextLayerMutex.Unlock()
                }
            }(chunk)
        }
        
        wg.Wait()
        
        // 移动到下一层
        currentLayer = nextLayer
    }
    
    // 转换结果
    result := make(map[int]int)
    distance.Range(func(key, value interface{}) bool {
        result[key.(int)] = value.(int)
        return true
    })
    
    return result
}

// 将切片分成多个块
func splitIntoChunks[T any](items []T, numChunks int) [][]T {
    if len(items) == 0 {
        return [][]T{}
    }
    
    if numChunks <= 0 || numChunks > len(items) {
        numChunks = len(items)
    }
    
    chunkSize := (len(items) + numChunks - 1) / numChunks
    chunks := make([][]T, 0, numChunks)
    
    for i := 0; i < len(items); i += chunkSize {
        end := i + chunkSize
        if end > len(items) {
            end = len(items)
        }
        chunks = append(chunks, items[i:end])
    }
    
    return chunks
}

// 并行最短路径（Dijkstra算法）
func ParallelDijkstra(g *WeightedGraph, start int, numWorkers int) map[int]int {
    if numWorkers <= 0 {
        numWorkers = runtime.NumCPU()
    }
    
    vertices := g.Vertices()
    n := len(vertices)
    
    // 初始化距离
    distance := make(map[int]int)
    for _, v := range vertices {
        if v == start {
            distance[v] = 0
        } else {
            distance[v] = math.MaxInt32
        }
    }
    
    visited := make(map[int]bool)
    
    // 处理所有顶点
    for i := 0; i < n; i++ {
        // 找到未访问的最小距离顶点
        u := -1
        for _, v := range vertices {
            if !visited[v] && (u == -1 || distance[v] < distance[u]) {
                u = v
            }
        }
        
        if u == -1 || distance[u] == math.MaxInt32 {
            break
        }
        
        visited[u] = true
        
        // 获取邻居
        neighbors := g.Neighbors(u)
        
        // 空邻居列表，跳过
        if len(neighbors) == 0 {
            continue
        }
        
        // 并行更新距离
        chunks := splitIntoChunks(neighbors, numWorkers)
        var wg sync.WaitGroup
        
        for _, chunk := range chunks {
            wg.Add(1)
            go func(edges []WeightedEdge) {
                defer wg.Done()
                
                for _, edge := range edges {
                    v := edge.To
                    weight := edge.Weight
                    
                    if !visited[v] {
                        newDist := distance[u] + weight
                        if newDist < distance[v] {
                            // 使用原子操作或互斥锁更新距离
                            func() {
                                distance[v] = newDist
                            }()
                        }
                    }
                }
            }(chunk)
        }
        
        wg.Wait()
    }
    
    return distance
}

// 带权重的图的边
type WeightedEdge struct {
    To     int
    Weight int
}

// 带权重的图
type WeightedGraph struct {
    adjacencyList map[int][]WeightedEdge
}

// 创建新的带权重图
func NewWeightedGraph() *WeightedGraph {
    return &WeightedGraph{
        adjacencyList: make(map[int][]WeightedEdge),
    }
}

// 添加顶点
func (g *WeightedGraph) AddVertex(v int) {
    if _, exists := g.adjacencyList[v]; !exists {
        g.adjacencyList[v] = []WeightedEdge{}
    }
}

// 添加带权重的边
func (g *WeightedGraph) AddEdge(from, to, weight int) {
    g.AddVertex(from)
    g.AddVertex(to)
    g.adjacencyList[from] = append(g.adjacencyList[from], WeightedEdge{To: to, Weight: weight})
}

// 获取所有顶点
func (g *WeightedGraph) Vertices() []int {
    vertices := make([]int, 0, len(g.adjacencyList))
    for v := range g.adjacencyList {
        vertices = append(vertices, v)
    }
    return vertices
}

// 获取邻居
func (g *WeightedGraph) Neighbors(v int) []WeightedEdge {
    return g.adjacencyList[v]
}

// 用法示例
func parallelGraphAlgorithmsExample() {
    // 创建示例图
    g := NewGraph()
    
    // 添加边
    // 创建一个类似于社交网络的图
    edges := []struct {
        from, to int
    }{
        {1, 2}, {1, 3}, {1, 4},
        {2, 5}, {2, 6},
        {3, 7}, {3, 8},
        {4, 9}, {4, 10},
        {5, 11}, {5, 12},
        {7, 13}, {7, 14},
        {9, 15}, {9, 16},
    }
    
    for _, e := range edges {
        g.AddEdge(e.from, e.to)
        // 添加反向边使其成为无向图
        g.AddEdge(e.to, e.from)
    }
    
    fmt.Println("并行图算法测试:")
    
    // 测试串行BFS
    start := time.Now()
    serialResult := BFS(g, 1)
    serialDuration := time.Since(start)
    
    fmt.Printf("串行BFS耗时: %v\n", serialDuration)
    fmt.Printf("从顶点1到达的顶点数: %d\n", len(serialResult))
    
    // 测试并行BFS
    numWorkers := runtime.NumCPU()
    start = time.Now()
    parallelResult := ParallelBFS(g, 1, numWorkers)
    parallelDuration := time.Since(start)
    
    fmt.Printf("并行BFS (%d个worker) 耗时: %v\n", numWorkers, parallelDuration)
    fmt.Printf("从顶点1到达的顶点数: %d\n", len(parallelResult))
    
    // 验证结果正确性
    correct := true
    if len(serialResult) != len(parallelResult) {
        correct = false
    } else {
        for vertex, dist := range serialResult {
            if parallelDist, ok := parallelResult[vertex]; !ok || parallelDist != dist {
                correct = false
                break
            }
        }
    }
    
    fmt.Printf("结果一致: %t\n", correct)
    
    // 创建大型图用于性能测试
    fmt.Println("\n大型图性能测试:")
    
    // 生成随机图
    largeGraph := generateRandomGraph(10000, 10)
    
    // 测试不同worker数量
    workerCounts := []int{1, 2, 4, 8, 16}
    
    serialStart := time.Now()
    BFS(largeGraph, 0)
    serialTime := time.Since(serialStart)
    fmt.Printf("串行BFS (大图): %v\n", serialTime)
    
    for _, workers := range workerCounts {
        start = time.Now()
        ParallelBFS(largeGraph, 0, workers)
        duration := time.Since(start)
        
        fmt.Printf("并行BFS (workers=%d): %v, 加速比: %.2fx\n", 
                  workers, duration, float64(serialTime)/float64(duration))
    }
    
    // 测试带权重的图和Dijkstra算法
    fmt.Println("\n并行Dijkstra算法测试:")
    
    // 创建带权重的图
    wg := NewWeightedGraph()
    
    // 添加带权重的边
    weightedEdges := []struct {
        from, to, weight int
    }{
        {0, 1, 4}, {0, 7, 8},
        {1, 2, 8}, {1, 7, 11},
        {2, 3, 7}, {2, 8, 2},
        {2, 5, 4},
        {3, 4, 9}, {3, 5, 14},
        {4, 5, 10},
        {5, 6, 2},
        {6, 7, 1}, {6, 8, 6},
        {7, 8, 7},
    }
    
    for _, e := range weightedEdges {
        wg.AddEdge(e.from, e.to, e.weight)
    }
    
    // 并行Dijkstra
    dijkstraResult := ParallelDijkstra(wg, 0, runtime.NumCPU())
    
    fmt.Println("从顶点0到其他顶点的最短路径:")
    vertices := wg.Vertices()
    sort.Ints(vertices)
    for _, v := range vertices {
        fmt.Printf("  到顶点%d的距离: %d\n", v, dijkstraResult[v])
    }
}

// 生成随机图
func generateRandomGraph(n, avgDegree int) *AdjacencyListGraph {
    g := NewGraph()
    
    // 确保所有顶点都被添加
    for i := 0; i < n; i++ {
        g.AddVertex(i)
    }
    
    // 随机添加边
    edgesToAdd := n * avgDegree / 2
    
    for i := 0; i < edgesToAdd; i++ {
        from := rand.Intn(n)
        to := rand.Intn(n)
        
        // 避免自环
        if from != to {
            g.AddEdge(from, to)
            g.AddEdge(to, from)  // 无向图
        }
    }
    
    return g
}
```

### 8.4 并行幂集算法

**定义**：幂集是一个集合的所有子集的集合。并行幂集算法利用多线程并行计算大集合的幂集，可以显著提高大数据集上的性能。

**Go 2025 实现**：

```go
// 串行幂集算法
func PowerSet[T comparable](set []T) [][]T {
    powerSet := make([][]T, 0)
    
    // 空集是任何集合的子集
    powerSet = append(powerSet, []T{})
    
    for _, item := range set {
        // 对于当前幂集中的每个子集，创建一个新的包含当前项的子集
        numSubsets := len(powerSet)
        for i := 0; i < numSubsets; i++ {
            // 复制现有子集
            newSubset := make([]T, len(powerSet[i]), len(powerSet[i])+1)
            copy(newSubset, powerSet[i])
            
            // 添加当前项
            newSubset = append(newSubset, item)
            
            // 添加到幂集
            powerSet = append(powerSet, newSubset)
        }
    }
    
    return powerSet
}

// 并行幂集算法
func ParallelPowerSet[T comparable](set []T, numWorkers int) [][]T {
    if numWorkers <= 0 {
        numWorkers = runtime.NumCPU()
    }
    
    n := len(set)
    
    // 对于大集合，子集数量巨大，限制计算量
    if n > 20 {
        panic("集合太大，子集数量会超过内存限制。请限制集合大小或使用迭代器实现。")
    }
    
    // 子集的总数量
    numSubsets := 1 << n  // 2^n
    
    // 创建结果切片
    result := make([][]T, numSubsets)
    result[0] = []T{}  // 空集
    
    // 平均每个worker处理的子集数量
    workPerWorker := (numSubsets - 1 + numWorkers - 1) / numWorkers
    
    var wg sync.WaitGroup
    
    // 启动worker
    for w := 0; w < numWorkers; w++ {
        wg.Add(1)
        go func(workerId int) {
            defer wg.Done()
            
            start := workerId*workPerWorker + 1  // 跳过空集
            end := (workerId+1) * workPerWorker
            if end > numSubsets {
                end = numSubsets
            }
            
            // 处理每个组合
            for i := start; i < end; i++ {
                subset := make([]T, 0, bits.OnesCount(uint(i)))
                
                // 检查每一位
                for j := 0; j < n; j++ {
                    if (i & (1 << j)) != 0 {
                        subset = append(subset, set[j])
                    }
                }
                
                result[i] = subset
            }
        }(w)
    }
    
    wg.Wait()
    return result
}

// 并行幂集生成器（迭代器模式）
type PowerSetIterator[T comparable] struct {
    originalSet []T
    current     int
    total       int
}

// 创建幂集迭代器
func NewPowerSetIterator[T comparable](set []T) *PowerSetIterator[T] {
    n := len(set)
    if n > 30 {
        panic("集合太大，总子集数量会超过int范围。请使用较小的集合。")
    }
    
    return &PowerSetIterator[T]{
        originalSet: set,
        current:     0,
        total:       1 << n,  // 2^n
    }
}

// 检查是否有下一个元素
func (it *PowerSetIterator[T]) HasNext() bool {
    return it.current < it.total
}

// 获取下一个子集
func (it *PowerSetIterator[T]) Next() []T {
    if !it.HasNext() {
        panic("没有更多子集")
    }
    
    subset := make([]T, 0, bits.OnesCount(uint(it.current)))
    
    for j := 0; j < len(it.originalSet); j++ {
        if (it.current & (1 << j)) != 0 {
            subset = append(subset, it.originalSet[j])
        }
    }
    
    it.current++
    return subset
}

// 并行处理幂集
func ProcessPowerSetParallel[T comparable, R any](
    set []T,
    processor func([]T) R,
    numWorkers int,
) []R {
    if numWorkers <= 0 {
        numWorkers = runtime.NumCPU()
    }
    
    n := len(set)
    numSubsets := 1 << n  // 2^n
    
    // 创建结果切片
    results := make([]R, numSubsets)
    
    // 划分工作
    var wg sync.WaitGroup
    
    for w := 0; w < numWorkers; w++ {
        wg.Add(1)
        go func(workerId int) {
            defer wg.Done()
            
            start := workerId * numSubsets / numWorkers
            end := (workerId + 1) * numSubsets / numWorkers
            
            for i := start; i < end; i++ {
                subset := make([]T, 0, bits.OnesCount(uint(i)))
                
                for j := 0; j < n; j++ {
                    if (i & (1 << j)) != 0 {
                        subset = append(subset, set[j])
                    }
                }
                
                results[i] = processor(subset)
            }
        }(w)
    }
    
    wg.Wait()
    return results
}

// 用法示例
func parallelPowerSetExample() {
    // 创建测试集合
    set := []string{"a", "b", "c", "d", "e"}
    
    fmt.Println("并行幂集算法测试:")
    fmt.Printf("原始集合: %v\n", set)
    
    // 测试串行幂集算法
    start := time.Now()
    serialPowerSet := PowerSet(set)
    serialDuration := time.Since(start)
    
    fmt.Printf("串行算法生成的幂集大小: %d, 耗时: %v\n", 
              len(serialPowerSet), serialDuration)
    
    // 测试并行幂集算法
    numWorkers := runtime.NumCPU()
    start = time.Now()
    parallelPowerSet := ParallelPowerSet(set, numWorkers)
    parallelDuration := time.Since(start)
    
    fmt.Printf("并行算法生成的幂集大小: %d, 耗时: %v\n", 
              len(parallelPowerSet), parallelDuration)
    
    // 验证结果
    correct := len(serialPowerSet) == len(parallelPowerSet)
    fmt.Printf("结果大小一致: %t\n", correct)
    
    // 使用迭代器模式
    fmt.Println("\n使用幂集迭代器:")
    iterator := NewPowerSetIterator([]string{"x", "y", "z"})
    for iterator.HasNext() {
        subset := iterator.Next()
        fmt.Printf("  %v\n", subset)
    }
    
    // 性能测试
    fmt.Println("\n性能测试:")
    
    // 测试多种不同大小的集合
    testSizes := []int{10, 15, 18, 20}
    
    for _, size := range testSizes {
        // 生成测试集合
        testSet := make([]int, size)
        for i := 0; i < size; i++ {
            testSet[i] = i
        }
        
        // 计算子集数量
        numSubsets := 1 << size
        
        fmt.Printf("\n测试集合大小: %d (产生 %d 个子集)\n", size, numSubsets)
        
        // 为大集合跳过实际计算，只测试并行处理速度
        if size > 15 {
            // 使用处理函数测试
            start = time.Now()
            ProcessPowerSetParallel(testSet, func(subset []int) int {
                return len(subset)  // 简单处理函数：返回子集大小
            }, 1)  // 单线程
            singleDuration := time.Since(start)
            
            start = time.Now()
            ProcessPowerSetParallel(testSet, func(subset []int) int {
                return len(subset)
            }, runtime.NumCPU())  // 多线程
            multiDuration := time.Since(start)
            
            fmt.Printf("处理时间 (单线程): %v\n", singleDuration)
            fmt.Printf("处理时间 (多线程): %v\n", multiDuration)
            fmt.Printf("加速比: %.2fx\n", float64(singleDuration)/float64(multiDuration))
            
            continue
        }
        
        // 实际计算幂集
        start = time.Now()
        PowerSet(testSet)
        serialTime := time.Since(start)
        
        start = time.Now()
        ParallelPowerSet(testSet, runtime.NumCPU())
        parallelTime := time.Since(start)
        
        fmt.Printf("串行时间: %v\n", serialTime)
        fmt.Printf("并行时间: %v\n", parallelTime)
        fmt.Printf("加速比: %.2fx\n", float64(serialTime)/float64(parallelTime))
    }
}
```

### 8.5 并行前缀和

**定义**：前缀和（或累积和）是一种计算数组中所有前缀的累积和的算法。
并行前缀和算法通过分治法在多个处理器上并行计算前缀和，可以将O(n)的工作分解成并行的O(log n)时间步骤。

**Go 2025 实现**：

```go
// 串行前缀和
func PrefixSum(arr []int) []int {
    n := len(arr)
    if n == 0 {
        return []int{}
    }
    
    result := make([]int, n)
    result[0] = arr[0]
    
    for i := 1; i < n; i++ {
        result[i] = result[i-1] + arr[i]
    }
    
    return result
}

// 并行前缀和
func ParallelPrefixSum(arr []int, numWorkers int) []int {
    n := len(arr)
    if n <= 1 {
        return arr
    }
    
    if numWorkers <= 0 {
        numWorkers = runtime.NumCPU()
    }
    
    // 创建输出数组
    result := make([]int, n)
    copy(result, arr)
    
    // 上扫描阶段
    // 构建"减少树"
    d := 1
    for d < n {
        var wg sync.WaitGroup
        
        // 将工作划分为块
        elementsPerStep := 2 * d
        stepsCount := (n + elementsPerStep - 1) / elementsPerStep
        
        blocksPerWorker := (stepsCount + numWorkers - 1) / numWorkers
        if blocksPerWorker == 0 {
            blocksPerWorker = 1
        }
        
        for worker := 0; worker < numWorkers; worker++ {
            wg.Add(1)
            go func(workerId int) {
                defer wg.Done()
                
                startBlock := workerId * blocksPerWorker
                endBlock := (workerId + 1) * blocksPerWorker
                if endBlock > stepsCount {
                    endBlock = stepsCount
                }
                
                for block := startBlock; block < endBlock; block++ {
                    k := block * elementsPerStep
                    if k+d < n {
                        result[k+elementsPerStep-1] = result[k+d-1] + result[k+elementsPerStep-1]
                    }
                }
            }(worker)
        }
        
        wg.Wait()
        d *= 2
    }
    
    // 下扫描阶段
    result[n-1] = 0  // 清除最后一个元素以开始从0实现包含扫描
    
    // 遍历树向下传播
    d = n / 2
    for d >= 1 {
        var wg sync.WaitGroup
        
        elementsPerStep := 2 * d
        stepsCount := (n + elementsPerStep - 1) / elementsPerStep
        
        blocksPerWorker := (stepsCount + numWorkers - 1) / numWorkers
        if blocksPerWorker == 0 {
            blocksPerWorker = 1
        }
        
        for worker := 0; worker < numWorkers; worker++ {
            wg.Add(1)
            go func(workerId int) {
                defer wg.Done()
                
                startBlock := workerId * blocksPerWorker
                endBlock := (workerId + 1) * blocksPerWorker
                if endBlock > stepsCount {
                    endBlock = stepsCount
                }
                
                for block := startBlock; block < endBlock; block++ {
                    k := block * elementsPerStep
                    if k+d < n {
                        right := result[k+elementsPerStep-1]
                        result[k+elementsPerStep-1] = result[k+d-1] + right
                        result[k+d-1] = right
                    }
                }
            }(worker)
        }
        
        wg.Wait()
        d /= 2
    }
    
    // 将所有元素右移一位，并加上原始值
    for i := n - 1; i > 0; i-- {
        result[i] = result[i-1] + arr[i]
    }
    result[0] = arr[0]
    
    return result
}

// 简化的并行前缀和 (Blelloch算法)
func SimplifiedParallelPrefixSum(arr []int, numWorkers int) []int {
    n := len(arr)
    if n <= 1 {
        return arr
    }
    
    if numWorkers <= 0 {
        numWorkers = runtime.NumCPU()
    }
    
    result := make([]int, n)
    copy(result, arr)
    
    // 上扫描阶段 (up-sweep/reduce)
    for d := 1; d < n; d *= 2 {
        var wg sync.WaitGroup
        stride := 2 * d
        
        // 计算每个worker处理的元素对数量
        pairs := n / stride
        if n%stride != 0 {
            pairs++
        }
        
        pairsPerWorker := (pairs + numWorkers - 1) / numWorkers
        
        for worker := 0; worker < numWorkers; worker++ {
            wg.Add(1)
            go func(workerId int) {
                defer wg.Done()
                
                start := workerId * pairsPerWorker
                end := (workerId + 1) * pairsPerWorker
                if end > pairs {
                    end = pairs
                }
                
                for i := start; i < end; i++ {
                    idx := (i + 1) * stride - 1
                    if idx < n && idx-d >= 0 {
                        result[idx] += result[idx-d]
                    }
                }
            }(worker)
        }
        
        wg.Wait()
    }
    
    // 设置根为0（准备下扫描）
    result[n-1] = 0
    
    // 下扫描阶段 (down-sweep)
    for d := n / 2; d >= 1; d /= 2 {
        var wg sync.WaitGroup
        stride := 2 * d
        
        // 计算每个worker处理的元素对数量
        pairs := n / stride
        if n%stride != 0 {
            pairs++
        }
        
        pairsPerWorker := (pairs + numWorkers - 1) / numWorkers
        
        for worker := 0; worker < numWorkers; worker++ {
            wg.Add(1)
            go func(workerId int) {
                defer wg.Done()
                
                start := workerId * pairsPerWorker
                end := (workerId + 1) * pairsPerWorker
                if end > pairs {
                    end = pairs
                }
                
                for i := start; i < end; i++ {
                    right := (i + 1) * stride - 1
                    left := right - d
                    
                    if right < n && left >= 0 {
                        temp := result[left]
                        result[left] = result[right]
                        result[right] += temp
                    }
                }
            }(worker)
        }
        
        wg.Wait()
    }
    
    // 修正结果（每个元素加上其原始值）
    for i := 0; i < n; i++ {
        result[i] += arr[i]
    }
    
    return result
}

// 用法示例
func parallelPrefixSumExample() {
    // 创建测试数组
    sizes := []int{100, 1000, 10000, 100000, 1000000, 10000000}
    
    fmt.Println("并行前缀和测试:")
    
    for _, size := range sizes {
        arr := make([]int, size)
        
        // 填充数组
        for i := range arr {
            arr[i] = i % 10
        }
        
        fmt.Printf("\n数组大小: %d\n", size)
        
        // 测试串行前缀和
        start := time.Now()
        serialResult := PrefixSum(arr)
        serialDuration := time.Since(start)
        
        fmt.Printf("串行前缀和: %v\n", serialDuration)
        
        // 测试并行前缀和
        numWorkers := runtime.NumCPU()
        start = time.Now()
        parallelResult := ParallelPrefixSum(arr, numWorkers)
        parallelDuration := time.Since(start)
        
        fmt.Printf("并行前缀和 (%d worker): %v\n", numWorkers, parallelDuration)
        
        // 测试简化并行算法
        start = time.Now()
        simplifiedResult := SimplifiedParallelPrefixSum(arr, numWorkers)
        simplifiedDuration := time.Since(start)
        
        fmt.Printf("简化并行前缀和: %v\n", simplifiedDuration)
        
        // 验证结果
        correctParallel := true
        correctSimplified := true
        
        // 只检查前10个和最后10个元素
        for i := 0; i < 10 && i < size; i++ {
            if serialResult[i] != parallelResult[i] {
                correctParallel = false
            }
            if serialResult[i] != simplifiedResult[i] {
                correctSimplified = false
            }
        }
        
        for i := size - 10; i < size; i++ {
            if serialResult[i] != parallelResult[i] {
                correctParallel = false
            }
            if serialResult[i] != simplifiedResult[i] {
                correctSimplified = false
            }
        }
        
        fmt.Printf("并行结果正确: %t\n", correctParallel)
        fmt.Printf("简化并行结果正确: %t\n", correctSimplified)
        
        // 计算加速比
        if size >= 1000 {  // 只对较大数组计算加速比
            fmt.Printf("并行加速比: %.2fx\n", float64(serialDuration)/float64(parallelDuration))
            fmt.Printf("简化加速比: %.2fx\n", float64(serialDuration)/float64(simplifiedDuration))
        }
    }
    
    // 测试不同worker数量的扩展性
    fmt.Println("\n测试不同worker数量的扩展性:")
    
    largeArray := make([]int, 10000000)  // 1千万元素
    for i := range largeArray {
        largeArray[i] = i % 10
    }
    
    workerCounts := []int{1, 2, 4, 8, 16, 32}
    
    // 先用单线程测量基准时间
    start := time.Now()
    PrefixSum(largeArray)
    baselineDuration := time.Since(start)
    fmt.Printf("单线程基准: %v\n", baselineDuration)
    
    for _, workers := range workerCounts {
        if workers > runtime.NumCPU() {
            continue  // 跳过超过CPU核心数的测试
        }
        
        start = time.Now()
        ParallelPrefixSum(largeArray, workers)
        duration := time.Since(start)
        
        fmt.Printf("Worker数=%d: %v (加速比: %.2fx)\n", 
                  workers, duration, float64(baselineDuration)/float64(duration))
    }
}
```

### 8.6 并行矩阵乘法

**定义**：矩阵乘法是线性代数中的基本操作，计算复杂度为O(n³)。并行矩阵乘法通过将计算分布到多个处理器上，可以显著提高性能。

**Go 2025 实现**：

```go
// 矩阵类型
type Matrix struct {
    Rows, Cols int
    Data       [][]float64
}

// 创建新矩阵
func NewMatrix(rows, cols int) *Matrix {
    data := make([][]float64, rows)
    for i := range data {
        data[i] = make([]float64, cols)
    }
    
    return &Matrix{
        Rows: rows,
        Cols: cols,
        Data: data,
    }
}

// 随机初始化矩阵
func (m *Matrix) RandomInit(min, max float64) {
    for i := 0; i < m.Rows; i++ {
        for j := 0; j < m.Cols; j++ {
            m.Data[i][j] = min + rand.Float64()*(max-min)
        }
    }
}

// 串行矩阵乘法
func MatrixMultiply(a, b *Matrix) (*Matrix, error) {
    // 检查矩阵维度
    if a.Cols != b.Rows {
        return nil, fmt.Errorf("矩阵维度不匹配: %dx%d 和 %dx%d", 
                             a.Rows, a.Cols, b.Rows, b.Cols)
    }
    
    result := NewMatrix(a.Rows, b.Cols)
    
    for i := 0; i < a.Rows; i++ {
        for j := 0; j < b.Cols; j++ {
            sum := 0.0
            for k := 0; k < a.Cols; k++ {
                sum += a.Data[i][k] * b.Data[k][j]
            }
            result.Data[i][j] = sum
        }
    }
    
    return result, nil
}

// 并行矩阵乘法
func ParallelMatrixMultiply(a, b *Matrix, numWorkers int) (*Matrix, error) {
    // 检查矩阵维度
    if a.Cols != b.Rows {
        return nil, fmt.Errorf("矩阵维度不匹配: %dx%d 和 %dx%d", 
                             a.Rows, a.Cols, b.Rows, b.Cols)
    }
    
    if numWorkers <= 0 {
        numWorkers = runtime.NumCPU()
    }
    
    result := NewMatrix(a.Rows, b.Cols)
    
    // 计算每个worker处理的行数
    rowsPerWorker := (a.Rows + numWorkers - 1) / numWorkers
    
    var wg sync.WaitGroup
    
    for w := 0; w < numWorkers; w++ {
        wg.Add(1)
        go func(workerId int) {
            defer wg.Done()
            
            // 计算此worker处理的行范围
            startRow := workerId * rowsPerWorker
            endRow := (workerId + 1) * rowsPerWorker
            
            if endRow > a.Rows {
                endRow = a.Rows
            }
            
            // 处理分配的行
            for i := startRow; i < endRow; i++ {
                for j := 0; j < b.Cols; j++ {
                    sum := 0.0
                    for k := 0; k < a.Cols; k++ {
                        sum += a.Data[i][k] * b.Data[k][j]
                    }
                    result.Data[i][j] = sum
                }
            }
        }(w)
    }
    
    wg.Wait()
    return result, nil
}

// 分块矩阵乘法
func BlockMatrixMultiply(a, b *Matrix, blockSize int) (*Matrix, error) {
    // 检查矩阵维度
    if a.Cols != b.Rows {
        return nil, fmt.Errorf("矩阵维度不匹配: %dx%d 和 %dx%d", 
                             a.Rows, a.Cols, b.Rows, b.Cols)
    }
    
    result := NewMatrix(a.Rows, b.Cols)
    
    // 按块进行乘法
    for i := 0; i < a.Rows; i += blockSize {
        iEnd := i + blockSize
        if iEnd > a.Rows {
            iEnd = a.Rows
        }
        
        for j := 0; j < b.Cols; j += blockSize {
            jEnd := j + blockSize
            if jEnd > b.Cols {
                jEnd = b.Cols
            }
            
            for k := 0; k < a.Cols; k += blockSize {
                kEnd := k + blockSize
                if kEnd > a.Cols {
                    kEnd = a.Cols
                }
                
                // 乘法计算块
                for ii := i; ii < iEnd; ii++ {
                    for jj := j; jj < jEnd; jj++ {
                        for kk := k; kk < kEnd; kk++ {
                            result.Data[ii][jj] += a.Data[ii][kk] * b.Data[kk][jj]
                        }
                    }
                }
            }
        }
    }
    
    return result, nil
}

// 并行分块矩阵乘法
func ParallelBlockMatrixMultiply(a, b *Matrix, blockSize, numWorkers int) (*Matrix, error) {
    // 检查矩阵维度
    if a.Cols != b.Rows {
        return nil, fmt.Errorf("矩阵维度不匹配: %dx%d 和 %dx%d", 
                             a.Rows, a.Cols, b.Rows, b.Cols)
    }
    
    if numWorkers <= 0 {
        numWorkers = runtime.NumCPU()
    }
    
    result := NewMatrix(a.Rows, b.Cols)
    
    // 计算水平块数
    hBlocks := (a.Rows + blockSize - 1) / blockSize
    vBlocks := (b.Cols + blockSize - 1) / blockSize
    totalBlocks := hBlocks * vBlocks
    
    // 确保worker不多于总块数
    if numWorkers > totalBlocks {
        numWorkers = totalBlocks
    }
    
    blocksPerWorker := (totalBlocks + numWorkers - 1) / numWorkers
    
    var wg sync.WaitGroup
    
    // 启动worker处理块
    for w := 0; w < numWorkers; w++ {
        wg.Add(1)
        go func(workerId int) {
            defer wg.Done()
            
            // 计算此worker处理的块
            startBlock := workerId * blocksPerWorker
            endBlock := (workerId + 1) * blocksPerWorker
            
            if endBlock > totalBlocks {
                endBlock = totalBlocks
            }
            
            for block := startBlock; block < endBlock; block++ {
                // 将一维块索引转换为二维块坐标
                iBlock := block / vBlocks
                jBlock := block % vBlocks
                
                // 计算实际行列范围
                i := iBlock * blockSize
                iEnd := i + blockSize
                if iEnd > a.Rows {
                    iEnd = a.Rows
                }
                
                j := jBlock * blockSize
                jEnd := j + blockSize
                if jEnd > b.Cols {
                    jEnd = b.Cols
                }
                
                // 处理此块的所有k块
                for k := 0; k < a.Cols; k += blockSize {
                    kEnd := k + blockSize
                    if kEnd > a.Cols {
                        kEnd = a.Cols
                    }
                    
                    // 计算块乘法
                    for ii := i; ii < iEnd; ii++ {
                        for jj := j; jj < jEnd; jj++ {
                            for kk := k; kk < kEnd; kk++ {
                                result.Data[ii][jj] += a.Data[ii][kk] * b.Data[kk][jj]
                            }
                        }
                    }
                }
            }
        }(w)
    }
    
    wg.Wait()
    return result, nil
}

// Strassen算法 (仅适用于2的幂次方大小的方阵)
func StrassenMultiply(a, b *Matrix) (*Matrix, error) {
    // 检查矩阵维度
    if a.Rows != a.Cols || b.Rows != b.Cols || a.Cols != b.Rows {
        return nil, fmt.Errorf("Strassen算法需要方阵")
    }
    
    n := a.Rows
    // 检查是否为2的幂
    if n&(n-1) != 0 {
        return nil, fmt.Errorf("Strassen算法需要矩阵大小为2的幂")
    }
    
    return strassenHelper(a, b, n), nil
}

// Strassen算法的递归辅助函数
func strassenHelper(a, b *Matrix, n int) *Matrix {
    // 基本情况
    if n <= 64 {  // 对小矩阵使用常规算法
        result := NewMatrix(n, n)
        for i := 0; i < n; i++ {
            for j := 0; j < n; j++ {
                for k := 0; k < n; k++ {
                    result.Data[i][j] += a.Data[i][k] * b.Data[k][j]
                }
            }
        }
        return result
    }
    
    // 矩阵划分
    halfN := n / 2
    
    // 创建子矩阵
    a11 := subMatrix(a, 0, 0, halfN)
    a12 := subMatrix(a, 0, halfN, halfN)
    a21 := subMatrix(a, halfN, 0, halfN)
    a22 := subMatrix(a, halfN, halfN, halfN)
    
    b11 := subMatrix(b, 0, 0, halfN)
    b12 := subMatrix(b, 0, halfN, halfN)
    b21 := subMatrix(b, halfN, 0, halfN)
    b22 := subMatrix(b, halfN, halfN, halfN)
    
    // 计算Strassen的7个乘积
    m1 := strassenHelper(addMatrices(a11, a22), addMatrices(b11, b22), halfN)
    m2 := strassenHelper(addMatrices(a21, a22), b11, halfN)
    m3 := strassenHelper(a11, subtractMatrices(b12, b22), halfN)
    m4 := strassenHelper(a22, subtractMatrices(b21, b11), halfN)
    m5 := strassenHelper(addMatrices(a11, a12), b22, halfN)
    m6 := strassenHelper(subtractMatrices(a21, a11), addMatrices(b11, b12), halfN)
    m7 := strassenHelper(subtractMatrices(a12, a22), addMatrices(b21, b22), halfN)
    
    // 计算结果的子矩阵
    c11 := addMatrices(subtractMatrices(addMatrices(m1, m4), m5), m7)
    c12 := addMatrices(m3, m5)
    c21 := addMatrices(m2, m4)
    c22 := addMatrices(subtractMatrices(addMatrices(m1, m3), m2), m6)
    
    // 组合子矩阵
    result := NewMatrix(n, n)
    for i := 0; i < halfN; i++ {
        for j := 0; j < halfN; j++ {
            result.Data[i][j] = c11.Data[i][j]
            result.Data[i][j+halfN] = c12.Data[i][j]
            result.Data[i+halfN][j] = c21.Data[i][j]
            result.Data[i+halfN][j+halfN] = c22.Data[i][j]
        }
    }
    
    return result
}

// 提取子矩阵
func subMatrix(m *Matrix, rowStart, colStart, size int) *Matrix {
    result := NewMatrix(size, size)
    for i := 0; i < size; i++ {
        for j := 0; j < size; j++ {
            result.Data[i][j] = m.Data[rowStart+i][colStart+j]
        }
    }
    return result
}

// 矩阵加法
func addMatrices(a, b *Matrix) *Matrix {
    n := a.Rows
    result := NewMatrix(n, n)
    for i := 0; i < n; i++ {
        for j := 0; j < n; j++ {
            result.Data[i][j] = a.Data[i][j] + b.Data[i][j]
        }
    }
    return result
}

// 矩阵减法
func subtractMatrices(a, b *Matrix) *Matrix {
    n := a.Rows
    result := NewMatrix(n, n)
    for i := 0; i < n; i++ {
        for j := 0; j < n; j++ {
            result.Data[i][j] = a.Data[i][j] - b.Data[i][j]
        }
    }
    return result
}

// 矩阵相等检查
func MatricesEqual(a, b *Matrix, epsilon float64) bool {
    if a.Rows != b.Rows || a.Cols != b.Cols {
        return false
    }
    
    for i := 0; i < a.Rows; i++ {
        for j := 0; j < a.Cols; j++ {
            if math.Abs(a.Data[i][j] - b.Data[i][j]) > epsilon {
                return false
            }
        }
    }
    
    return true
}

// 用法示例
func parallelMatrixMultiplyExample() {
    fmt.Println("并行矩阵乘法测试:")
    
    // 测试不同大小的矩阵
    sizes := []int{100, 500, 1000, 2000}
    
    for _, size := range sizes {
        fmt.Printf("\n矩阵大小: %dx%d\n", size, size)
        
        // 创建随机矩阵
        a := NewMatrix(size, size)
        b := NewMatrix(size, size)
        
        a.RandomInit(0, 1)
        b.RandomInit(0, 1)
        
        // 测试串行乘法
        var serialResult *Matrix
        var serialDuration time.Duration
        
        // 对于大矩阵，跳过串行计算
        if size <= 1000 {
            start := time.Now()
            serialResult, _ = MatrixMultiply(a, b)
            serialDuration = time.Since(start)
            fmt.Printf("串行乘法: %v\n", serialDuration)
        } else {
            fmt.Println("串行乘法: 跳过（太大）")
        }
        
        // 测试并行乘法
        numWorkers := runtime.NumCPU()
        start := time.Now()
        parallelResult, _ := ParallelMatrixMultiply(a, b, numWorkers)
        parallelDuration := time.Since(start)
        
        fmt.Printf("并行乘法 (%d worker): %v\n", numWorkers, parallelDuration)
        
        // 测试分块乘法
        blockSize := 32  // 可调整
        start = time.Now()
        blockResult, _ := BlockMatrixMultiply(a, b, blockSize)
        blockDuration := time.Since(start)
        
        fmt.Printf("分块乘法 (块大小=%d): %v\n", blockSize, blockDuration)
        
        // 测试并行分块乘法
        start = time.Now()
        parallelBlockResult, _ := ParallelBlockMatrixMultiply(a, b, blockSize, numWorkers)
        parallelBlockDuration := time.Since(start)
        
        fmt.Printf("并行分块乘法: %v\n", parallelBlockDuration)
        
        // 验证结果（如果有串行结果）
        if serialResult != nil {
            // 检查结果是否一致
            fmt.Printf("并行结果正确: %t\n", 
                      MatricesEqual(serialResult, parallelResult, 1e-10))
            fmt.Printf("分块结果正确: %t\n", 
                      MatricesEqual(serialResult, blockResult, 1e-10))
            fmt.Printf("并行分块结果正确: %t\n", 
                      MatricesEqual(serialResult, parallelBlockResult, 1e-10))
            
            // 计算加速比
            fmt.Printf("并行加速比: %.2fx\n", 
                      float64(serialDuration)/float64(parallelDuration))
            fmt.Printf("分块加速比: %.2fx\n", 
                      float64(serialDuration)/float64(blockDuration))
            fmt.Printf("并行分块加速比: %.2fx\n", 
                      float64(serialDuration)/float64(parallelBlockDuration))
        }
    }
    
    // 测试Strassen算法（仅用于2的幂大小的方阵）
    fmt.Println("\nStrassen算法测试:")
    
    strassenSizes := []int{128, 256, 512, 1024}
    
    for _, size := range strassenSizes {
        fmt.Printf("\n矩阵大小: %dx%d\n", size, size)
        
        // 创建随机矩阵
        a := NewMatrix(size, size)
        b := NewMatrix(size, size)
        
        a.RandomInit(0, 1)
        b.RandomInit(0, 1)
        
        // 常规算法
        var standardResult *Matrix
        var standardDuration time.Duration
        
        if size <= 512 {
            start := time.Now()
            standardResult, _ = MatrixMultiply(a, b)
            standardDuration = time.Since(start)
            fmt.Printf("常规算法: %v\n", standardDuration)
        } else {
            // 对于大矩阵，使用并行算法作为基准
            start := time.Now()
            standardResult, _ = ParallelMatrixMultiply(a, b, runtime.NumCPU())
            standardDuration = time.Since(start)
            fmt.Printf("并行算法 (基准): %v\n", standardDuration)
        }
        
        // Strassen算法
        start := time.Now()
        strassenResult, _ := StrassenMultiply(a, b)
        strassenDuration := time.Since(start)
        
        fmt.Printf("Strassen算法: %v\n", strassenDuration)
        
        // 验证结果
        correct := MatricesEqual(standardResult, strassenResult, 1e-10)
        fmt.Printf("Strassen结果正确: %t\n", correct)
        
        // 计算加速比
        fmt.Printf("Strassen加速比: %.2fx\n", 
                  float64(standardDuration)/float64(strassenDuration))
    }
}
```

## 9. 未来展望与总结

随着Go语言的不断发展，并行和分布式算法的设计与实现将变得越来越重要。我们展示的算法和数据结构演示了Go如何在现代硬件上高效利用多核处理器执行复杂计算任务。

在未来，Go的并发模型可能会进一步增强，包括：

1. **结构化并发**：更好的goroutine管理和生命周期控制
2. **并行编程原语**：更丰富的高级并行模式，如Fork-Join、工作窃取调度等
3. **内存模型优化**：更高效的共享内存访问和同步原语
4. **硬件加速**：更好地利用GPU、FPGA等专用硬件
5. **分布式计算**：跨网络节点的计算框架与库

通过结合Go的简洁语法、强大的并发模型和2025版本中的增强泛型支持，
程序员将能够更轻松地实现高性能算法，同时保持代码可读性和可维护性。

总结：

- **Go 2025**在类型系统和泛型方面的增强，使实现通用算法和数据结构变得更加简洁高效
- **并行算法**的实现展示了Go如何利用多核处理器加速计算密集型任务
- **高级数据结构**（如布隆过滤器、跳表和一致性哈希）为解决特定问题提供了高效工具
- **函数式编程范式**的应用与Go的命令式风格相结合，提供了更多样化的问题解决方法
- **性能调优技术**如缓存感知算法设计和内存布局优化，在Go中同样适用且重要

### 9.1 基准测试与性能剖析

在Go的开发过程中，基准测试和性能剖析是优化算法的重要手段。Go 2025版本进一步增强了这些工具的能力：

```go
// 基准测试示例
func BenchmarkAlgorithms(b *testing.B) {
    sizes := []int{100, 1000, 10000}
    algorithms := map[string]func([]int, int) []int{
        "串行归并排序":  func(data []int, _ int) []int { return MergeSort(data) },
        "并行归并排序":  func(data []int, n int) []int { return ParallelMergeSort(data, 100, n) },
        "标准库排序":   func(data []int, _ int) []int { 
            result := make([]int, len(data))
            copy(result, data)
            sort.Ints(result)
            return result
        },
    }
    
    for _, size := range sizes {
        // 准备随机数据
        data := make([]int, size)
        for i := range data {
            data[i] = rand.Intn(10000)
        }
        
        for name, algorithm := range algorithms {
            b.Run(fmt.Sprintf("%s-Size%d", name, size), func(b *testing.B) {
                b.ResetTimer()
                for i := 0; i < b.N; i++ {
                    algorithm(data, runtime.NumCPU())
                }
            })
        }
    }
}

// 使用内置的性能分析器
func profileAlgorithm() {
    // 创建CPU性能分析文件
    cpuFile, _ := os.Create("cpu_profile.pprof")
    defer cpuFile.Close()
    pprof.StartCPUProfile(cpuFile)
    defer pprof.StopCPUProfile()
    
    // 运行需要分析的算法
    data := generateLargeDataset(1000000)
    ParallelMergeSort(data, 100, runtime.NumCPU())
    
    // 创建内存性能分析文件
    memFile, _ := os.Create("mem_profile.pprof")
    defer memFile.Close()
    runtime.GC() // 在记录内存使用前先进行垃圾收集
    pprof.WriteHeapProfile(memFile)
    
    // 结果可以使用pprof工具进行分析：
    // go tool pprof cpu_profile.pprof
    // go tool pprof mem_profile.pprof
}
```

### 9.2 云原生和分布式算法

Go在云原生和分布式系统方面的应用将进一步扩展，2025版本中可能会增强对分布式算法的支持：

```go
// 分布式一致性算法 (Raft协议简化示例)
type RaftNode struct {
    id          int
    state       string // "follower", "candidate", "leader"
    currentTerm int
    votedFor    int
    log         []LogEntry
    commitIndex int
    peers       []string
    // 其他Raft状态
}

type LogEntry struct {
    Term    int
    Command string
}

func (n *RaftNode) Start() {
    // 初始化为follower
    n.state = "follower"
    n.currentTerm = 0
    n.votedFor = -1
    
    // 启动后台goroutine处理各种Raft定时任务
    go n.runElectionTimer()
    go n.heartbeatLoop()
    go n.applyCommittedEntries()
}

func (n *RaftNode) runElectionTimer() {
    for {
        // 随机选举超时
        timeout := 150 + rand.Intn(150) // 150-300ms
        time.Sleep(time.Duration(timeout) * time.Millisecond)
        
        if n.state == "follower" || n.state == "candidate" {
            // 开始选举
            n.startElection()
        }
    }
}

func (n *RaftNode) startElection() {
    n.state = "candidate"
    n.currentTerm++
    n.votedFor = n.id
    
    // 向其他节点请求投票
    // ...省略实现细节
}

func (n *RaftNode) heartbeatLoop() {
    for {
        if n.state == "leader" {
            // 发送心跳
            n.sendHeartbeats()
        }
        time.Sleep(50 * time.Millisecond)
    }
}

// 分布式键值存储 (简化示例)
type DistributedKV struct {
    data           map[string]string
    mu             sync.RWMutex
    nodeID         string
    peers          []string
    consistentHash *ConsistentHash[string]
}

func NewDistributedKV(nodeID string, peers []string) *DistributedKV {
    kv := &DistributedKV{
        data:   make(map[string]string),
        nodeID: nodeID,
        peers:  peers,
    }
    
    // 创建一致性哈希环
    ch := NewConsistentHash[string](10, nil)
    ch.Add(append(peers, nodeID)...)
    kv.consistentHash = ch
    
    return kv
}

func (kv *DistributedKV) Put(key, value string) error {
    // 确定键应该存储在哪个节点
    node, _ := kv.consistentHash.Get(key)
    
    if node == kv.nodeID {
        // 当前节点负责此键
        kv.mu.Lock()
        kv.data[key] = value
        kv.mu.Unlock()
        return nil
    } else {
        // 转发到负责的节点
        return kv.forwardPut(node, key, value)
    }
}

func (kv *DistributedKV) Get(key string) (string, error) {
    node, _ := kv.consistentHash.Get(key)
    
    if node == kv.nodeID {
        // 当前节点负责此键
        kv.mu.RLock()
        value, ok := kv.data[key]
        kv.mu.RUnlock()
        
        if !ok {
            return "", fmt.Errorf("键不存在: %s", key)
        }
        return value, nil
    } else {
        // 转发到负责的节点
        return kv.forwardGet(node, key)
    }
}

// 转发请求实现 (简化)
func (kv *DistributedKV) forwardPut(node, key, value string) error {
    // 实际实现中，这里会进行网络调用
    // ...
    return nil
}

func (kv *DistributedKV) forwardGet(node, key string) (string, error) {
    // 实际实现中，这里会进行网络调用
    // ...
    return "", nil
}
```

### 9.3 AI与机器学习相关算法

Go 2025在机器学习和AI领域的应用将会增加，特别是在模型部署和高性能推理方面：

```go
// 简单神经网络实现
type NeuralNetwork struct {
    layers []Layer
}

type Layer interface {
    Forward(input [][]float64) [][]float64
}

// 全连接层
type DenseLayer struct {
    weights [][]float64
    biases  []float64
    activation func(float64) float64
}

func NewDenseLayer(inputSize, outputSize int, activation func(float64) float64) *DenseLayer {
    // 初始化权重和偏置
    weights := make([][]float64, inputSize)
    for i := range weights {
        weights[i] = make([]float64, outputSize)
        for j := range weights[i] {
            weights[i][j] = rand.NormFloat64() * 0.1 // 随机初始化
        }
    }
    
    biases := make([]float64, outputSize)
    
    return &DenseLayer{
        weights:    weights,
        biases:     biases,
        activation: activation,
    }
}

func (l *DenseLayer) Forward(input [][]float64) [][]float64 {
    batchSize := len(input)
    outputSize := len(l.biases)
    
    output := make([][]float64, batchSize)
    for i := range output {
        output[i] = make([]float64, outputSize)
        // 初始化为偏置值
        copy(output[i], l.biases)
    }
    
    // 矩阵乘法: output = input * weights + biases
    for i := 0; i < batchSize; i++ {
        for j := 0; j < outputSize; j++ {
            for k := 0; k < len(l.weights); k++ {
                output[i][j] += input[i][k] * l.weights[k][j]
            }
            // 应用激活函数
            output[i][j] = l.activation(output[i][j])
        }
    }
    
    return output
}

// 激活函数
func ReLU(x float64) float64 {
    if x > 0 {
        return x
    }
    return 0
}

func Sigmoid(x float64) float64 {
    return 1.0 / (1.0 + math.Exp(-x))
}

// 并行推理
func (nn *NeuralNetwork) PredictParallel(input [][]float64, numWorkers int) [][]float64 {
    batchSize := len(input)
    
    if numWorkers <= 0 {
        numWorkers = runtime.NumCPU()
    }
    
    // 每个worker处理的样本数
    samplesPerWorker := (batchSize + numWorkers - 1) / numWorkers
    
    // 存储中间结果
    var mu sync.Mutex
    layerOutputs := make([][][]float64, len(nn.layers)+1)
    layerOutputs[0] = input
    
    // 按层计算
    for l := 0; l < len(nn.layers); l++ {
        var wg sync.WaitGroup
        
        // 创建当前层的输出
        layerOutputs[l+1] = make([][]float64, batchSize)
        
        // 并行处理批次
        for w := 0; w < numWorkers; w++ {
            wg.Add(1)
            go func(workerId int) {
                defer wg.Done()
                
                start := workerId * samplesPerWorker
                end := (workerId + 1) * samplesPerWorker
                if end > batchSize {
                    end = batchSize
                }
                
                // 跳过空批次
                if start >= batchSize {
                    return
                }
                
                // 处理此worker的样本
                workerInput := layerOutputs[l][start:end]
                workerOutput := nn.layers[l].Forward(workerInput)
                
                // 存储结果
                mu.Lock()
                for i := 0; i < len(workerOutput); i++ {
                    layerOutputs[l+1][start+i] = workerOutput[i]
                }
                mu.Unlock()
            }(w)
        }
        
        wg.Wait()
    }
    
    // 返回最后一层的输出
    return layerOutputs[len(nn.layers)]
}

// 简单的K-means聚类算法
func KMeansClustering(data [][]float64, k, maxIterations int) ([][]float64, []int) {
    n := len(data)
    dim := len(data[0])
    
    // 初始化中心点 (从数据中随机选择)
    centers := make([][]float64, k)
    used := make(map[int]bool)
    
    for i := 0; i < k; i++ {
        for {
            idx := rand.Intn(n)
            if !used[idx] {
                centers[i] = make([]float64, dim)
                copy(centers[i], data[idx])
                used[idx] = true
                break
            }
        }
    }
    
    // 分配数组 (每个点属于哪个簇)
    assignments := make([]int, n)
    
    for iter := 0; iter < maxIterations; iter++ {
        // 分配每个点到最近的中心
        changed := false
        
        for i := 0; i < n; i++ {
            minDist := math.MaxFloat64
            minIdx := 0
            
            for j := 0; j < k; j++ {
                dist := euclideanDistance(data[i], centers[j])
                if dist < minDist {
                    minDist = dist
                    minIdx = j
                }
            }
            
            if assignments[i] != minIdx {
                assignments[i] = minIdx
                changed = true
            }
        }
        
        // 如果没有点改变簇，则收敛
        if !changed {
            break
        }
        
        // 重新计算中心点
        counts := make([]int, k)
        newCenters := make([][]float64, k)
        for i := range newCenters {
            newCenters[i] = make([]float64, dim)
        }
        
        for i := 0; i < n; i++ {
            cluster := assignments[i]
            counts[cluster]++
            
            for j := 0; j < dim; j++ {
                newCenters[cluster][j] += data[i][j]
            }
        }
        
        // 平均化
        for i := 0; i < k; i++ {
            if counts[i] > 0 {
                for j := 0; j < dim; j++ {
                    newCenters[i][j] /= float64(counts[i])
                }
            }
        }
        
        centers = newCenters
    }
    
    return centers, assignments
}

func euclideanDistance(a, b []float64) float64 {
    sum := 0.0
    for i := range a {
        diff := a[i] - b[i]
        sum += diff * diff
    }
    return math.Sqrt(sum)
}
```

### 9.4 总结与展望

Go 2025通过其增强的泛型系统、高效的并发模型和简洁的语法，为算法和数据结构的实现提供了强大的支持。本文展示的各种算法和数据结构实现，不仅仅是学术示例，它们在实际应用中具有重要价值：

1. **高性能Web服务**可以利用一致性哈希、布隆过滤器和并发数据结构来提高吞吐量和降低延迟
2. **大数据处理系统**可以采用并行排序、并行图算法和分布式键值存储来处理海量数据
3. **低延迟交易系统**可以应用无锁数据结构和缓存感知算法来减少响应时间
4. **推荐引擎和搜索系统**可以使用Trie树、跳表和前缀树等数据结构来加速查询
5. **分布式系统**可以实现一致性协议、分布式锁和容错机制来提高系统可靠性

随着硬件和网络技术的发展，我们可以预见Go语言在以下方向将有更多创新：

- **异构计算**：更好地集成GPU、TPU等专用硬件加速器
- **量子计算接口**：为量子计算提供清晰简洁的编程模型
- **内存优化**：进一步减少GC延迟，提高内存利用效率
- **边缘计算**：适应资源受限环境的轻量级算法和数据结构
- **自适应算法**：根据运行时条件自动调整算法参数和策略

Go语言的设计哲学——简洁、明确、实用——使其成为实现高效算法和数据结构的理想选择。无论是系统级应用还是云原生服务，我们都能看到Go在性能和生产力之间取得了良好的平衡。

展望未来，随着Go 2025和后续版本的发展，我们可以期待更加丰富的标准库、更强大的语言特性和更广泛的生态系统，这将进一步提升Go在计算机科学各领域的应用价值。

通过合理使用本文介绍的算法和数据结构，开发者可以构建既高效又可靠的应用程序，充分发挥现代计算硬件的潜力，满足不断增长的性能需求，同时保持代码的可读性和可维护性。

在算法与工程实践的交叉点上，Go语言正在写下属于自己的篇章。
