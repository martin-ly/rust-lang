
# rust-lang

[rust-lang-philosophy](docs/rust_core_philosophy.md)
[rust-lang](docs/rust_paradiam.md)

## rust programming language learning - pre-knowledge

[rust-cpp-lang](docs/lang_compare/rust_cpp.md)

### 1. Programming language model: include { variable, type system, control_flow }

    1.1 reference relative relationship lifetime syntax model: include { variable } 
    1.2 resource defination and organization,lifecycle RAII model: include { type system }
    1.3 runtime behavior Semantic model: include { control_flow }

[memory](docs/view_type_theory/type_control_memory.md)
[rust-lang-model](docs/view_type_control/type_variable_control03.md)

### 2. variable syntax model: include { own, borrow, scope }

    2.1 Ownership concept for human inference,Compiler Syntax Semantic check: include { Copy Semantic, Clone Semantic, Move Semantic }, 
    2.2 Defination,Modify explict Semantic: include { let,constant, ref, mut, ref mut }
    2.3 Copy implicit Semantic on Primitive Types: include{ number, boolean,etc internal Types}
    2.4 Clone explicit Semantic on Types
    2.5 Move implicit Semantic on Compound or Composite Types(programmer define types): include{ struct, enum, tuple, array, etc},
    2.6 Static check on move Semantic in Compiling time,variable's validate,Ownership's linear moving: include { visibility, shadow, scope ,only one owner},
    2.7 Runtime check on move Semantic in Compiling time or runtime,
    2.8 Scope and visibility semantic model: include { global, local, static,function,closure,expression }

[rust-borrow-checker](docs/rust/ownership_borrow_scope/borrow_check_inference.md)
[variable](docs/rust/control/control_flow_rust.md)
[ref_mut_reason](docs/rust/ownership_borrow_scope/ref_mut_reason.md)

### 3. type system model: include { primitive_type, compound_type, generic_type, trait_type }

    3.1 primitive_type: include{ number, boolean,etc internal Types}
    3.2 compound_type: include{  tuple, array, slice, string,etc}
    3.3 composite_type: include{ struct, enum }
    3.4 type_of_type: include{ type_alias, type_newtype, impl, trait } 
    3.5 generic_type: include{ generic_function, generic_struct, generic_enum, generic_trait,generic_impl}
    3.6 async_type: include{ async_function, async_trait }
    3.7 type_transform: include{ type_cast: as, into, from,try_into, try_from }
    3.8 type_variance: include{ invariant_type, covariant_type, contravariance_type }

[variant](docs/view_type_theory/type_variant/variant.md)
[variant_reason](docs/view_type_theory/type_variant/variant_reason.md)
[invariant_type](docs/view_type_theory/type_variant/invariance_type.md)
[covariant_type](docs/view_type_theory/type_variant/covariance_type.md)
[contravariance_type](docs/view_type_theory/type_variant/contravariance_type.md)
[variable](docs/view_type_theory/type_variant/mutability_rust.md)

### 4. control_flow model: include { function, closure, expression, statement }

    4.1 function: include{ function_define, function_call, function_signature }
    4.2 closure: include{ closure_define, closure_call }
    4.3 expression: include{ expression,match, expression_value }
    4.4 statement: include{ statement,if,else,while,for,label,loop,match,return,break,continue,yield,gen,async,await,macro }

### 5. package and engineer

[package_mod](docs/rust/cargo_package_mod.md)

## 1. own_borrow_scope  

[ref_refmut](docs/rust/ownership_borrow_scope/ref_mut_reason.md)

## 2. type_system

## 3. control_fn

## 4. generic

## 5. threads

## 6. async

## 7. process

## 8. algorithms

[algorithms](docs/rust/algorithms)

## 9. design_pattern

[design_pattern](docs/design_pattern)

## 10. networks

## 11. frameworks

## 12. middlewares

## 13. microservice
