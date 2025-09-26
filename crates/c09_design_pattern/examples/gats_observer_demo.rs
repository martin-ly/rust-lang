use c09_design_pattern::behavioral::observer::define::{BorrowingObserver, BorrowingSubjectString};

fn main() {
    let mut subject = BorrowingSubjectString::new();
    subject.register_observer(BorrowingObserver);

    let msg = String::from("GATs observer demo");
    subject.notify_observers(&msg);
}


