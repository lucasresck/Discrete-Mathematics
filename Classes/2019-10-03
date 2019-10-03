constant U : Type
constant p : U → U → Prop
constants A B C : U → Prop

theorem ex1 : (∃ x, ∀ y, p x y) → (∀ y, ∃ x, p x y) :=
  begin
    intros h1,
    intros a,
    cases h1 with b h2,
    existsi b,
    have h3, from h2 a,
    assumption
  end

theorem ex2 (h1 : ∀ x, A x ∨ B x) (h2 : ∀ y, ¬ A y) :
∀ x, B x :=
  begin
    intro a,
    cases h1 a,
    have h3, from h2 a, contradiction,
    assumption
  end

constants even odd : U → Prop
constant s : U → U

theorem ex3 (h1 : ∀ x, even x ∨ odd x)
(h2 : ∀ x, odd x → even (s x)) :
∀ x, even x ∨ even (s x) :=
  begin
    intro a,
    cases h1 a,
    exact (or.inl h),
    --have h3, from h2 a h,
    exact (or.inr $ h2 a h)
  end

theorem ex4 : (∃ x, A x) ∨ (∃ x, B x) → (∃ x, A x ∨ B x) :=
  begin
    intro h,
    cases h,
    cases h,
    existsi h_w,
    exact (or.inl h_h),
    cases h,
    existsi h_w,
    exact (or.inr h_h),
end
