Inductive season : Type :=
    | spring
    | summer
    | autumn
    | winter.

Check spring.

Definition opp_season (s :season) :season :=
    match s with
    | spring => autumn
    | summer => winter
    | autumn => spring
    | winter => summer
    end.

Compute (opp_season (opp_season spring)).