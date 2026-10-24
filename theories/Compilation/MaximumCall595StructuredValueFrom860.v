From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall595StructuredContextFrom860 MaximumCall595StructuredChunk000From860 MaximumCall595StructuredChunk001From860 MaximumCall595StructuredChunk002From860 MaximumCall595StructuredChunk003From860 MaximumCall595StructuredChunk004From860 MaximumCall595StructuredChunk005From860 MaximumCall595StructuredChunk006From860 MaximumCall595StructuredChunk007From860 MaximumCall595StructuredChunk008From860 MaximumCall595StructuredChunk009From860 MaximumCall595StructuredChunk010From860 MaximumCall595StructuredChunk011From860 MaximumCall595StructuredChunk012From860 MaximumCall595StructuredChunk013From860 MaximumCall595StructuredChunk014From860 MaximumCall595StructuredChunk015From860 MaximumCall595StructuredChunk016From860 MaximumCall595StructuredChunk017From860 MaximumCall595StructuredChunk018From860 MaximumCall595StructuredChunk019From860 MaximumCall595StructuredChunk020From860 MaximumCall595StructuredChunk021From860 MaximumCall595StructuredChunk022From860 MaximumCall595StructuredChunk023From860 MaximumCall595StructuredChunk024From860 MaximumCall595StructuredChunk025From860 MaximumCall595StructuredChunk026From860 MaximumCall595StructuredChunk027From860 MaximumCall595StructuredChunk028From860 MaximumCall595StructuredChunk029From860 MaximumCall595StructuredChunk030From860 MaximumCall595StructuredChunk031From860 MaximumCall595StructuredChunk032From860 MaximumCall595StructuredChunk033From860 MaximumCall595StructuredChunk034From860 MaximumCall595StructuredChunk035From860 MaximumCall595StructuredChunk036From860 MaximumCall595StructuredChunk037From860 MaximumCall595StructuredChunk038From860 MaximumCall595StructuredChunk039From860 MaximumCall595StructuredChunk040From860 MaximumCall595StructuredChunk041From860 MaximumCall595StructuredChunk042From860 MaximumCall595StructuredChunk043From860 MaximumCall595StructuredChunk044From860 MaximumCall595StructuredChunk045From860 MaximumCall595StructuredChunk046From860 MaximumCall595StructuredChunk047From860 MaximumCall595StructuredChunk048From860 MaximumCall595StructuredChunk049From860 MaximumCall595StructuredChunk050From860 MaximumCall595StructuredChunk051From860 MaximumCall595StructuredChunk052From860 MaximumCall595StructuredChunk053From860 MaximumCall595StructuredChunk054From860 MaximumCall595StructuredChunk055From860 MaximumCall595StructuredChunk056From860 MaximumCall595StructuredChunk057From860 MaximumCall595StructuredChunk058From860 MaximumCall595StructuredChunk059From860 MaximumCall595StructuredChunk060From860 MaximumCall595StructuredChunk061From860 MaximumCall595StructuredChunk062From860 MaximumCall595StructuredChunk063From860 MaximumCall595StructuredChunk064From860 MaximumCall595StructuredChunk065From860 MaximumCall595StructuredChunk066From860 MaximumCall595StructuredChunk067From860 MaximumCall595StructuredChunk068From860 MaximumCall595StructuredChunk069From860 MaximumCall595StructuredChunk070From860 MaximumCall595StructuredChunk071From860 MaximumCall595StructuredChunk072From860 MaximumCall595StructuredChunk073From860 MaximumCall595StructuredChunk074From860 MaximumCall595StructuredChunk075From860 MaximumCall595StructuredChunk076From860 MaximumCall595StructuredChunk077From860 MaximumCall595StructuredChunk078From860 MaximumCall595StructuredChunk079From860 MaximumCall595StructuredChunk080From860 MaximumCall595StructuredChunk081From860 MaximumCall595StructuredChunk082From860 MaximumCall595StructuredChunk083From860 MaximumCall595StructuredChunk084From860 MaximumCall595StructuredChunk085From860 MaximumCall595StructuredChunk086From860 MaximumCall595StructuredChunk087From860 MaximumCall595StructuredChunk088From860 MaximumCall595StructuredChunk089From860 MaximumCall595StructuredChunk090From860 MaximumCall595StructuredChunk091From860 MaximumCall595StructuredChunk092From860 MaximumCall595StructuredChunk093From860 MaximumCall595StructuredChunk094From860 MaximumCall595StructuredChunk095From860 MaximumCall595StructuredChunk096From860 MaximumCall595StructuredChunk097From860 MaximumCall595StructuredChunk098From860 MaximumCall595StructuredChunk099From860 MaximumCall595StructuredChunk100From860 MaximumCall595StructuredChunk101From860 MaximumCall595StructuredChunk102From860 MaximumCall595StructuredChunk103From860 MaximumCall595StructuredChunk104From860 MaximumCall595StructuredChunk105From860 MaximumCall595StructuredChunk106From860 MaximumCall595StructuredChunk107From860 MaximumCall595StructuredChunk108From860 MaximumCall595StructuredChunk109From860 MaximumCall595StructuredChunk110From860 MaximumCall595StructuredChunk111From860 MaximumCall595StructuredChunk112From860 MaximumCall595StructuredChunk113From860 MaximumCall595StructuredChunk114From860 MaximumCall595StructuredChunk115From860 MaximumCall595StructuredChunk116From860 MaximumCall595StructuredChunk117From860 MaximumCall595StructuredChunk118From860 MaximumCall595StructuredChunk119From860 MaximumCall595StructuredChunk120From860 MaximumCall595StructuredChunk121From860 MaximumCall595StructuredChunk122From860 MaximumCall595StructuredChunk123From860 MaximumCall595StructuredChunk124From860 MaximumCall595StructuredChunk125From860 MaximumCall595StructuredChunk126From860 MaximumCall595StructuredChunk127From860 MaximumCall595StructuredChunk128From860 MaximumCall595StructuredChunk129From860 MaximumCall595StructuredChunk130From860 MaximumCall595StructuredChunk131From860 MaximumCall595StructuredChunk132From860 MaximumCall595StructuredChunk133From860 MaximumCall595StructuredChunk134From860 MaximumCall595StructuredChunk135From860 MaximumCall595StructuredChunk136From860 MaximumCall595StructuredChunk137From860 MaximumCall595StructuredChunk138From860.

Definition values :=
  MaximumCall595StructuredChunk000From860.values ++
  MaximumCall595StructuredChunk001From860.values ++
  MaximumCall595StructuredChunk002From860.values ++
  MaximumCall595StructuredChunk003From860.values ++
  MaximumCall595StructuredChunk004From860.values ++
  MaximumCall595StructuredChunk005From860.values ++
  MaximumCall595StructuredChunk006From860.values ++
  MaximumCall595StructuredChunk007From860.values ++
  MaximumCall595StructuredChunk008From860.values ++
  MaximumCall595StructuredChunk009From860.values ++
  MaximumCall595StructuredChunk010From860.values ++
  MaximumCall595StructuredChunk011From860.values ++
  MaximumCall595StructuredChunk012From860.values ++
  MaximumCall595StructuredChunk013From860.values ++
  MaximumCall595StructuredChunk014From860.values ++
  MaximumCall595StructuredChunk015From860.values ++
  MaximumCall595StructuredChunk016From860.values ++
  MaximumCall595StructuredChunk017From860.values ++
  MaximumCall595StructuredChunk018From860.values ++
  MaximumCall595StructuredChunk019From860.values ++
  MaximumCall595StructuredChunk020From860.values ++
  MaximumCall595StructuredChunk021From860.values ++
  MaximumCall595StructuredChunk022From860.values ++
  MaximumCall595StructuredChunk023From860.values ++
  MaximumCall595StructuredChunk024From860.values ++
  MaximumCall595StructuredChunk025From860.values ++
  MaximumCall595StructuredChunk026From860.values ++
  MaximumCall595StructuredChunk027From860.values ++
  MaximumCall595StructuredChunk028From860.values ++
  MaximumCall595StructuredChunk029From860.values ++
  MaximumCall595StructuredChunk030From860.values ++
  MaximumCall595StructuredChunk031From860.values ++
  MaximumCall595StructuredChunk032From860.values ++
  MaximumCall595StructuredChunk033From860.values ++
  MaximumCall595StructuredChunk034From860.values ++
  MaximumCall595StructuredChunk035From860.values ++
  MaximumCall595StructuredChunk036From860.values ++
  MaximumCall595StructuredChunk037From860.values ++
  MaximumCall595StructuredChunk038From860.values ++
  MaximumCall595StructuredChunk039From860.values ++
  MaximumCall595StructuredChunk040From860.values ++
  MaximumCall595StructuredChunk041From860.values ++
  MaximumCall595StructuredChunk042From860.values ++
  MaximumCall595StructuredChunk043From860.values ++
  MaximumCall595StructuredChunk044From860.values ++
  MaximumCall595StructuredChunk045From860.values ++
  MaximumCall595StructuredChunk046From860.values ++
  MaximumCall595StructuredChunk047From860.values ++
  MaximumCall595StructuredChunk048From860.values ++
  MaximumCall595StructuredChunk049From860.values ++
  MaximumCall595StructuredChunk050From860.values ++
  MaximumCall595StructuredChunk051From860.values ++
  MaximumCall595StructuredChunk052From860.values ++
  MaximumCall595StructuredChunk053From860.values ++
  MaximumCall595StructuredChunk054From860.values ++
  MaximumCall595StructuredChunk055From860.values ++
  MaximumCall595StructuredChunk056From860.values ++
  MaximumCall595StructuredChunk057From860.values ++
  MaximumCall595StructuredChunk058From860.values ++
  MaximumCall595StructuredChunk059From860.values ++
  MaximumCall595StructuredChunk060From860.values ++
  MaximumCall595StructuredChunk061From860.values ++
  MaximumCall595StructuredChunk062From860.values ++
  MaximumCall595StructuredChunk063From860.values ++
  MaximumCall595StructuredChunk064From860.values ++
  MaximumCall595StructuredChunk065From860.values ++
  MaximumCall595StructuredChunk066From860.values ++
  MaximumCall595StructuredChunk067From860.values ++
  MaximumCall595StructuredChunk068From860.values ++
  MaximumCall595StructuredChunk069From860.values ++
  MaximumCall595StructuredChunk070From860.values ++
  MaximumCall595StructuredChunk071From860.values ++
  MaximumCall595StructuredChunk072From860.values ++
  MaximumCall595StructuredChunk073From860.values ++
  MaximumCall595StructuredChunk074From860.values ++
  MaximumCall595StructuredChunk075From860.values ++
  MaximumCall595StructuredChunk076From860.values ++
  MaximumCall595StructuredChunk077From860.values ++
  MaximumCall595StructuredChunk078From860.values ++
  MaximumCall595StructuredChunk079From860.values ++
  MaximumCall595StructuredChunk080From860.values ++
  MaximumCall595StructuredChunk081From860.values ++
  MaximumCall595StructuredChunk082From860.values ++
  MaximumCall595StructuredChunk083From860.values ++
  MaximumCall595StructuredChunk084From860.values ++
  MaximumCall595StructuredChunk085From860.values ++
  MaximumCall595StructuredChunk086From860.values ++
  MaximumCall595StructuredChunk087From860.values ++
  MaximumCall595StructuredChunk088From860.values ++
  MaximumCall595StructuredChunk089From860.values ++
  MaximumCall595StructuredChunk090From860.values ++
  MaximumCall595StructuredChunk091From860.values ++
  MaximumCall595StructuredChunk092From860.values ++
  MaximumCall595StructuredChunk093From860.values ++
  MaximumCall595StructuredChunk094From860.values ++
  MaximumCall595StructuredChunk095From860.values ++
  MaximumCall595StructuredChunk096From860.values ++
  MaximumCall595StructuredChunk097From860.values ++
  MaximumCall595StructuredChunk098From860.values ++
  MaximumCall595StructuredChunk099From860.values ++
  MaximumCall595StructuredChunk100From860.values ++
  MaximumCall595StructuredChunk101From860.values ++
  MaximumCall595StructuredChunk102From860.values ++
  MaximumCall595StructuredChunk103From860.values ++
  MaximumCall595StructuredChunk104From860.values ++
  MaximumCall595StructuredChunk105From860.values ++
  MaximumCall595StructuredChunk106From860.values ++
  MaximumCall595StructuredChunk107From860.values ++
  MaximumCall595StructuredChunk108From860.values ++
  MaximumCall595StructuredChunk109From860.values ++
  MaximumCall595StructuredChunk110From860.values ++
  MaximumCall595StructuredChunk111From860.values ++
  MaximumCall595StructuredChunk112From860.values ++
  MaximumCall595StructuredChunk113From860.values ++
  MaximumCall595StructuredChunk114From860.values ++
  MaximumCall595StructuredChunk115From860.values ++
  MaximumCall595StructuredChunk116From860.values ++
  MaximumCall595StructuredChunk117From860.values ++
  MaximumCall595StructuredChunk118From860.values ++
  MaximumCall595StructuredChunk119From860.values ++
  MaximumCall595StructuredChunk120From860.values ++
  MaximumCall595StructuredChunk121From860.values ++
  MaximumCall595StructuredChunk122From860.values ++
  MaximumCall595StructuredChunk123From860.values ++
  MaximumCall595StructuredChunk124From860.values ++
  MaximumCall595StructuredChunk125From860.values ++
  MaximumCall595StructuredChunk126From860.values ++
  MaximumCall595StructuredChunk127From860.values ++
  MaximumCall595StructuredChunk128From860.values ++
  MaximumCall595StructuredChunk129From860.values ++
  MaximumCall595StructuredChunk130From860.values ++
  MaximumCall595StructuredChunk131From860.values ++
  MaximumCall595StructuredChunk132From860.values ++
  MaximumCall595StructuredChunk133From860.values ++
  MaximumCall595StructuredChunk134From860.values ++
  MaximumCall595StructuredChunk135From860.values ++
  MaximumCall595StructuredChunk136From860.values ++
  MaximumCall595StructuredChunk137From860.values ++
  MaximumCall595StructuredChunk138From860.values.

Lemma values_eq :
  List.map MaximumCall595StructuredContextFrom860.depth MaximumCall595StructuredContextFrom860.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 139
    MaximumCall595StructuredContextFrom860.depth MaximumCall595StructuredContextFrom860.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall595StructuredChunk000From860.values_eq,
      MaximumCall595StructuredChunk001From860.values_eq,
      MaximumCall595StructuredChunk002From860.values_eq,
      MaximumCall595StructuredChunk003From860.values_eq,
      MaximumCall595StructuredChunk004From860.values_eq,
      MaximumCall595StructuredChunk005From860.values_eq,
      MaximumCall595StructuredChunk006From860.values_eq,
      MaximumCall595StructuredChunk007From860.values_eq,
      MaximumCall595StructuredChunk008From860.values_eq,
      MaximumCall595StructuredChunk009From860.values_eq,
      MaximumCall595StructuredChunk010From860.values_eq,
      MaximumCall595StructuredChunk011From860.values_eq,
      MaximumCall595StructuredChunk012From860.values_eq,
      MaximumCall595StructuredChunk013From860.values_eq,
      MaximumCall595StructuredChunk014From860.values_eq,
      MaximumCall595StructuredChunk015From860.values_eq,
      MaximumCall595StructuredChunk016From860.values_eq,
      MaximumCall595StructuredChunk017From860.values_eq,
      MaximumCall595StructuredChunk018From860.values_eq,
      MaximumCall595StructuredChunk019From860.values_eq,
      MaximumCall595StructuredChunk020From860.values_eq,
      MaximumCall595StructuredChunk021From860.values_eq,
      MaximumCall595StructuredChunk022From860.values_eq,
      MaximumCall595StructuredChunk023From860.values_eq,
      MaximumCall595StructuredChunk024From860.values_eq,
      MaximumCall595StructuredChunk025From860.values_eq,
      MaximumCall595StructuredChunk026From860.values_eq,
      MaximumCall595StructuredChunk027From860.values_eq,
      MaximumCall595StructuredChunk028From860.values_eq,
      MaximumCall595StructuredChunk029From860.values_eq,
      MaximumCall595StructuredChunk030From860.values_eq,
      MaximumCall595StructuredChunk031From860.values_eq,
      MaximumCall595StructuredChunk032From860.values_eq,
      MaximumCall595StructuredChunk033From860.values_eq,
      MaximumCall595StructuredChunk034From860.values_eq,
      MaximumCall595StructuredChunk035From860.values_eq,
      MaximumCall595StructuredChunk036From860.values_eq,
      MaximumCall595StructuredChunk037From860.values_eq,
      MaximumCall595StructuredChunk038From860.values_eq,
      MaximumCall595StructuredChunk039From860.values_eq,
      MaximumCall595StructuredChunk040From860.values_eq,
      MaximumCall595StructuredChunk041From860.values_eq,
      MaximumCall595StructuredChunk042From860.values_eq,
      MaximumCall595StructuredChunk043From860.values_eq,
      MaximumCall595StructuredChunk044From860.values_eq,
      MaximumCall595StructuredChunk045From860.values_eq,
      MaximumCall595StructuredChunk046From860.values_eq,
      MaximumCall595StructuredChunk047From860.values_eq,
      MaximumCall595StructuredChunk048From860.values_eq,
      MaximumCall595StructuredChunk049From860.values_eq,
      MaximumCall595StructuredChunk050From860.values_eq,
      MaximumCall595StructuredChunk051From860.values_eq,
      MaximumCall595StructuredChunk052From860.values_eq,
      MaximumCall595StructuredChunk053From860.values_eq,
      MaximumCall595StructuredChunk054From860.values_eq,
      MaximumCall595StructuredChunk055From860.values_eq,
      MaximumCall595StructuredChunk056From860.values_eq,
      MaximumCall595StructuredChunk057From860.values_eq,
      MaximumCall595StructuredChunk058From860.values_eq,
      MaximumCall595StructuredChunk059From860.values_eq,
      MaximumCall595StructuredChunk060From860.values_eq,
      MaximumCall595StructuredChunk061From860.values_eq,
      MaximumCall595StructuredChunk062From860.values_eq,
      MaximumCall595StructuredChunk063From860.values_eq,
      MaximumCall595StructuredChunk064From860.values_eq,
      MaximumCall595StructuredChunk065From860.values_eq,
      MaximumCall595StructuredChunk066From860.values_eq,
      MaximumCall595StructuredChunk067From860.values_eq,
      MaximumCall595StructuredChunk068From860.values_eq,
      MaximumCall595StructuredChunk069From860.values_eq,
      MaximumCall595StructuredChunk070From860.values_eq,
      MaximumCall595StructuredChunk071From860.values_eq,
      MaximumCall595StructuredChunk072From860.values_eq,
      MaximumCall595StructuredChunk073From860.values_eq,
      MaximumCall595StructuredChunk074From860.values_eq,
      MaximumCall595StructuredChunk075From860.values_eq,
      MaximumCall595StructuredChunk076From860.values_eq,
      MaximumCall595StructuredChunk077From860.values_eq,
      MaximumCall595StructuredChunk078From860.values_eq,
      MaximumCall595StructuredChunk079From860.values_eq,
      MaximumCall595StructuredChunk080From860.values_eq,
      MaximumCall595StructuredChunk081From860.values_eq,
      MaximumCall595StructuredChunk082From860.values_eq,
      MaximumCall595StructuredChunk083From860.values_eq,
      MaximumCall595StructuredChunk084From860.values_eq,
      MaximumCall595StructuredChunk085From860.values_eq,
      MaximumCall595StructuredChunk086From860.values_eq,
      MaximumCall595StructuredChunk087From860.values_eq,
      MaximumCall595StructuredChunk088From860.values_eq,
      MaximumCall595StructuredChunk089From860.values_eq,
      MaximumCall595StructuredChunk090From860.values_eq,
      MaximumCall595StructuredChunk091From860.values_eq,
      MaximumCall595StructuredChunk092From860.values_eq,
      MaximumCall595StructuredChunk093From860.values_eq,
      MaximumCall595StructuredChunk094From860.values_eq,
      MaximumCall595StructuredChunk095From860.values_eq,
      MaximumCall595StructuredChunk096From860.values_eq,
      MaximumCall595StructuredChunk097From860.values_eq,
      MaximumCall595StructuredChunk098From860.values_eq,
      MaximumCall595StructuredChunk099From860.values_eq,
      MaximumCall595StructuredChunk100From860.values_eq,
      MaximumCall595StructuredChunk101From860.values_eq,
      MaximumCall595StructuredChunk102From860.values_eq,
      MaximumCall595StructuredChunk103From860.values_eq,
      MaximumCall595StructuredChunk104From860.values_eq,
      MaximumCall595StructuredChunk105From860.values_eq,
      MaximumCall595StructuredChunk106From860.values_eq,
      MaximumCall595StructuredChunk107From860.values_eq,
      MaximumCall595StructuredChunk108From860.values_eq,
      MaximumCall595StructuredChunk109From860.values_eq,
      MaximumCall595StructuredChunk110From860.values_eq,
      MaximumCall595StructuredChunk111From860.values_eq,
      MaximumCall595StructuredChunk112From860.values_eq,
      MaximumCall595StructuredChunk113From860.values_eq,
      MaximumCall595StructuredChunk114From860.values_eq,
      MaximumCall595StructuredChunk115From860.values_eq,
      MaximumCall595StructuredChunk116From860.values_eq,
      MaximumCall595StructuredChunk117From860.values_eq,
      MaximumCall595StructuredChunk118From860.values_eq,
      MaximumCall595StructuredChunk119From860.values_eq,
      MaximumCall595StructuredChunk120From860.values_eq,
      MaximumCall595StructuredChunk121From860.values_eq,
      MaximumCall595StructuredChunk122From860.values_eq,
      MaximumCall595StructuredChunk123From860.values_eq,
      MaximumCall595StructuredChunk124From860.values_eq,
      MaximumCall595StructuredChunk125From860.values_eq,
      MaximumCall595StructuredChunk126From860.values_eq,
      MaximumCall595StructuredChunk127From860.values_eq,
      MaximumCall595StructuredChunk128From860.values_eq,
      MaximumCall595StructuredChunk129From860.values_eq,
      MaximumCall595StructuredChunk130From860.values_eq,
      MaximumCall595StructuredChunk131From860.values_eq,
      MaximumCall595StructuredChunk132From860.values_eq,
      MaximumCall595StructuredChunk133From860.values_eq,
      MaximumCall595StructuredChunk134From860.values_eq,
      MaximumCall595StructuredChunk135From860.values_eq,
      MaximumCall595StructuredChunk136From860.values_eq,
      MaximumCall595StructuredChunk137From860.values_eq,
      MaximumCall595StructuredChunk138From860.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
