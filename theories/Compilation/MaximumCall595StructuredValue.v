From Galette Require Import Base.
From Stdlib Require Import List Lia.
From InitE.Compilation Require Import FastMaximum MaximumListChunks
  MaximumCall595StructuredContext MaximumCall595StructuredChunk000 MaximumCall595StructuredChunk001 MaximumCall595StructuredChunk002 MaximumCall595StructuredChunk003 MaximumCall595StructuredChunk004 MaximumCall595StructuredChunk005 MaximumCall595StructuredChunk006 MaximumCall595StructuredChunk007 MaximumCall595StructuredChunk008 MaximumCall595StructuredChunk009 MaximumCall595StructuredChunk010 MaximumCall595StructuredChunk011 MaximumCall595StructuredChunk012 MaximumCall595StructuredChunk013 MaximumCall595StructuredChunk014 MaximumCall595StructuredChunk015 MaximumCall595StructuredChunk016 MaximumCall595StructuredChunk017 MaximumCall595StructuredChunk018 MaximumCall595StructuredChunk019 MaximumCall595StructuredChunk020 MaximumCall595StructuredChunk021 MaximumCall595StructuredChunk022 MaximumCall595StructuredChunk023 MaximumCall595StructuredChunk024 MaximumCall595StructuredChunk025 MaximumCall595StructuredChunk026 MaximumCall595StructuredChunk027 MaximumCall595StructuredChunk028 MaximumCall595StructuredChunk029 MaximumCall595StructuredChunk030 MaximumCall595StructuredChunk031 MaximumCall595StructuredChunk032 MaximumCall595StructuredChunk033 MaximumCall595StructuredChunk034 MaximumCall595StructuredChunk035 MaximumCall595StructuredChunk036 MaximumCall595StructuredChunk037 MaximumCall595StructuredChunk038 MaximumCall595StructuredChunk039 MaximumCall595StructuredChunk040 MaximumCall595StructuredChunk041 MaximumCall595StructuredChunk042 MaximumCall595StructuredChunk043 MaximumCall595StructuredChunk044 MaximumCall595StructuredChunk045 MaximumCall595StructuredChunk046 MaximumCall595StructuredChunk047 MaximumCall595StructuredChunk048 MaximumCall595StructuredChunk049 MaximumCall595StructuredChunk050 MaximumCall595StructuredChunk051 MaximumCall595StructuredChunk052 MaximumCall595StructuredChunk053 MaximumCall595StructuredChunk054 MaximumCall595StructuredChunk055 MaximumCall595StructuredChunk056 MaximumCall595StructuredChunk057 MaximumCall595StructuredChunk058 MaximumCall595StructuredChunk059 MaximumCall595StructuredChunk060 MaximumCall595StructuredChunk061 MaximumCall595StructuredChunk062 MaximumCall595StructuredChunk063 MaximumCall595StructuredChunk064 MaximumCall595StructuredChunk065 MaximumCall595StructuredChunk066 MaximumCall595StructuredChunk067 MaximumCall595StructuredChunk068 MaximumCall595StructuredChunk069 MaximumCall595StructuredChunk070 MaximumCall595StructuredChunk071 MaximumCall595StructuredChunk072 MaximumCall595StructuredChunk073 MaximumCall595StructuredChunk074 MaximumCall595StructuredChunk075 MaximumCall595StructuredChunk076 MaximumCall595StructuredChunk077 MaximumCall595StructuredChunk078 MaximumCall595StructuredChunk079 MaximumCall595StructuredChunk080 MaximumCall595StructuredChunk081 MaximumCall595StructuredChunk082 MaximumCall595StructuredChunk083 MaximumCall595StructuredChunk084 MaximumCall595StructuredChunk085 MaximumCall595StructuredChunk086 MaximumCall595StructuredChunk087 MaximumCall595StructuredChunk088 MaximumCall595StructuredChunk089 MaximumCall595StructuredChunk090 MaximumCall595StructuredChunk091 MaximumCall595StructuredChunk092 MaximumCall595StructuredChunk093 MaximumCall595StructuredChunk094 MaximumCall595StructuredChunk095 MaximumCall595StructuredChunk096 MaximumCall595StructuredChunk097 MaximumCall595StructuredChunk098 MaximumCall595StructuredChunk099 MaximumCall595StructuredChunk100 MaximumCall595StructuredChunk101 MaximumCall595StructuredChunk102 MaximumCall595StructuredChunk103 MaximumCall595StructuredChunk104 MaximumCall595StructuredChunk105 MaximumCall595StructuredChunk106 MaximumCall595StructuredChunk107 MaximumCall595StructuredChunk108 MaximumCall595StructuredChunk109 MaximumCall595StructuredChunk110 MaximumCall595StructuredChunk111 MaximumCall595StructuredChunk112 MaximumCall595StructuredChunk113 MaximumCall595StructuredChunk114 MaximumCall595StructuredChunk115 MaximumCall595StructuredChunk116 MaximumCall595StructuredChunk117 MaximumCall595StructuredChunk118 MaximumCall595StructuredChunk119 MaximumCall595StructuredChunk120 MaximumCall595StructuredChunk121 MaximumCall595StructuredChunk122 MaximumCall595StructuredChunk123 MaximumCall595StructuredChunk124 MaximumCall595StructuredChunk125 MaximumCall595StructuredChunk126 MaximumCall595StructuredChunk127 MaximumCall595StructuredChunk128 MaximumCall595StructuredChunk129 MaximumCall595StructuredChunk130 MaximumCall595StructuredChunk131 MaximumCall595StructuredChunk132 MaximumCall595StructuredChunk133 MaximumCall595StructuredChunk134 MaximumCall595StructuredChunk135 MaximumCall595StructuredChunk136 MaximumCall595StructuredChunk137 MaximumCall595StructuredChunk138.

Definition values :=
  MaximumCall595StructuredChunk000.values ++
  MaximumCall595StructuredChunk001.values ++
  MaximumCall595StructuredChunk002.values ++
  MaximumCall595StructuredChunk003.values ++
  MaximumCall595StructuredChunk004.values ++
  MaximumCall595StructuredChunk005.values ++
  MaximumCall595StructuredChunk006.values ++
  MaximumCall595StructuredChunk007.values ++
  MaximumCall595StructuredChunk008.values ++
  MaximumCall595StructuredChunk009.values ++
  MaximumCall595StructuredChunk010.values ++
  MaximumCall595StructuredChunk011.values ++
  MaximumCall595StructuredChunk012.values ++
  MaximumCall595StructuredChunk013.values ++
  MaximumCall595StructuredChunk014.values ++
  MaximumCall595StructuredChunk015.values ++
  MaximumCall595StructuredChunk016.values ++
  MaximumCall595StructuredChunk017.values ++
  MaximumCall595StructuredChunk018.values ++
  MaximumCall595StructuredChunk019.values ++
  MaximumCall595StructuredChunk020.values ++
  MaximumCall595StructuredChunk021.values ++
  MaximumCall595StructuredChunk022.values ++
  MaximumCall595StructuredChunk023.values ++
  MaximumCall595StructuredChunk024.values ++
  MaximumCall595StructuredChunk025.values ++
  MaximumCall595StructuredChunk026.values ++
  MaximumCall595StructuredChunk027.values ++
  MaximumCall595StructuredChunk028.values ++
  MaximumCall595StructuredChunk029.values ++
  MaximumCall595StructuredChunk030.values ++
  MaximumCall595StructuredChunk031.values ++
  MaximumCall595StructuredChunk032.values ++
  MaximumCall595StructuredChunk033.values ++
  MaximumCall595StructuredChunk034.values ++
  MaximumCall595StructuredChunk035.values ++
  MaximumCall595StructuredChunk036.values ++
  MaximumCall595StructuredChunk037.values ++
  MaximumCall595StructuredChunk038.values ++
  MaximumCall595StructuredChunk039.values ++
  MaximumCall595StructuredChunk040.values ++
  MaximumCall595StructuredChunk041.values ++
  MaximumCall595StructuredChunk042.values ++
  MaximumCall595StructuredChunk043.values ++
  MaximumCall595StructuredChunk044.values ++
  MaximumCall595StructuredChunk045.values ++
  MaximumCall595StructuredChunk046.values ++
  MaximumCall595StructuredChunk047.values ++
  MaximumCall595StructuredChunk048.values ++
  MaximumCall595StructuredChunk049.values ++
  MaximumCall595StructuredChunk050.values ++
  MaximumCall595StructuredChunk051.values ++
  MaximumCall595StructuredChunk052.values ++
  MaximumCall595StructuredChunk053.values ++
  MaximumCall595StructuredChunk054.values ++
  MaximumCall595StructuredChunk055.values ++
  MaximumCall595StructuredChunk056.values ++
  MaximumCall595StructuredChunk057.values ++
  MaximumCall595StructuredChunk058.values ++
  MaximumCall595StructuredChunk059.values ++
  MaximumCall595StructuredChunk060.values ++
  MaximumCall595StructuredChunk061.values ++
  MaximumCall595StructuredChunk062.values ++
  MaximumCall595StructuredChunk063.values ++
  MaximumCall595StructuredChunk064.values ++
  MaximumCall595StructuredChunk065.values ++
  MaximumCall595StructuredChunk066.values ++
  MaximumCall595StructuredChunk067.values ++
  MaximumCall595StructuredChunk068.values ++
  MaximumCall595StructuredChunk069.values ++
  MaximumCall595StructuredChunk070.values ++
  MaximumCall595StructuredChunk071.values ++
  MaximumCall595StructuredChunk072.values ++
  MaximumCall595StructuredChunk073.values ++
  MaximumCall595StructuredChunk074.values ++
  MaximumCall595StructuredChunk075.values ++
  MaximumCall595StructuredChunk076.values ++
  MaximumCall595StructuredChunk077.values ++
  MaximumCall595StructuredChunk078.values ++
  MaximumCall595StructuredChunk079.values ++
  MaximumCall595StructuredChunk080.values ++
  MaximumCall595StructuredChunk081.values ++
  MaximumCall595StructuredChunk082.values ++
  MaximumCall595StructuredChunk083.values ++
  MaximumCall595StructuredChunk084.values ++
  MaximumCall595StructuredChunk085.values ++
  MaximumCall595StructuredChunk086.values ++
  MaximumCall595StructuredChunk087.values ++
  MaximumCall595StructuredChunk088.values ++
  MaximumCall595StructuredChunk089.values ++
  MaximumCall595StructuredChunk090.values ++
  MaximumCall595StructuredChunk091.values ++
  MaximumCall595StructuredChunk092.values ++
  MaximumCall595StructuredChunk093.values ++
  MaximumCall595StructuredChunk094.values ++
  MaximumCall595StructuredChunk095.values ++
  MaximumCall595StructuredChunk096.values ++
  MaximumCall595StructuredChunk097.values ++
  MaximumCall595StructuredChunk098.values ++
  MaximumCall595StructuredChunk099.values ++
  MaximumCall595StructuredChunk100.values ++
  MaximumCall595StructuredChunk101.values ++
  MaximumCall595StructuredChunk102.values ++
  MaximumCall595StructuredChunk103.values ++
  MaximumCall595StructuredChunk104.values ++
  MaximumCall595StructuredChunk105.values ++
  MaximumCall595StructuredChunk106.values ++
  MaximumCall595StructuredChunk107.values ++
  MaximumCall595StructuredChunk108.values ++
  MaximumCall595StructuredChunk109.values ++
  MaximumCall595StructuredChunk110.values ++
  MaximumCall595StructuredChunk111.values ++
  MaximumCall595StructuredChunk112.values ++
  MaximumCall595StructuredChunk113.values ++
  MaximumCall595StructuredChunk114.values ++
  MaximumCall595StructuredChunk115.values ++
  MaximumCall595StructuredChunk116.values ++
  MaximumCall595StructuredChunk117.values ++
  MaximumCall595StructuredChunk118.values ++
  MaximumCall595StructuredChunk119.values ++
  MaximumCall595StructuredChunk120.values ++
  MaximumCall595StructuredChunk121.values ++
  MaximumCall595StructuredChunk122.values ++
  MaximumCall595StructuredChunk123.values ++
  MaximumCall595StructuredChunk124.values ++
  MaximumCall595StructuredChunk125.values ++
  MaximumCall595StructuredChunk126.values ++
  MaximumCall595StructuredChunk127.values ++
  MaximumCall595StructuredChunk128.values ++
  MaximumCall595StructuredChunk129.values ++
  MaximumCall595StructuredChunk130.values ++
  MaximumCall595StructuredChunk131.values ++
  MaximumCall595StructuredChunk132.values ++
  MaximumCall595StructuredChunk133.values ++
  MaximumCall595StructuredChunk134.values ++
  MaximumCall595StructuredChunk135.values ++
  MaximumCall595StructuredChunk136.values ++
  MaximumCall595StructuredChunk137.values ++
  MaximumCall595StructuredChunk138.values.

Lemma values_eq :
  List.map MaximumCall595StructuredContext.depth MaximumCall595StructuredContext.leaves = values.
Proof.
  rewrite <- (MaximumListChunks.gather_exact 139
    MaximumCall595StructuredContext.depth MaximumCall595StructuredContext.leaves).
  - unfold MaximumListChunks.gather.
    cbn [List.seq List.map List.concat].
    rewrite MaximumCall595StructuredChunk000.values_eq,
      MaximumCall595StructuredChunk001.values_eq,
      MaximumCall595StructuredChunk002.values_eq,
      MaximumCall595StructuredChunk003.values_eq,
      MaximumCall595StructuredChunk004.values_eq,
      MaximumCall595StructuredChunk005.values_eq,
      MaximumCall595StructuredChunk006.values_eq,
      MaximumCall595StructuredChunk007.values_eq,
      MaximumCall595StructuredChunk008.values_eq,
      MaximumCall595StructuredChunk009.values_eq,
      MaximumCall595StructuredChunk010.values_eq,
      MaximumCall595StructuredChunk011.values_eq,
      MaximumCall595StructuredChunk012.values_eq,
      MaximumCall595StructuredChunk013.values_eq,
      MaximumCall595StructuredChunk014.values_eq,
      MaximumCall595StructuredChunk015.values_eq,
      MaximumCall595StructuredChunk016.values_eq,
      MaximumCall595StructuredChunk017.values_eq,
      MaximumCall595StructuredChunk018.values_eq,
      MaximumCall595StructuredChunk019.values_eq,
      MaximumCall595StructuredChunk020.values_eq,
      MaximumCall595StructuredChunk021.values_eq,
      MaximumCall595StructuredChunk022.values_eq,
      MaximumCall595StructuredChunk023.values_eq,
      MaximumCall595StructuredChunk024.values_eq,
      MaximumCall595StructuredChunk025.values_eq,
      MaximumCall595StructuredChunk026.values_eq,
      MaximumCall595StructuredChunk027.values_eq,
      MaximumCall595StructuredChunk028.values_eq,
      MaximumCall595StructuredChunk029.values_eq,
      MaximumCall595StructuredChunk030.values_eq,
      MaximumCall595StructuredChunk031.values_eq,
      MaximumCall595StructuredChunk032.values_eq,
      MaximumCall595StructuredChunk033.values_eq,
      MaximumCall595StructuredChunk034.values_eq,
      MaximumCall595StructuredChunk035.values_eq,
      MaximumCall595StructuredChunk036.values_eq,
      MaximumCall595StructuredChunk037.values_eq,
      MaximumCall595StructuredChunk038.values_eq,
      MaximumCall595StructuredChunk039.values_eq,
      MaximumCall595StructuredChunk040.values_eq,
      MaximumCall595StructuredChunk041.values_eq,
      MaximumCall595StructuredChunk042.values_eq,
      MaximumCall595StructuredChunk043.values_eq,
      MaximumCall595StructuredChunk044.values_eq,
      MaximumCall595StructuredChunk045.values_eq,
      MaximumCall595StructuredChunk046.values_eq,
      MaximumCall595StructuredChunk047.values_eq,
      MaximumCall595StructuredChunk048.values_eq,
      MaximumCall595StructuredChunk049.values_eq,
      MaximumCall595StructuredChunk050.values_eq,
      MaximumCall595StructuredChunk051.values_eq,
      MaximumCall595StructuredChunk052.values_eq,
      MaximumCall595StructuredChunk053.values_eq,
      MaximumCall595StructuredChunk054.values_eq,
      MaximumCall595StructuredChunk055.values_eq,
      MaximumCall595StructuredChunk056.values_eq,
      MaximumCall595StructuredChunk057.values_eq,
      MaximumCall595StructuredChunk058.values_eq,
      MaximumCall595StructuredChunk059.values_eq,
      MaximumCall595StructuredChunk060.values_eq,
      MaximumCall595StructuredChunk061.values_eq,
      MaximumCall595StructuredChunk062.values_eq,
      MaximumCall595StructuredChunk063.values_eq,
      MaximumCall595StructuredChunk064.values_eq,
      MaximumCall595StructuredChunk065.values_eq,
      MaximumCall595StructuredChunk066.values_eq,
      MaximumCall595StructuredChunk067.values_eq,
      MaximumCall595StructuredChunk068.values_eq,
      MaximumCall595StructuredChunk069.values_eq,
      MaximumCall595StructuredChunk070.values_eq,
      MaximumCall595StructuredChunk071.values_eq,
      MaximumCall595StructuredChunk072.values_eq,
      MaximumCall595StructuredChunk073.values_eq,
      MaximumCall595StructuredChunk074.values_eq,
      MaximumCall595StructuredChunk075.values_eq,
      MaximumCall595StructuredChunk076.values_eq,
      MaximumCall595StructuredChunk077.values_eq,
      MaximumCall595StructuredChunk078.values_eq,
      MaximumCall595StructuredChunk079.values_eq,
      MaximumCall595StructuredChunk080.values_eq,
      MaximumCall595StructuredChunk081.values_eq,
      MaximumCall595StructuredChunk082.values_eq,
      MaximumCall595StructuredChunk083.values_eq,
      MaximumCall595StructuredChunk084.values_eq,
      MaximumCall595StructuredChunk085.values_eq,
      MaximumCall595StructuredChunk086.values_eq,
      MaximumCall595StructuredChunk087.values_eq,
      MaximumCall595StructuredChunk088.values_eq,
      MaximumCall595StructuredChunk089.values_eq,
      MaximumCall595StructuredChunk090.values_eq,
      MaximumCall595StructuredChunk091.values_eq,
      MaximumCall595StructuredChunk092.values_eq,
      MaximumCall595StructuredChunk093.values_eq,
      MaximumCall595StructuredChunk094.values_eq,
      MaximumCall595StructuredChunk095.values_eq,
      MaximumCall595StructuredChunk096.values_eq,
      MaximumCall595StructuredChunk097.values_eq,
      MaximumCall595StructuredChunk098.values_eq,
      MaximumCall595StructuredChunk099.values_eq,
      MaximumCall595StructuredChunk100.values_eq,
      MaximumCall595StructuredChunk101.values_eq,
      MaximumCall595StructuredChunk102.values_eq,
      MaximumCall595StructuredChunk103.values_eq,
      MaximumCall595StructuredChunk104.values_eq,
      MaximumCall595StructuredChunk105.values_eq,
      MaximumCall595StructuredChunk106.values_eq,
      MaximumCall595StructuredChunk107.values_eq,
      MaximumCall595StructuredChunk108.values_eq,
      MaximumCall595StructuredChunk109.values_eq,
      MaximumCall595StructuredChunk110.values_eq,
      MaximumCall595StructuredChunk111.values_eq,
      MaximumCall595StructuredChunk112.values_eq,
      MaximumCall595StructuredChunk113.values_eq,
      MaximumCall595StructuredChunk114.values_eq,
      MaximumCall595StructuredChunk115.values_eq,
      MaximumCall595StructuredChunk116.values_eq,
      MaximumCall595StructuredChunk117.values_eq,
      MaximumCall595StructuredChunk118.values_eq,
      MaximumCall595StructuredChunk119.values_eq,
      MaximumCall595StructuredChunk120.values_eq,
      MaximumCall595StructuredChunk121.values_eq,
      MaximumCall595StructuredChunk122.values_eq,
      MaximumCall595StructuredChunk123.values_eq,
      MaximumCall595StructuredChunk124.values_eq,
      MaximumCall595StructuredChunk125.values_eq,
      MaximumCall595StructuredChunk126.values_eq,
      MaximumCall595StructuredChunk127.values_eq,
      MaximumCall595StructuredChunk128.values_eq,
      MaximumCall595StructuredChunk129.values_eq,
      MaximumCall595StructuredChunk130.values_eq,
      MaximumCall595StructuredChunk131.values_eq,
      MaximumCall595StructuredChunk132.values_eq,
      MaximumCall595StructuredChunk133.values_eq,
      MaximumCall595StructuredChunk134.values_eq,
      MaximumCall595StructuredChunk135.values_eq,
      MaximumCall595StructuredChunk136.values_eq,
      MaximumCall595StructuredChunk137.values_eq,
      MaximumCall595StructuredChunk138.values_eq.
    reflexivity.
  - vm_compute. lia.
Qed.

Definition depth_value :=
  fold_right FastMaximum.join_depth (Some 0) values.
