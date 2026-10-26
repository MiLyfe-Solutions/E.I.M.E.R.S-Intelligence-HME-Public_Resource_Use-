import V185TrunkScan21Chunk018

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_229488 : List Nat := [2, 1, 1, 1, 5, 2, 2, 3, 4]
def baseStart_229488 : Nat := 118140960795 + 229488 * 2 ^ 59
def prefixEnd_229488 : Nat := 4983230072969 + 3 ^ 40 * 229488 * 2
def baseEnd_229488 : Nat := 52372288195157049264271

theorem tailTrace_229488 : CollatzResearch.WordTrace tailWord_229488 prefixEnd_229488 52372288195157049264271 := by
  unfold tailWord_229488
  simp only [CollatzResearch.WordTrace]
  refine ⟨4185057496305822137580559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5580076661741096183440745 4185057496305822137580559)
  ·
    refine ⟨6277586244458733206370839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4185057496305822137580559 6277586244458733206370839)
    ·
      refine ⟨9416379366688099809556259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6277586244458733206370839 9416379366688099809556259)
      ·
        refine ⟨14124569050032149714334389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9416379366688099809556259 14124569050032149714334389)
        ·
          refine ⟨1324178348440514035718849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14124569050032149714334389 1324178348440514035718849)
          ·
            refine ⟨993133761330385526789137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1324178348440514035718849 993133761330385526789137)
            ·
              refine ⟨744850320997789145091853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993133761330385526789137 744850320997789145091853)
              ·
                refine ⟨279318870374170929409445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 744850320997789145091853 279318870374170929409445)
                ·
                  refine ⟨52372288195157049264271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279318870374170929409445 52372288195157049264271)
                  ·
                    rfl

theorem cell21_229488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_229488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229488 prefixEnd_229488 := by exact prefixLift 229488
  have htrace : WordTrace (prefixWord ++ tailWord_229488) baseStart_229488 baseEnd_229488 := by
    simpa [prefixWord, tailWord_229488, baseEnd_229488] using wordTrace_append hprefix tailTrace_229488
  have hstable : (prefixWord ++ tailWord_229488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229488).length < 2 ^ (prefixWord ++ tailWord_229488).sum := by decide
  have hdescent : baseEnd_229488 < baseStart_229488 := by decide
  rcases family_descends (prefixWord ++ tailWord_229488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229533 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 5]
def baseStart_229533 : Nat := 118140960795 + 229533 * 2 ^ 59
def prefixEnd_229533 : Nat := 4983230072969 + 3 ^ 40 * 229533 * 2
def baseEnd_229533 : Nat := 52382557808246971014179

theorem tailTrace_229533 : CollatzResearch.WordTrace tailWord_229533 prefixEnd_229533 52382557808246971014179 := by
  unfold tailWord_229533
  simp only [CollatzResearch.WordTrace]
  refine ⟨8371756277448616960549253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5581170851632411307032835 8371756277448616960549253)
  ·
    refine ⟨1569704302021615680102985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8371756277448616960549253 1569704302021615680102985)
    ·
      refine ⟨1177278226516211760077239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1569704302021615680102985 1177278226516211760077239)
      ·
        refine ⟨1765917339774317640115859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177278226516211760077239 1765917339774317640115859)
        ·
          refine ⟨2648876009661476460173789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765917339774317640115859 2648876009661476460173789)
          ·
            refine ⟨993328503623053672565171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2648876009661476460173789 993328503623053672565171)
            ·
              refine ⟨1489992755434580508847757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993328503623053672565171 1489992755434580508847757)
              ·
                refine ⟨558747283287967690817909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1489992755434580508847757 558747283287967690817909)
                ·
                  refine ⟨52382557808246971014179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 558747283287967690817909 52382557808246971014179)
                  ·
                    rfl

theorem cell21_229533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_229533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229533 prefixEnd_229533 := by exact prefixLift 229533
  have htrace : WordTrace (prefixWord ++ tailWord_229533) baseStart_229533 baseEnd_229533 := by
    simpa [prefixWord, tailWord_229533, baseEnd_229533] using wordTrace_append hprefix tailTrace_229533
  have hstable : (prefixWord ++ tailWord_229533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229533).length < 2 ^ (prefixWord ++ tailWord_229533).sum := by decide
  have hdescent : baseEnd_229533 < baseStart_229533 := by decide
  rcases family_descends (prefixWord ++ tailWord_229533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229553 : List Nat := [1, 2, 2, 5, 3, 1, 2, 5]
def baseStart_229553 : Nat := 118140960795 + 229553 * 2 ^ 59
def prefixEnd_229553 : Nat := 4983230072969 + 3 ^ 40 * 229553 * 2
def baseEnd_229553 : Nat := 17462374026910460226935

theorem tailTrace_229553 : CollatzResearch.WordTrace tailWord_229553 prefixEnd_229553 17462374026910460226935 := by
  unfold tailWord_229553
  simp only [CollatzResearch.WordTrace]
  refine ⟨8372485737376160376277313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5581657158250773584184875 8372485737376160376277313)
  ·
    refine ⟨6279364303032120282207985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8372485737376160376277313 6279364303032120282207985)
    ·
      refine ⟨4709523227274090211655989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6279364303032120282207985 4709523227274090211655989)
      ·
        refine ⟨441517802556945957342749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4709523227274090211655989 441517802556945957342749)
        ·
          refine ⟨165569175958854734003531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441517802556945957342749 165569175958854734003531)
          ·
            refine ⟨248353763938282101005297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165569175958854734003531 248353763938282101005297)
            ·
              refine ⟨186265322953711575753973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248353763938282101005297 186265322953711575753973)
              ·
                refine ⟨17462374026910460226935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186265322953711575753973 17462374026910460226935)
                ·
                  rfl

theorem cell21_229553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 5].length) (baseStart_229553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229553 prefixEnd_229553 := by exact prefixLift 229553
  have htrace : WordTrace (prefixWord ++ tailWord_229553) baseStart_229553 baseEnd_229553 := by
    simpa [prefixWord, tailWord_229553, baseEnd_229553] using wordTrace_append hprefix tailTrace_229553
  have hstable : (prefixWord ++ tailWord_229553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229553).length < 2 ^ (prefixWord ++ tailWord_229553).sum := by decide
  have hdescent : baseEnd_229553 < baseStart_229553 := by decide
  rcases family_descends (prefixWord ++ tailWord_229553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229640 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 4]
def baseStart_229640 : Nat := 118140960795 + 229640 * 2 ^ 59
def prefixEnd_229640 : Nat := 4983230072969 + 3 ^ 40 * 229640 * 2
def baseEnd_229640 : Nat := 52406976666038562730627

theorem tailTrace_229640 : CollatzResearch.WordTrace tailWord_229640 prefixEnd_229640 52406976666038562730627 := by
  unfold tailWord_229640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4187829444030487117347187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5583772592040649489796249 4187829444030487117347187)
  ·
    refine ⟨6281744166045730676020781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4187829444030487117347187 6281744166045730676020781)
    ·
      refine ⟨2355654062267149003507793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6281744166045730676020781 2355654062267149003507793)
      ·
        refine ⟨1766740546700361752630845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2355654062267149003507793 1766740546700361752630845)
        ·
          refine ⟨662527705012635657236567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1766740546700361752630845 662527705012635657236567)
          ·
            refine ⟨993791557518953485854851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662527705012635657236567 993791557518953485854851)
            ·
              refine ⟨1490687336278430228782277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993791557518953485854851 1490687336278430228782277)
              ·
                refine ⟨279503875552205667896677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1490687336278430228782277 279503875552205667896677)
                ·
                  refine ⟨52406976666038562730627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279503875552205667896677 52406976666038562730627)
                  ·
                    rfl

theorem cell21_229640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_229640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229640 prefixEnd_229640 := by exact prefixLift 229640
  have htrace : WordTrace (prefixWord ++ tailWord_229640) baseStart_229640 baseEnd_229640 := by
    simpa [prefixWord, tailWord_229640, baseEnd_229640] using wordTrace_append hprefix tailTrace_229640
  have hstable : (prefixWord ++ tailWord_229640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229640).length < 2 ^ (prefixWord ++ tailWord_229640).sum := by decide
  have hdescent : baseEnd_229640 < baseStart_229640 := by decide
  rcases family_descends (prefixWord ++ tailWord_229640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229899 : List Nat := [1, 1, 1, 1, 7, 3, 2, 5]
def baseStart_229899 : Nat := 118140960795 + 229899 * 2 ^ 59
def prefixEnd_229899 : Nat := 4983230072969 + 3 ^ 40 * 229899 * 2
def baseEnd_229899 : Nat := 17488694664903889304477

theorem tailTrace_229899 : CollatzResearch.WordTrace tailWord_229899 prefixEnd_229899 17488694664903889304477 := by
  unfold tailWord_229899
  simp only [CollatzResearch.WordTrace]
  refine ⟨8385105394122661468372751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5590070262748440978915167 8385105394122661468372751)
  ·
    refine ⟨12577658091183992202559127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8385105394122661468372751 12577658091183992202559127)
    ·
      refine ⟨18866487136775988303838691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12577658091183992202559127 18866487136775988303838691)
      ·
        refine ⟨28299730705163982455758037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18866487136775988303838691 28299730705163982455758037)
        ·
          refine ⟨663274938402280838806829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 28299730705163982455758037 663274938402280838806829)
          ·
            refine ⟨248728101900855314552561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 663274938402280838806829 248728101900855314552561)
            ·
              refine ⟨186546076425641485914421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248728101900855314552561 186546076425641485914421)
              ·
                refine ⟨17488694664903889304477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186546076425641485914421 17488694664903889304477)
                ·
                  rfl

theorem cell21_229899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 5].length) (baseStart_229899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229899 prefixEnd_229899 := by exact prefixLift 229899
  have htrace : WordTrace (prefixWord ++ tailWord_229899) baseStart_229899 baseEnd_229899 := by
    simpa [prefixWord, tailWord_229899, baseEnd_229899] using wordTrace_append hprefix tailTrace_229899
  have hstable : (prefixWord ++ tailWord_229899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229899).length < 2 ^ (prefixWord ++ tailWord_229899).sum := by decide
  have hdescent : baseEnd_229899 < baseStart_229899 := by decide
  rcases family_descends (prefixWord ++ tailWord_229899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229930 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_229930 : Nat := 118140960795 + 229930 * 2 ^ 59
def prefixEnd_229930 : Nat := 4983230072969 + 3 ^ 40 * 229930 * 2
def baseEnd_229930 : Nat := 52473158617062502896701

theorem tailTrace_229930 : CollatzResearch.WordTrace tailWord_229930 prefixEnd_229930 52473158617062502896701 := by
  unfold tailWord_229930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2096559014252588440687811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5590824038006902508500829 2096559014252588440687811)
  ·
    refine ⟨3144838521378882661031717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2096559014252588440687811 3144838521378882661031717)
    ·
      refine ⟨589657222758540498943447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3144838521378882661031717 589657222758540498943447)
      ·
        refine ⟨884485834137810748415171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589657222758540498943447 884485834137810748415171)
        ·
          refine ⟨1326728751206716122622757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884485834137810748415171 1326728751206716122622757)
          ·
            refine ⟨248761640851259272991767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1326728751206716122622757 248761640851259272991767)
            ·
              refine ⟨373142461276888909487651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248761640851259272991767 373142461276888909487651)
              ·
                refine ⟨559713691915333364231477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373142461276888909487651 559713691915333364231477)
                ·
                  refine ⟨52473158617062502896701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 559713691915333364231477 52473158617062502896701)
                  ·
                    rfl

theorem cell21_229930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_229930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229930 prefixEnd_229930 := by exact prefixLift 229930
  have htrace : WordTrace (prefixWord ++ tailWord_229930) baseStart_229930 baseEnd_229930 := by
    simpa [prefixWord, tailWord_229930, baseEnd_229930] using wordTrace_append hprefix tailTrace_229930
  have hstable : (prefixWord ++ tailWord_229930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229930).length < 2 ^ (prefixWord ++ tailWord_229930).sum := by decide
  have hdescent : baseEnd_229930 < baseStart_229930 := by decide
  rcases family_descends (prefixWord ++ tailWord_229930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229933 : List Nat := [1, 5, 4, 1, 1, 1, 2, 6]
def baseStart_229933 : Nat := 118140960795 + 229933 * 2 ^ 59
def prefixEnd_229933 : Nat := 4983230072969 + 3 ^ 40 * 229933 * 2
def baseEnd_229933 : Nat := 17491281085978388115565

theorem tailTrace_229933 : CollatzResearch.WordTrace tailWord_229933 prefixEnd_229933 17491281085978388115565 := by
  unfold tailWord_229933
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386345475999485275110453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5590896983999656850073635 8386345475999485275110453)
  ·
    refine ⟨786219888374951744541605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8386345475999485275110453 786219888374951744541605)
    ·
      refine ⟨147416229070303452101551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 786219888374951744541605 147416229070303452101551)
      ·
        refine ⟨221124343605455178152327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147416229070303452101551 221124343605455178152327)
        ·
          refine ⟨331686515408182767228491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221124343605455178152327 331686515408182767228491)
          ·
            refine ⟨497529773112274150842737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331686515408182767228491 497529773112274150842737)
            ·
              refine ⟨373147329834205613132053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497529773112274150842737 373147329834205613132053)
              ·
                refine ⟨17491281085978388115565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 373147329834205613132053 17491281085978388115565)
                ·
                  rfl

theorem cell21_229933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 6].length) (baseStart_229933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229933 prefixEnd_229933 := by exact prefixLift 229933
  have htrace : WordTrace (prefixWord ++ tailWord_229933) baseStart_229933 baseEnd_229933 := by
    simpa [prefixWord, tailWord_229933, baseEnd_229933] using wordTrace_append hprefix tailTrace_229933
  have hstable : (prefixWord ++ tailWord_229933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229933).length < 2 ^ (prefixWord ++ tailWord_229933).sum := by decide
  have hdescent : baseEnd_229933 < baseStart_229933 := by decide
  rcases family_descends (prefixWord ++ tailWord_229933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_229992 : List Nat := [2, 1, 4, 3, 3, 1, 1, 6]
def baseStart_229992 : Nat := 118140960795 + 229992 * 2 ^ 59
def prefixEnd_229992 : Nat := 4983230072969 + 3 ^ 40 * 229992 * 2
def baseEnd_229992 : Nat := 17495769287254724287747

theorem tailTrace_229992 : CollatzResearch.WordTrace tailWord_229992 prefixEnd_229992 17495769287254724287747 := by
  unfold tailWord_229992
  simp only [CollatzResearch.WordTrace]
  refine ⟨4194248691392869175754115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5592331588523825567672153 4194248691392869175754115)
  ·
    refine ⟨6291373037089303763631173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4194248691392869175754115 6291373037089303763631173)
    ·
      refine ⟨1179632444454244455680845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6291373037089303763631173 1179632444454244455680845)
      ·
        refine ⟨442362166670341670880317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1179632444454244455680845 442362166670341670880317)
        ·
          refine ⟨165885812501378126580119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442362166670341670880317 165885812501378126580119)
          ·
            refine ⟨248828718752067189870179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165885812501378126580119 248828718752067189870179)
            ·
              refine ⟨373243078128100784805269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248828718752067189870179 373243078128100784805269)
              ·
                refine ⟨17495769287254724287747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 373243078128100784805269 17495769287254724287747)
                ·
                  rfl

theorem cell21_229992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 6].length) (baseStart_229992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_229992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_229992 prefixEnd_229992 := by exact prefixLift 229992
  have htrace : WordTrace (prefixWord ++ tailWord_229992) baseStart_229992 baseEnd_229992 := by
    simpa [prefixWord, tailWord_229992, baseEnd_229992] using wordTrace_append hprefix tailTrace_229992
  have hstable : (prefixWord ++ tailWord_229992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_229992).length < 2 ^ (prefixWord ++ tailWord_229992).sum := by decide
  have hdescent : baseEnd_229992 < baseStart_229992 := by decide
  rcases family_descends (prefixWord ++ tailWord_229992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230006 : List Nat := [5, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_230006 : Nat := 118140960795 + 230006 * 2 ^ 59
def prefixEnd_230006 : Nat := 4983230072969 + 3 ^ 40 * 230006 * 2
def baseEnd_230006 : Nat := 52490502852503259629879

theorem tailTrace_230006 : CollatzResearch.WordTrace tailWord_230006 prefixEnd_230006 52490502852503259629879 := by
  unfold tailWord_230006
  simp only [CollatzResearch.WordTrace]
  refine ⟨524313000295938671407367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5592672003156679161678581 524313000295938671407367)
  ·
    refine ⟨786469500443908007111051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524313000295938671407367 786469500443908007111051)
    ·
      refine ⟨1179704250665862010666577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 786469500443908007111051 1179704250665862010666577)
      ·
        refine ⟨884778187999396507999933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1179704250665862010666577 884778187999396507999933)
        ·
          refine ⟨331791820499773690499975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 884778187999396507999933 331791820499773690499975)
          ·
            refine ⟨497687730749660535749963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331791820499773690499975 497687730749660535749963)
            ·
              refine ⟨746531596124490803624945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497687730749660535749963 746531596124490803624945)
              ·
                refine ⟨559898697093368102718709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746531596124490803624945 559898697093368102718709)
                ·
                  refine ⟨52490502852503259629879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 559898697093368102718709 52490502852503259629879)
                  ·
                    rfl

theorem cell21_230006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_230006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230006 prefixEnd_230006 := by exact prefixLift 230006
  have htrace : WordTrace (prefixWord ++ tailWord_230006) baseStart_230006 baseEnd_230006 := by
    simpa [prefixWord, tailWord_230006, baseEnd_230006] using wordTrace_append hprefix tailTrace_230006
  have hstable : (prefixWord ++ tailWord_230006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230006).length < 2 ^ (prefixWord ++ tailWord_230006).sum := by decide
  have hdescent : baseEnd_230006 < baseStart_230006 := by decide
  rcases family_descends (prefixWord ++ tailWord_230006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230034 : List Nat := [3, 2, 3, 1, 2, 2, 8]
def baseStart_230034 : Nat := 118140960795 + 230034 * 2 ^ 59
def prefixEnd_230034 : Nat := 4983230072969 + 3 ^ 40 * 230034 * 2
def baseEnd_230034 : Nat := 5832988092664603684795

theorem tailTrace_230034 : CollatzResearch.WordTrace tailWord_230034 prefixEnd_230034 5832988092664603684795 := by
  unfold tailWord_230034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2097507312158394881134289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5593352832422386349691437 2097507312158394881134289)
  ·
    refine ⟨1573130484118796160850717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2097507312158394881134289 1573130484118796160850717)
    ·
      refine ⟨589923931544548560319019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1573130484118796160850717 589923931544548560319019)
      ·
        refine ⟨884885897316822840478529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589923931544548560319019 884885897316822840478529)
        ·
          refine ⟨663664422987617130358897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884885897316822840478529 663664422987617130358897)
          ·
            refine ⟨497748317240712847769173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663664422987617130358897 497748317240712847769173)
            ·
              refine ⟨5832988092664603684795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 497748317240712847769173 5832988092664603684795)
              ·
                rfl

theorem cell21_230034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 8].length) (baseStart_230034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230034 prefixEnd_230034 := by exact prefixLift 230034
  have htrace : WordTrace (prefixWord ++ tailWord_230034) baseStart_230034 baseEnd_230034 := by
    simpa [prefixWord, tailWord_230034, baseEnd_230034] using wordTrace_append hprefix tailTrace_230034
  have hstable : (prefixWord ++ tailWord_230034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230034).length < 2 ^ (prefixWord ++ tailWord_230034).sum := by decide
  have hdescent : baseEnd_230034 < baseStart_230034 := by decide
  rcases family_descends (prefixWord ++ tailWord_230034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230107 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 11]
def baseStart_230107 : Nat := 118140960795 + 230107 * 2 ^ 59
def prefixEnd_230107 : Nat := 4983230072969 + 3 ^ 40 * 230107 * 2
def baseEnd_230107 : Nat := 52513552428549528446339

theorem tailTrace_230107 : CollatzResearch.WordTrace tailWord_230107 prefixEnd_230107 52513552428549528446339 := by
  unfold tailWord_230107
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392691777369112991944575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5595127851579408661296383 8392691777369112991944575)
  ·
    refine ⟨12589037666053669487916863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8392691777369112991944575 12589037666053669487916863)
    ·
      refine ⟨18883556499080504231875295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12589037666053669487916863 18883556499080504231875295)
      ·
        refine ⟨28325334748620756347812943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18883556499080504231875295 28325334748620756347812943)
        ·
          refine ⟨42488002122931134521719415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28325334748620756347812943 42488002122931134521719415)
          ·
            refine ⟨63732003184396701782579123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42488002122931134521719415 63732003184396701782579123)
            ·
              refine ⟨95598004776595052673868685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63732003184396701782579123 95598004776595052673868685)
              ·
                refine ⟨35849251791223144752700757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95598004776595052673868685 35849251791223144752700757)
                ·
                  refine ⟨52513552428549528446339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 35849251791223144752700757 52513552428549528446339)
                  ·
                    rfl

theorem cell21_230107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_230107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230107 prefixEnd_230107 := by exact prefixLift 230107
  have htrace : WordTrace (prefixWord ++ tailWord_230107) baseStart_230107 baseEnd_230107 := by
    simpa [prefixWord, tailWord_230107, baseEnd_230107] using wordTrace_append hprefix tailTrace_230107
  have hstable : (prefixWord ++ tailWord_230107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230107).length < 2 ^ (prefixWord ++ tailWord_230107).sum := by decide
  have hdescent : baseEnd_230107 < baseStart_230107 := by decide
  rcases family_descends (prefixWord ++ tailWord_230107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230113 : List Nat := [1, 2, 3, 1, 4, 3, 2, 1, 4]
def baseStart_230113 : Nat := 118140960795 + 230113 * 2 ^ 59
def prefixEnd_230113 : Nat := 4983230072969 + 3 ^ 40 * 230113 * 2
def baseEnd_230113 : Nat := 52514921710294851346327

theorem tailTrace_230113 : CollatzResearch.WordTrace tailWord_230113 prefixEnd_230113 52514921710294851346327 := by
  unfold tailWord_230113
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392910615347376016662993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5595273743564917344441995 8392910615347376016662993)
  ·
    refine ⟨6294682961510532012497245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8392910615347376016662993 6294682961510532012497245)
    ·
      refine ⟨2360506110566449504686467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6294682961510532012497245 2360506110566449504686467)
      ·
        refine ⟨3540759165849674257029701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360506110566449504686467 3540759165849674257029701)
        ·
          refine ⟨663892343596813923193069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3540759165849674257029701 663892343596813923193069)
          ·
            refine ⟨248959628848805221197401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 663892343596813923193069 248959628848805221197401)
            ·
              refine ⟨186719721636603915898051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248959628848805221197401 186719721636603915898051)
              ·
                refine ⟨280079582454905873847077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186719721636603915898051 280079582454905873847077)
                ·
                  refine ⟨52514921710294851346327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280079582454905873847077 52514921710294851346327)
                  ·
                    rfl

theorem cell21_230113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_230113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230113 prefixEnd_230113 := by exact prefixLift 230113
  have htrace : WordTrace (prefixWord ++ tailWord_230113) baseStart_230113 baseEnd_230113 := by
    simpa [prefixWord, tailWord_230113, baseEnd_230113] using wordTrace_append hprefix tailTrace_230113
  have hstable : (prefixWord ++ tailWord_230113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230113).length < 2 ^ (prefixWord ++ tailWord_230113).sum := by decide
  have hdescent : baseEnd_230113 < baseStart_230113 := by decide
  rcases family_descends (prefixWord ++ tailWord_230113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230138 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_230138 : Nat := 118140960795 + 230138 * 2 ^ 59
def prefixEnd_230138 : Nat := 4983230072969 + 3 ^ 40 * 230138 * 2
def baseEnd_230138 : Nat := 52520627050900363429609

theorem tailTrace_230138 : CollatzResearch.WordTrace tailWord_230138 prefixEnd_230138 52520627050900363429609 := by
  unfold tailWord_230138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098455610064201321580767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5595881626837870190882045 2098455610064201321580767)
  ·
    refine ⟨3147683415096301982371151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2098455610064201321580767 3147683415096301982371151)
    ·
      refine ⟨4721525122644452973556727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3147683415096301982371151 4721525122644452973556727)
      ·
        refine ⟨7082287683966679460335091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4721525122644452973556727 7082287683966679460335091)
        ·
          refine ⟨10623431525950019190502637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7082287683966679460335091 10623431525950019190502637)
          ·
            refine ⟨3983786822231257196438489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10623431525950019190502637 3983786822231257196438489)
            ·
              refine ⟨2987840116673442897328867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3983786822231257196438489 2987840116673442897328867)
              ·
                refine ⟨4481760175010164345993301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987840116673442897328867 4481760175010164345993301)
                ·
                  refine ⟨52520627050900363429609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4481760175010164345993301 52520627050900363429609)
                  ·
                    rfl

theorem cell21_230138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_230138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230138 prefixEnd_230138 := by exact prefixLift 230138
  have htrace : WordTrace (prefixWord ++ tailWord_230138) baseStart_230138 baseEnd_230138 := by
    simpa [prefixWord, tailWord_230138, baseEnd_230138] using wordTrace_append hprefix tailTrace_230138
  have hstable : (prefixWord ++ tailWord_230138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230138).length < 2 ^ (prefixWord ++ tailWord_230138).sum := by decide
  have hdescent : baseEnd_230138 < baseStart_230138 := by decide
  rcases family_descends (prefixWord ++ tailWord_230138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230141 : List Nat := [1, 4, 1, 1, 1, 1, 4, 5, 3]
def baseStart_230141 : Nat := 118140960795 + 230141 * 2 ^ 59
def prefixEnd_230141 : Nat := 4983230072969 + 3 ^ 40 * 230141 * 2
def baseEnd_230141 : Nat := 52521311691773024879603

theorem tailTrace_230141 : CollatzResearch.WordTrace tailWord_230141 prefixEnd_230141 52521311691773024879603 := by
  unfold tailWord_230141
  simp only [CollatzResearch.WordTrace]
  refine ⟨8393931859245936798682277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5595954572830624532454851 8393931859245936798682277)
  ·
    refine ⟨1573862223608613149752927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8393931859245936798682277 1573862223608613149752927)
    ·
      refine ⟨2360793335412919724629391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1573862223608613149752927 2360793335412919724629391)
      ·
        refine ⟨3541190003119379586944087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360793335412919724629391 3541190003119379586944087)
        ·
          refine ⟨5311785004679069380416131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541190003119379586944087 5311785004679069380416131)
          ·
            refine ⟨7967677507018604070624197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311785004679069380416131 7967677507018604070624197)
            ·
              refine ⟨1493939532565988263242037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7967677507018604070624197 1493939532565988263242037)
              ·
                refine ⟨140056831178061399678941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1493939532565988263242037 140056831178061399678941)
                ·
                  refine ⟨52521311691773024879603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140056831178061399678941 52521311691773024879603)
                  ·
                    rfl

theorem cell21_230141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_230141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230141 prefixEnd_230141 := by exact prefixLift 230141
  have htrace : WordTrace (prefixWord ++ tailWord_230141) baseStart_230141 baseEnd_230141 := by
    simpa [prefixWord, tailWord_230141, baseEnd_230141] using wordTrace_append hprefix tailTrace_230141
  have hstable : (prefixWord ++ tailWord_230141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230141).length < 2 ^ (prefixWord ++ tailWord_230141).sum := by decide
  have hdescent : baseEnd_230141 < baseStart_230141 := by decide
  rcases family_descends (prefixWord ++ tailWord_230141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230206 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_230206 : Nat := 118140960795 + 230206 * 2 ^ 59
def prefixEnd_230206 : Nat := 4983230072969 + 3 ^ 40 * 230206 * 2
def baseEnd_230206 : Nat := 52536145577347356296137

theorem tailTrace_230206 : CollatzResearch.WordTrace tailWord_230206 prefixEnd_230206 52536145577347356296137 := by
  unfold tailWord_230206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1049537825501306612474809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5597535069340301933198981 1049537825501306612474809)
  ·
    refine ⟨787153369125979959356107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1049537825501306612474809 787153369125979959356107)
    ·
      refine ⟨1180730053688969939034161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787153369125979959356107 1180730053688969939034161)
      ·
        refine ⟨885547540266727454275621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1180730053688969939034161 885547540266727454275621)
        ·
          refine ⟨166040163800011397676679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 885547540266727454275621 166040163800011397676679)
          ·
            refine ⟨249060245700017096515019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166040163800011397676679 249060245700017096515019)
            ·
              refine ⟨373590368550025644772529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249060245700017096515019 373590368550025644772529)
              ·
                refine ⟨280192776412519233579397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373590368550025644772529 280192776412519233579397)
                ·
                  refine ⟨52536145577347356296137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280192776412519233579397 52536145577347356296137)
                  ·
                    rfl

theorem cell21_230206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_230206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230206 prefixEnd_230206 := by exact prefixLift 230206
  have htrace : WordTrace (prefixWord ++ tailWord_230206) baseStart_230206 baseEnd_230206 := by
    simpa [prefixWord, tailWord_230206, baseEnd_230206] using wordTrace_append hprefix tailTrace_230206
  have hstable : (prefixWord ++ tailWord_230206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230206).length < 2 ^ (prefixWord ++ tailWord_230206).sum := by decide
  have hdescent : baseEnd_230206 < baseStart_230206 := by decide
  rcases family_descends (prefixWord ++ tailWord_230206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230217 : List Nat := [1, 2, 1, 1, 2, 5, 2, 4, 3]
def baseStart_230217 : Nat := 118140960795 + 230217 * 2 ^ 59
def prefixEnd_230217 : Nat := 4983230072969 + 3 ^ 40 * 230217 * 2
def baseEnd_230217 : Nat := 52538655927213781612781

theorem tailTrace_230217 : CollatzResearch.WordTrace tailWord_230217 prefixEnd_230217 52538655927213781612781 := by
  unfold tailWord_230217
  simp only [CollatzResearch.WordTrace]
  refine ⟨8396703806970601778448905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5597802537980401185632603 8396703806970601778448905)
  ·
    refine ⟨6297527855227951333836679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8396703806970601778448905 6297527855227951333836679)
    ·
      refine ⟨9446291782841927000755019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6297527855227951333836679 9446291782841927000755019)
      ·
        refine ⟨14169437674262890501132529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9446291782841927000755019 14169437674262890501132529)
        ·
          refine ⟨10627078255697167875849397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14169437674262890501132529 10627078255697167875849397)
          ·
            refine ⟨996288586471609488360881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10627078255697167875849397 996288586471609488360881)
            ·
              refine ⟨747216439853707116270661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996288586471609488360881 747216439853707116270661)
              ·
                refine ⟨140103082472570084300749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 747216439853707116270661 140103082472570084300749)
                ·
                  refine ⟨52538655927213781612781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140103082472570084300749 52538655927213781612781)
                  ·
                    rfl

theorem cell21_230217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 3].length) (baseStart_230217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230217 prefixEnd_230217 := by exact prefixLift 230217
  have htrace : WordTrace (prefixWord ++ tailWord_230217) baseStart_230217 baseEnd_230217 := by
    simpa [prefixWord, tailWord_230217, baseEnd_230217] using wordTrace_append hprefix tailTrace_230217
  have hstable : (prefixWord ++ tailWord_230217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230217).length < 2 ^ (prefixWord ++ tailWord_230217).sum := by decide
  have hdescent : baseEnd_230217 < baseStart_230217 := by decide
  rcases family_descends (prefixWord ++ tailWord_230217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230259 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 7]
def baseStart_230259 : Nat := 118140960795 + 230259 * 2 ^ 59
def prefixEnd_230259 : Nat := 4983230072969 + 3 ^ 40 * 230259 * 2
def baseEnd_230259 : Nat := 52548240899431041912695

theorem tailTrace_230259 : CollatzResearch.WordTrace tailWord_230259 prefixEnd_230259 52548240899431041912695 := by
  unfold tailWord_230259
  simp only [CollatzResearch.WordTrace]
  refine ⟨8398235672818442951477831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5598823781878961967651887 8398235672818442951477831)
  ·
    refine ⟨12597353509227664427216747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8398235672818442951477831 12597353509227664427216747)
    ·
      refine ⟨18896030263841496640825121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12597353509227664427216747 18896030263841496640825121)
      ·
        refine ⟨14172022697881122480618841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18896030263841496640825121 14172022697881122480618841)
        ·
          refine ⟨10629017023410841860464131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14172022697881122480618841 10629017023410841860464131)
          ·
            refine ⟨15943525535116262790696197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10629017023410841860464131 15943525535116262790696197)
            ·
              refine ⟨2989411037834299273255537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15943525535116262790696197 2989411037834299273255537)
              ·
                refine ⟨2242058278375724454941653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2989411037834299273255537 2242058278375724454941653)
                ·
                  refine ⟨52548240899431041912695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2242058278375724454941653 52548240899431041912695)
                  ·
                    rfl

theorem cell21_230259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_230259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230259 prefixEnd_230259 := by exact prefixLift 230259
  have htrace : WordTrace (prefixWord ++ tailWord_230259) baseStart_230259 baseEnd_230259 := by
    simpa [prefixWord, tailWord_230259, baseEnd_230259] using wordTrace_append hprefix tailTrace_230259
  have hstable : (prefixWord ++ tailWord_230259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230259).length < 2 ^ (prefixWord ++ tailWord_230259).sum := by decide
  have hdescent : baseEnd_230259 < baseStart_230259 := by decide
  rcases family_descends (prefixWord ++ tailWord_230259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230262 : List Nat := [5, 1, 1, 3, 1, 1, 9]
def baseStart_230262 : Nat := 118140960795 + 230262 * 2 ^ 59
def prefixEnd_230262 : Nat := 4983230072969 + 3 ^ 40 * 230262 * 2
def baseEnd_230262 : Nat := 5838769504478189262521

theorem tailTrace_230262 : CollatzResearch.WordTrace tailWord_230262 prefixEnd_230262 5838769504478189262521 := by
  unfold tailWord_230262
  simp only [CollatzResearch.WordTrace]
  refine ⟨524896568237973403989815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5598896727871716309224693 524896568237973403989815)
  ·
    refine ⟨787344852356960105984723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524896568237973403989815 787344852356960105984723)
    ·
      refine ⟨1181017278535440158977085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787344852356960105984723 1181017278535440158977085)
      ·
        refine ⟨442881479450790059616407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1181017278535440158977085 442881479450790059616407)
        ·
          refine ⟨664322219176185089424611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442881479450790059616407 664322219176185089424611)
          ·
            refine ⟨996483328764277634136917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664322219176185089424611 996483328764277634136917)
            ·
              refine ⟨5838769504478189262521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 996483328764277634136917 5838769504478189262521)
              ·
                rfl

theorem cell21_230262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 9].length) (baseStart_230262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230262 prefixEnd_230262 := by exact prefixLift 230262
  have htrace : WordTrace (prefixWord ++ tailWord_230262) baseStart_230262 baseEnd_230262 := by
    simpa [prefixWord, tailWord_230262, baseEnd_230262] using wordTrace_append hprefix tailTrace_230262
  have hstable : (prefixWord ++ tailWord_230262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230262).length < 2 ^ (prefixWord ++ tailWord_230262).sum := by decide
  have hdescent : baseEnd_230262 < baseStart_230262 := by decide
  rcases family_descends (prefixWord ++ tailWord_230262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230321 : List Nat := [1, 2, 2, 4, 3, 9]
def baseStart_230321 : Nat := 118140960795 + 230321 * 2 ^ 59
def prefixEnd_230321 : Nat := 4983230072969 + 3 ^ 40 * 230321 * 2
def baseEnd_230321 : Nat := 1946755190523433773305

theorem tailTrace_230321 : CollatzResearch.WordTrace tailWord_230321 prefixEnd_230321 1946755190523433773305 := by
  unfold tailWord_230321
  simp only [CollatzResearch.WordTrace]
  refine ⟨8400496998593827540234817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5600331332395885026823211 8400496998593827540234817)
  ·
    refine ⟨6300372748945370655176113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8400496998593827540234817 6300372748945370655176113)
    ·
      refine ⟨4725279561709027991382085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6300372748945370655176113 4725279561709027991382085)
      ·
        refine ⟨885989917820442748384141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4725279561709027991382085 885989917820442748384141)
        ·
          refine ⟨332246219182666030644053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 885989917820442748384141 332246219182666030644053)
          ·
            refine ⟨1946755190523433773305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 332246219182666030644053 1946755190523433773305)
            ·
              rfl

theorem cell21_230321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 9].length) (baseStart_230321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230321 prefixEnd_230321 := by exact prefixLift 230321
  have htrace : WordTrace (prefixWord ++ tailWord_230321) baseStart_230321 baseEnd_230321 := by
    simpa [prefixWord, tailWord_230321, baseEnd_230321] using wordTrace_append hprefix tailTrace_230321
  have hstable : (prefixWord ++ tailWord_230321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230321).length < 2 ^ (prefixWord ++ tailWord_230321).sum := by decide
  have hdescent : baseEnd_230321 < baseStart_230321 := by decide
  rcases family_descends (prefixWord ++ tailWord_230321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230383 : List Nat := [1, 1, 2, 1, 4, 3, 3, 2, 4]
def baseStart_230383 : Nat := 118140960795 + 230383 * 2 ^ 59
def prefixEnd_230383 : Nat := 4983230072969 + 3 ^ 40 * 230383 * 2
def baseEnd_230383 : Nat := 52576539388834381845775

theorem tailTrace_230383 : CollatzResearch.WordTrace tailWord_230383 prefixEnd_230383 52576539388834381845775 := by
  unfold tailWord_230383
  simp only [CollatzResearch.WordTrace]
  refine ⟨8402758324369212128991803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5601838882912808085994535 8402758324369212128991803)
  ·
    refine ⟨12604137486553818193487705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8402758324369212128991803 12604137486553818193487705)
    ·
      refine ⟨9453103114915363645115779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12604137486553818193487705 9453103114915363645115779)
      ·
        refine ⟨14179654672373045467673669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453103114915363645115779 14179654672373045467673669)
        ·
          refine ⟨2658685251069946025188813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14179654672373045467673669 2658685251069946025188813)
          ·
            refine ⟨997006969151229759445805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2658685251069946025188813 997006969151229759445805)
            ·
              refine ⟨373877613431711159792177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 997006969151229759445805 373877613431711159792177)
              ·
                refine ⟨280408210073783369844133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373877613431711159792177 280408210073783369844133)
                ·
                  refine ⟨52576539388834381845775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280408210073783369844133 52576539388834381845775)
                  ·
                    rfl

theorem cell21_230383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 4].length) (baseStart_230383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230383 prefixEnd_230383 := by exact prefixLift 230383
  have htrace : WordTrace (prefixWord ++ tailWord_230383) baseStart_230383 baseEnd_230383 := by
    simpa [prefixWord, tailWord_230383, baseEnd_230383] using wordTrace_append hprefix tailTrace_230383
  have hstable : (prefixWord ++ tailWord_230383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230383).length < 2 ^ (prefixWord ++ tailWord_230383).sum := by decide
  have hdescent : baseEnd_230383 < baseStart_230383 := by decide
  rcases family_descends (prefixWord ++ tailWord_230383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230386 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_230386 : Nat := 118140960795 + 230386 * 2 ^ 59
def prefixEnd_230386 : Nat := 4983230072969 + 3 ^ 40 * 230386 * 2
def baseEnd_230386 : Nat := 52577224029707043295769

theorem tailTrace_230386 : CollatzResearch.WordTrace tailWord_230386 prefixEnd_230386 52577224029707043295769 := by
  unfold tailWord_230386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100716935839585910337753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5601911828905562427567341 2100716935839585910337753)
  ·
    refine ⟨1575537701879689432753315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2100716935839585910337753 1575537701879689432753315)
    ·
      refine ⟨2363306552819534149129973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575537701879689432753315 2363306552819534149129973)
      ·
        refine ⟨221559989326831326480935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2363306552819534149129973 221559989326831326480935)
        ·
          refine ⟨332339983990246989721403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221559989326831326480935 332339983990246989721403)
          ·
            refine ⟨498509975985370484582105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332339983990246989721403 498509975985370484582105)
            ·
              refine ⟨373882481989027863436579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498509975985370484582105 373882481989027863436579)
              ·
                refine ⟨560823722983541795154869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373882481989027863436579 560823722983541795154869)
                ·
                  refine ⟨52577224029707043295769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 560823722983541795154869 52577224029707043295769)
                  ·
                    rfl

theorem cell21_230386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_230386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230386 prefixEnd_230386 := by exact prefixLift 230386
  have htrace : WordTrace (prefixWord ++ tailWord_230386) baseStart_230386 baseEnd_230386 := by
    simpa [prefixWord, tailWord_230386, baseEnd_230386] using wordTrace_append hprefix tailTrace_230386
  have hstable : (prefixWord ++ tailWord_230386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230386).length < 2 ^ (prefixWord ++ tailWord_230386).sum := by decide
  have hdescent : baseEnd_230386 < baseStart_230386 := by decide
  rcases family_descends (prefixWord ++ tailWord_230386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230414 : List Nat := [4, 1, 1, 2, 2, 2, 4, 5]
def baseStart_230414 : Nat := 118140960795 + 230414 * 2 ^ 59
def prefixEnd_230414 : Nat := 4983230072969 + 3 ^ 40 * 230414 * 2
def baseEnd_230414 : Nat := 17527871337061738943015

theorem tailTrace_230414 : CollatzResearch.WordTrace tailWord_230414 prefixEnd_230414 17527871337061738943015 := by
  unfold tailWord_230414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050486123407113052921287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5602592658171269615580197 1050486123407113052921287)
  ·
    refine ⟨1575729185110669579381931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1050486123407113052921287 1575729185110669579381931)
    ·
      refine ⟨2363593777666004369072897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575729185110669579381931 2363593777666004369072897)
      ·
        refine ⟨1772695333249503276804673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2363593777666004369072897 1772695333249503276804673)
        ·
          refine ⟨1329521499937127457603505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1772695333249503276804673 1329521499937127457603505)
          ·
            refine ⟨997141124952845593202629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1329521499937127457603505 997141124952845593202629)
            ·
              refine ⟨186963960928658548725493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 997141124952845593202629 186963960928658548725493)
              ·
                refine ⟨17527871337061738943015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186963960928658548725493 17527871337061738943015)
                ·
                  rfl

theorem cell21_230414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_230414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230414 prefixEnd_230414 := by exact prefixLift 230414
  have htrace : WordTrace (prefixWord ++ tailWord_230414) baseStart_230414 baseEnd_230414 := by
    simpa [prefixWord, tailWord_230414, baseEnd_230414] using wordTrace_append hprefix tailTrace_230414
  have hstable : (prefixWord ++ tailWord_230414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230414).length < 2 ^ (prefixWord ++ tailWord_230414).sum := by decide
  have hdescent : baseEnd_230414 < baseStart_230414 := by decide
  rcases family_descends (prefixWord ++ tailWord_230414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230493 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 4]
def baseStart_230493 : Nat := 118140960795 + 230493 * 2 ^ 59
def prefixEnd_230493 : Nat := 4983230072969 + 3 ^ 40 * 230493 * 2
def baseEnd_230493 : Nat := 52601642887498635012217

theorem tailTrace_230493 : CollatzResearch.WordTrace tailWord_230493 prefixEnd_230493 52601642887498635012217 := by
  unfold tailWord_230493
  simp only [CollatzResearch.WordTrace]
  refine ⟨8406770353970700915496133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5604513569313800610330755 8406770353970700915496133)
  ·
    refine ⟨1576269441369506421655525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8406770353970700915496133 1576269441369506421655525)
    ·
      refine ⟨295550520256782454060411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1576269441369506421655525 295550520256782454060411)
      ·
        refine ⟨443325780385173681090617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295550520256782454060411 443325780385173681090617)
        ·
          refine ⟨332494335288880260817963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 443325780385173681090617 332494335288880260817963)
          ·
            refine ⟨498741502933320391226945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332494335288880260817963 498741502933320391226945)
            ·
              refine ⟨374056127199990293420209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498741502933320391226945 374056127199990293420209)
              ·
                refine ⟨280542095399992720065157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374056127199990293420209 280542095399992720065157)
                ·
                  refine ⟨52601642887498635012217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280542095399992720065157 52601642887498635012217)
                  ·
                    rfl

theorem cell21_230493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_230493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230493 prefixEnd_230493 := by exact prefixLift 230493
  have htrace : WordTrace (prefixWord ++ tailWord_230493) baseStart_230493 baseEnd_230493 := by
    simpa [prefixWord, tailWord_230493, baseEnd_230493] using wordTrace_append hprefix tailTrace_230493
  have hstable : (prefixWord ++ tailWord_230493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230493).length < 2 ^ (prefixWord ++ tailWord_230493).sum := by decide
  have hdescent : baseEnd_230493 < baseStart_230493 := by decide
  rcases family_descends (prefixWord ++ tailWord_230493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230552 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 4]
def baseStart_230552 : Nat := 118140960795 + 230552 * 2 ^ 59
def prefixEnd_230552 : Nat := 4983230072969 + 3 ^ 40 * 230552 * 2
def baseEnd_230552 : Nat := 52615107491327643528763

theorem tailTrace_230552 : CollatzResearch.WordTrace tailWord_230552 prefixEnd_230552 52615107491327643528763 := by
  unfold tailWord_230552
  simp only [CollatzResearch.WordTrace]
  refine ⟨4204461130378476995946955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5605948173837969327929273 4204461130378476995946955)
  ·
    refine ⟨6306691695567715493920433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4204461130378476995946955 6306691695567715493920433)
    ·
      refine ⟨4730018771675786620440325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6306691695567715493920433 4730018771675786620440325)
      ·
        refine ⟨886878519689209991332561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4730018771675786620440325 886878519689209991332561)
        ·
          refine ⟨665158889766907493499421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886878519689209991332561 665158889766907493499421)
          ·
            refine ⟨249434583662590310062283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 665158889766907493499421 249434583662590310062283)
            ·
              refine ⟨374151875493885465093425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249434583662590310062283 374151875493885465093425)
              ·
                refine ⟨280613906620414098820069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374151875493885465093425 280613906620414098820069)
                ·
                  refine ⟨52615107491327643528763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280613906620414098820069 52615107491327643528763)
                  ·
                    rfl

theorem cell21_230552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_230552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230552 prefixEnd_230552 := by exact prefixLift 230552
  have htrace : WordTrace (prefixWord ++ tailWord_230552) baseStart_230552 baseEnd_230552 := by
    simpa [prefixWord, tailWord_230552, baseEnd_230552] using wordTrace_append hprefix tailTrace_230552
  have hstable : (prefixWord ++ tailWord_230552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230552).length < 2 ^ (prefixWord ++ tailWord_230552).sum := by decide
  have hdescent : baseEnd_230552 < baseStart_230552 := by decide
  rcases family_descends (prefixWord ++ tailWord_230552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230625 : List Nat := [1, 2, 3, 1, 3, 3, 2, 6]
def baseStart_230625 : Nat := 118140960795 + 230625 * 2 ^ 59
def prefixEnd_230625 : Nat := 4983230072969 + 3 ^ 40 * 230625 * 2
def baseEnd_230625 : Nat := 17543922361965246270649

theorem tailTrace_230625 : CollatzResearch.WordTrace tailWord_230625 prefixEnd_230625 17543922361965246270649 := by
  unfold tailWord_230625
  simp only [CollatzResearch.WordTrace]
  refine ⟨8411584789492487459301329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5607723192994991639534219 8411584789492487459301329)
  ·
    refine ⟨6308688592119365594475997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8411584789492487459301329 6308688592119365594475997)
    ·
      refine ⟨2365758222044762097928499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6308688592119365594475997 2365758222044762097928499)
      ·
        refine ⟨3548637333067143146892749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365758222044762097928499 3548637333067143146892749)
        ·
          refine ⟨1330738999900178680084781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3548637333067143146892749 1330738999900178680084781)
          ·
            refine ⟨499027124962567005031793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1330738999900178680084781 499027124962567005031793)
            ·
              refine ⟨374270343721925253773845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499027124962567005031793 374270343721925253773845)
              ·
                refine ⟨17543922361965246270649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 374270343721925253773845 17543922361965246270649)
                ·
                  rfl

theorem cell21_230625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 6].length) (baseStart_230625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230625 prefixEnd_230625 := by exact prefixLift 230625
  have htrace : WordTrace (prefixWord ++ tailWord_230625) baseStart_230625 baseEnd_230625 := by
    simpa [prefixWord, tailWord_230625, baseEnd_230625] using wordTrace_append hprefix tailTrace_230625
  have hstable : (prefixWord ++ tailWord_230625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230625).length < 2 ^ (prefixWord ++ tailWord_230625).sum := by decide
  have hdescent : baseEnd_230625 < baseStart_230625 := by decide
  rcases family_descends (prefixWord ++ tailWord_230625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230656 : List Nat := [2, 1, 1, 2, 1, 1, 3, 7, 3]
def baseStart_230656 : Nat := 118140960795 + 230656 * 2 ^ 59
def prefixEnd_230656 : Nat := 4983230072969 + 3 ^ 40 * 230656 * 2
def baseEnd_230656 : Nat := 52638841708246573795217

theorem tailTrace_230656 : CollatzResearch.WordTrace tailWord_230656 prefixEnd_230656 52638841708246573795217 := by
  unfold tailWord_230656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206357726190089876839911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5608476968253453169119881 4206357726190089876839911)
  ·
    refine ⟨6309536589285134815259867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4206357726190089876839911 6309536589285134815259867)
    ·
      refine ⟨9464304883927702222889801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6309536589285134815259867 9464304883927702222889801)
      ·
        refine ⟨7098228662945776667167351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9464304883927702222889801 7098228662945776667167351)
        ·
          refine ⟨10647342994418665000751027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098228662945776667167351 10647342994418665000751027)
          ·
            refine ⟨15971014491627997501126541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10647342994418665000751027 15971014491627997501126541)
            ·
              refine ⟨5989130434360499062922453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15971014491627997501126541 5989130434360499062922453)
              ·
                refine ⟨140370244555324196787245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5989130434360499062922453 140370244555324196787245)
                ·
                  refine ⟨52638841708246573795217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140370244555324196787245 52638841708246573795217)
                  ·
                    rfl

theorem cell21_230656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 3].length) (baseStart_230656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230656 prefixEnd_230656 := by exact prefixLift 230656
  have htrace : WordTrace (prefixWord ++ tailWord_230656) baseStart_230656 baseEnd_230656 := by
    simpa [prefixWord, tailWord_230656, baseEnd_230656] using wordTrace_append hprefix tailTrace_230656
  have hstable : (prefixWord ++ tailWord_230656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230656).length < 2 ^ (prefixWord ++ tailWord_230656).sum := by decide
  have hdescent : baseEnd_230656 < baseStart_230656 := by decide
  rcases family_descends (prefixWord ++ tailWord_230656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230732 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 5]
def baseStart_230732 : Nat := 118140960795 + 230732 * 2 ^ 59
def prefixEnd_230732 : Nat := 4983230072969 + 3 ^ 40 * 230732 * 2
def baseEnd_230732 : Nat := 52656185943687330528395

theorem tailTrace_230732 : CollatzResearch.WordTrace tailWord_230732 prefixEnd_230732 52656185943687330528395 := by
  unfold tailWord_230732
  simp only [CollatzResearch.WordTrace]
  refine ⟨4207743700052422366723225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5610324933403229822297633 4207743700052422366723225)
  ·
    refine ⟨3155807775039316775042419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4207743700052422366723225 3155807775039316775042419)
    ·
      refine ⟨4733711662558975162563629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3155807775039316775042419 4733711662558975162563629)
      ·
        refine ⟨1775141873459615685961361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4733711662558975162563629 1775141873459615685961361)
        ·
          refine ⟨1331356405094711764471021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775141873459615685961361 1331356405094711764471021)
          ·
            refine ⟨499258651910516911676633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1331356405094711764471021 499258651910516911676633)
            ·
              refine ⟨374443988932887683757475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499258651910516911676633 374443988932887683757475)
              ·
                refine ⟨561665983399331525636213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374443988932887683757475 561665983399331525636213)
                ·
                  refine ⟨52656185943687330528395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 561665983399331525636213 52656185943687330528395)
                  ·
                    rfl

theorem cell21_230732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_230732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230732 prefixEnd_230732 := by exact prefixLift 230732
  have htrace : WordTrace (prefixWord ++ tailWord_230732) baseStart_230732 baseEnd_230732 := by
    simpa [prefixWord, tailWord_230732, baseEnd_230732] using wordTrace_append hprefix tailTrace_230732
  have hstable : (prefixWord ++ tailWord_230732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230732).length < 2 ^ (prefixWord ++ tailWord_230732).sum := by decide
  have hdescent : baseEnd_230732 < baseStart_230732 := by decide
  rcases family_descends (prefixWord ++ tailWord_230732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230746 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_230746 : Nat := 118140960795 + 230746 * 2 ^ 59
def prefixEnd_230746 : Nat := 4983230072969 + 3 ^ 40 * 230746 * 2
def baseEnd_230746 : Nat := 52659380934426417295033

theorem tailTrace_230746 : CollatzResearch.WordTrace tailWord_230746 prefixEnd_230746 52659380934426417295033 := by
  unfold tailWord_230746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2103999505513531281114023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5610665348036083416304061 2103999505513531281114023)
  ·
    refine ⟨3155999258270296921671035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2103999505513531281114023 3155999258270296921671035)
    ·
      refine ⟨4733998887405445382506553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3155999258270296921671035 4733998887405445382506553)
      ·
        refine ⟨3550499165554084036879915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4733998887405445382506553 3550499165554084036879915)
        ·
          refine ⟨5325748748331126055319873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550499165554084036879915 5325748748331126055319873)
          ·
            refine ⟨3994311561248344541489905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5325748748331126055319873 3994311561248344541489905)
            ·
              refine ⟨2995733670936258406117429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3994311561248344541489905 2995733670936258406117429)
              ·
                refine ⟨280850031650274225573509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2995733670936258406117429 280850031650274225573509)
                ·
                  refine ⟨52659380934426417295033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 280850031650274225573509 52659380934426417295033)
                  ·
                    rfl

theorem cell21_230746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_230746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230746 prefixEnd_230746 := by exact prefixLift 230746
  have htrace : WordTrace (prefixWord ++ tailWord_230746) baseStart_230746 baseEnd_230746 := by
    simpa [prefixWord, tailWord_230746, baseEnd_230746] using wordTrace_append hprefix tailTrace_230746
  have hstable : (prefixWord ++ tailWord_230746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230746).length < 2 ^ (prefixWord ++ tailWord_230746).sum := by decide
  have hdescent : baseEnd_230746 < baseStart_230746 := by decide
  rcases family_descends (prefixWord ++ tailWord_230746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230901 : List Nat := [1, 3, 5, 1, 1, 2, 2, 1, 5]
def baseStart_230901 : Nat := 118140960795 + 230901 * 2 ^ 59
def prefixEnd_230901 : Nat := 4983230072969 + 3 ^ 40 * 230901 * 2
def baseEnd_230901 : Nat := 52694754046180592211383

theorem tailTrace_230901 : CollatzResearch.WordTrace tailWord_230901 prefixEnd_230901 52694754046180592211383 := by
  unfold tailWord_230901
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421651336492586596348557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5614434224328391064232371 8421651336492586596348557)
  ·
    refine ⟨3158119251184719973630709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8421651336492586596348557 3158119251184719973630709)
    ·
      refine ⟨296073679798567497527879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3158119251184719973630709 296073679798567497527879)
      ·
        refine ⟨444110519697851246291819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296073679798567497527879 444110519697851246291819)
        ·
          refine ⟨666165779546776869437729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444110519697851246291819 666165779546776869437729)
          ·
            refine ⟨499624334660082652078297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666165779546776869437729 499624334660082652078297)
            ·
              refine ⟨374718250995061989058723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499624334660082652078297 374718250995061989058723)
              ·
                refine ⟨562077376492592983588085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 374718250995061989058723 562077376492592983588085)
                ·
                  refine ⟨52694754046180592211383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 562077376492592983588085 52694754046180592211383)
                  ·
                    rfl

theorem cell21_230901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_230901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230901 prefixEnd_230901 := by exact prefixLift 230901
  have htrace : WordTrace (prefixWord ++ tailWord_230901) baseStart_230901 baseEnd_230901 := by
    simpa [prefixWord, tailWord_230901, baseEnd_230901] using wordTrace_append hprefix tailTrace_230901
  have hstable : (prefixWord ++ tailWord_230901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230901).length < 2 ^ (prefixWord ++ tailWord_230901).sum := by decide
  have hdescent : baseEnd_230901 < baseStart_230901 := by decide
  rcases family_descends (prefixWord ++ tailWord_230901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230966 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_230966 : Nat := 118140960795 + 230966 * 2 ^ 59
def prefixEnd_230966 : Nat := 4983230072969 + 3 ^ 40 * 230966 * 2
def baseEnd_230966 : Nat := 52709587931754923627917

theorem tailTrace_230966 : CollatzResearch.WordTrace tailWord_230966 prefixEnd_230966 52709587931754923627917 := by
  unfold tailWord_230966
  simp only [CollatzResearch.WordTrace]
  refine ⟨526501380078568918591547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5616014720838068464976501 526501380078568918591547)
  ·
    refine ⟨789752070117853377887321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 526501380078568918591547 789752070117853377887321)
    ·
      refine ⟨592314052588390033415491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 789752070117853377887321 592314052588390033415491)
      ·
        refine ⟨888471078882585050123237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592314052588390033415491 888471078882585050123237)
        ·
          refine ⟨166588327290484696898107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 888471078882585050123237 166588327290484696898107)
          ·
            refine ⟨249882490935727045347161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166588327290484696898107 249882490935727045347161)
            ·
              refine ⟨187411868201795284010371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249882490935727045347161 187411868201795284010371)
              ·
                refine ⟨281117802302692926015557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187411868201795284010371 281117802302692926015557)
                ·
                  refine ⟨52709587931754923627917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281117802302692926015557 52709587931754923627917)
                  ·
                    rfl

theorem cell21_230966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_230966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230966 prefixEnd_230966 := by exact prefixLift 230966
  have htrace : WordTrace (prefixWord ++ tailWord_230966) baseStart_230966 baseEnd_230966 := by
    simpa [prefixWord, tailWord_230966, baseEnd_230966] using wordTrace_append hprefix tailTrace_230966
  have hstable : (prefixWord ++ tailWord_230966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230966).length < 2 ^ (prefixWord ++ tailWord_230966).sum := by decide
  have hdescent : baseEnd_230966 < baseStart_230966 := by decide
  rcases family_descends (prefixWord ++ tailWord_230966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_230988 : List Nat := [2, 2, 1, 3, 1, 3, 2, 7]
def baseStart_230988 : Nat := 118140960795 + 230988 * 2 ^ 59
def prefixEnd_230988 : Nat := 4983230072969 + 3 ^ 40 * 230988 * 2
def baseEnd_230988 : Nat := 17571536210495924753735

theorem tailTrace_230988 : CollatzResearch.WordTrace tailWord_230988 prefixEnd_230988 17571536210495924753735 := by
  unfold tailWord_230988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4212412243588700227382809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5616549658118266969843745 4212412243588700227382809)
  ·
    refine ⟨3159309182691525170537107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4212412243588700227382809 3159309182691525170537107)
    ·
      refine ⟨4738963774037287755805661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3159309182691525170537107 4738963774037287755805661)
      ·
        refine ⟨1777111415263982908427123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4738963774037287755805661 1777111415263982908427123)
        ·
          refine ⟨2665667122895974362640685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777111415263982908427123 2665667122895974362640685)
          ·
            refine ⟨999625171085990385990257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2665667122895974362640685 999625171085990385990257)
            ·
              refine ⟨749718878314492789492693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999625171085990385990257 749718878314492789492693)
              ·
                refine ⟨17571536210495924753735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 749718878314492789492693 17571536210495924753735)
                ·
                  rfl

theorem cell21_230988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_230988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_230988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_230988 prefixEnd_230988 := by exact prefixLift 230988
  have htrace : WordTrace (prefixWord ++ tailWord_230988) baseStart_230988 baseEnd_230988 := by
    simpa [prefixWord, tailWord_230988, baseEnd_230988] using wordTrace_append hprefix tailTrace_230988
  have hstable : (prefixWord ++ tailWord_230988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_230988).length < 2 ^ (prefixWord ++ tailWord_230988).sum := by decide
  have hdescent : baseEnd_230988 < baseStart_230988 := by decide
  rcases family_descends (prefixWord ++ tailWord_230988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231005 : List Nat := [1, 4, 4, 2, 10]
def baseStart_231005 : Nat := 118140960795 + 231005 * 2 ^ 59
def prefixEnd_231005 : Nat := 4983230072969 + 3 ^ 40 * 231005 * 2
def baseEnd_231005 : Nat := 650845534112339783677

theorem tailTrace_231005 : CollatzResearch.WordTrace tailWord_231005 prefixEnd_231005 650845534112339783677 := by
  unfold tailWord_231005
  simp only [CollatzResearch.WordTrace]
  refine ⟨8425444528115812358134469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5616963018743874905422979 8425444528115812358134469)
  ·
    refine ⟨1579770849021714817150213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8425444528115812358134469 1579770849021714817150213)
    ·
      refine ⟨296207034191571528215665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1579770849021714817150213 296207034191571528215665)
      ·
        refine ⟨222155275643678646161749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296207034191571528215665 222155275643678646161749)
        ·
          refine ⟨650845534112339783677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 222155275643678646161749 650845534112339783677)
          ·
            rfl

theorem cell21_231005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 10].length) (baseStart_231005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231005 prefixEnd_231005 := by exact prefixLift 231005
  have htrace : WordTrace (prefixWord ++ tailWord_231005) baseStart_231005 baseEnd_231005 := by
    simpa [prefixWord, tailWord_231005, baseEnd_231005] using wordTrace_append hprefix tailTrace_231005
  have hstable : (prefixWord ++ tailWord_231005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231005).length < 2 ^ (prefixWord ++ tailWord_231005).sum := by decide
  have hdescent : baseEnd_231005 < baseStart_231005 := by decide
  rcases family_descends (prefixWord ++ tailWord_231005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231022 : List Nat := [4, 1, 2, 2, 3, 2, 1, 6]
def baseStart_231022 : Nat := 118140960795 + 231022 * 2 ^ 59
def prefixEnd_231022 : Nat := 4983230072969 + 3 ^ 40 * 231022 * 2
def baseEnd_231022 : Nat := 17574122631570423564823

theorem tailTrace_231022 : CollatzResearch.WordTrace tailWord_231022 prefixEnd_231022 17574122631570423564823 := by
  unfold tailWord_231022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1053258071131778032687915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5617376379369482841002213 1053258071131778032687915)
  ·
    refine ⟨1579887106697667049031873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1053258071131778032687915 1579887106697667049031873)
    ·
      refine ⟨1184915330023250286773905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1579887106697667049031873 1184915330023250286773905)
      ·
        refine ⟨888686497517437715080429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1184915330023250286773905 888686497517437715080429)
        ·
          refine ⟨333257436569039143155161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 888686497517437715080429 333257436569039143155161)
          ·
            refine ⟨249943077426779357366371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333257436569039143155161 249943077426779357366371)
            ·
              refine ⟨374914616140169036049557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249943077426779357366371 374914616140169036049557)
              ·
                refine ⟨17574122631570423564823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 374914616140169036049557 17574122631570423564823)
                ·
                  rfl

theorem cell21_231022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_231022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231022 prefixEnd_231022 := by exact prefixLift 231022
  have htrace : WordTrace (prefixWord ++ tailWord_231022) baseStart_231022 baseEnd_231022 := by
    simpa [prefixWord, tailWord_231022, baseEnd_231022] using wordTrace_append hprefix tailTrace_231022
  have hstable : (prefixWord ++ tailWord_231022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231022).length < 2 ^ (prefixWord ++ tailWord_231022).sum := by decide
  have hdescent : baseEnd_231022 < baseStart_231022 := by decide
  rcases family_descends (prefixWord ++ tailWord_231022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231064 : List Nat := [2, 1, 2, 4, 1, 3, 8]
def baseStart_231064 : Nat := 118140960795 + 231064 * 2 ^ 59
def prefixEnd_231064 : Nat := 4983230072969 + 3 ^ 40 * 231064 * 2
def baseEnd_231064 : Nat := 5859105874103170110487

theorem tailTrace_231064 : CollatzResearch.WordTrace tailWord_231064 prefixEnd_231064 5859105874103170110487 := by
  unfold tailWord_231064
  simp only [CollatzResearch.WordTrace]
  refine ⟨4213798217451032717266123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5618397623268043623021497 4213798217451032717266123)
  ·
    refine ⟨6320697326176549075899185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4213798217451032717266123 6320697326176549075899185)
    ·
      refine ⟨4740522994632411806924389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6320697326176549075899185 4740522994632411806924389)
      ·
        refine ⟨888848061493577213798323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4740522994632411806924389 888848061493577213798323)
        ·
          refine ⟨1333272092240365820697485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888848061493577213798323 1333272092240365820697485)
          ·
            refine ⟨499977034590137182761557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1333272092240365820697485 499977034590137182761557)
            ·
              refine ⟨5859105874103170110487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 499977034590137182761557 5859105874103170110487)
              ·
                rfl

theorem cell21_231064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 8].length) (baseStart_231064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231064 prefixEnd_231064 := by exact prefixLift 231064
  have htrace : WordTrace (prefixWord ++ tailWord_231064) baseStart_231064 baseEnd_231064 := by
    simpa [prefixWord, tailWord_231064, baseEnd_231064] using wordTrace_append hprefix tailTrace_231064
  have hstable : (prefixWord ++ tailWord_231064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231064).length < 2 ^ (prefixWord ++ tailWord_231064).sum := by decide
  have hdescent : baseEnd_231064 < baseStart_231064 := by decide
  rcases family_descends (prefixWord ++ tailWord_231064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231095 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 5]
def baseStart_231095 : Nat := 118140960795 + 231095 * 2 ^ 59
def prefixEnd_231095 : Nat := 4983230072969 + 3 ^ 40 * 231095 * 2
def baseEnd_231095 : Nat := 52739027489279365977653

theorem tailTrace_231095 : CollatzResearch.WordTrace tailWord_231095 prefixEnd_231095 52739027489279365977653 := by
  unfold tailWord_231095
  simp only [CollatzResearch.WordTrace]
  refine ⟨8428727097789757728910739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5619151398526505152607159 8428727097789757728910739)
  ·
    refine ⟨12643090646684636593366109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8428727097789757728910739 12643090646684636593366109)
    ·
      refine ⟨4741158992506738722512291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12643090646684636593366109 4741158992506738722512291)
      ·
        refine ⟨7111738488760108083768437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4741158992506738722512291 7111738488760108083768437)
        ·
          refine ⟨666725483321260132853291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7111738488760108083768437 666725483321260132853291)
          ·
            refine ⟨1000088224981890199279937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666725483321260132853291 1000088224981890199279937)
            ·
              refine ⟨750066168736417649459953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000088224981890199279937 750066168736417649459953)
              ·
                refine ⟨562549626552313237094965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750066168736417649459953 562549626552313237094965)
                ·
                  refine ⟨52739027489279365977653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 562549626552313237094965 52739027489279365977653)
                  ·
                    rfl

theorem cell21_231095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_231095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231095 prefixEnd_231095 := by exact prefixLift 231095
  have htrace : WordTrace (prefixWord ++ tailWord_231095) baseStart_231095 baseEnd_231095 := by
    simpa [prefixWord, tailWord_231095, baseEnd_231095] using wordTrace_append hprefix tailTrace_231095
  have hstable : (prefixWord ++ tailWord_231095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231095).length < 2 ^ (prefixWord ++ tailWord_231095).sum := by decide
  have hdescent : baseEnd_231095 < baseStart_231095 := by decide
  rcases family_descends (prefixWord ++ tailWord_231095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231129 : List Nat := [1, 2, 1, 2, 3, 4, 3, 2, 3]
def baseStart_231129 : Nat := 118140960795 + 231129 * 2 ^ 59
def prefixEnd_231129 : Nat := 4983230072969 + 3 ^ 40 * 231129 * 2
def baseEnd_231129 : Nat := 52746786752502862410917

theorem tailTrace_231129 : CollatzResearch.WordTrace tailWord_231129 prefixEnd_231129 52746786752502862410917 := by
  unfold tailWord_231129
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429967179666581535648441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5619978119777721023765627 8429967179666581535648441)
  ·
    refine ⟨6322475384749936151736331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8429967179666581535648441 6322475384749936151736331)
    ·
      refine ⟨9483713077124904227604497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6322475384749936151736331 9483713077124904227604497)
      ·
        refine ⟨7112784807843678170703373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9483713077124904227604497 7112784807843678170703373)
        ·
          refine ⟨2667294302941379314013765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7112784807843678170703373 2667294302941379314013765)
          ·
            refine ⟨500117681801508621377581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2667294302941379314013765 500117681801508621377581)
            ·
              refine ⟨187544130675565733016593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 500117681801508621377581 187544130675565733016593)
              ·
                refine ⟨140658098006674299762445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187544130675565733016593 140658098006674299762445)
                ·
                  refine ⟨52746786752502862410917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140658098006674299762445 52746786752502862410917)
                  ·
                    rfl

theorem cell21_231129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 3].length) (baseStart_231129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231129 prefixEnd_231129 := by exact prefixLift 231129
  have htrace : WordTrace (prefixWord ++ tailWord_231129) baseStart_231129 baseEnd_231129 := by
    simpa [prefixWord, tailWord_231129, baseEnd_231129] using wordTrace_append hprefix tailTrace_231129
  have hstable : (prefixWord ++ tailWord_231129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231129).length < 2 ^ (prefixWord ++ tailWord_231129).sum := by decide
  have hdescent : baseEnd_231129 < baseStart_231129 := by decide
  rcases family_descends (prefixWord ++ tailWord_231129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231140 : List Nat := [2, 3, 1, 1, 1, 3, 4, 6]
def baseStart_231140 : Nat := 118140960795 + 231140 * 2 ^ 59
def prefixEnd_231140 : Nat := 4983230072969 + 3 ^ 40 * 231140 * 2
def baseEnd_231140 : Nat := 17583099034123095909187

theorem tailTrace_231140 : CollatzResearch.WordTrace tailWord_231140 prefixEnd_231140 17583099034123095909187 := by
  unfold tailWord_231140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4215184191313365207149437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5620245588417820276199249 4215184191313365207149437)
  ·
    refine ⟨1580694071742511952681039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4215184191313365207149437 1580694071742511952681039)
    ·
      refine ⟨2371041107613767929021559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1580694071742511952681039 2371041107613767929021559)
      ·
        refine ⟨3556561661420651893532339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371041107613767929021559 3556561661420651893532339)
        ·
          refine ⟨5334842492130977840298509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3556561661420651893532339 5334842492130977840298509)
          ·
            refine ⟨2000565934549116690111941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5334842492130977840298509 2000565934549116690111941)
            ·
              refine ⟨375106112727959379395989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2000565934549116690111941 375106112727959379395989)
              ·
                refine ⟨17583099034123095909187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 375106112727959379395989 17583099034123095909187)
                ·
                  rfl

theorem cell21_231140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_231140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231140 prefixEnd_231140 := by exact prefixLift 231140
  have htrace : WordTrace (prefixWord ++ tailWord_231140) baseStart_231140 baseEnd_231140 := by
    simpa [prefixWord, tailWord_231140, baseEnd_231140] using wordTrace_append hprefix tailTrace_231140
  have hstable : (prefixWord ++ tailWord_231140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231140).length < 2 ^ (prefixWord ++ tailWord_231140).sum := by decide
  have hdescent : baseEnd_231140 < baseStart_231140 := by decide
  rcases family_descends (prefixWord ++ tailWord_231140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231202 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_231202 : Nat := 118140960795 + 231202 * 2 ^ 59
def prefixEnd_231202 : Nat := 4983230072969 + 3 ^ 40 * 231202 * 2
def baseEnd_231202 : Nat := 52763446347070957694101

theorem tailTrace_231202 : CollatzResearch.WordTrace tailWord_231202 prefixEnd_231202 52763446347070957694101 := by
  unfold tailWord_231202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108157427100528750763965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5621753138934743335370573 2108157427100528750763965)
  ·
    refine ⟨790559035162698281536487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2108157427100528750763965 790559035162698281536487)
    ·
      refine ⟨1185838552744047422304731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 790559035162698281536487 1185838552744047422304731)
      ·
        refine ⟨1778757829116071133457097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185838552744047422304731 1778757829116071133457097)
        ·
          refine ⟨1334068371837053350092823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1778757829116071133457097 1334068371837053350092823)
          ·
            refine ⟨2001102557755580025139235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334068371837053350092823 2001102557755580025139235)
            ·
              refine ⟨3001653836633370037708853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001102557755580025139235 3001653836633370037708853)
              ·
                refine ⟨281405047184378441035205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3001653836633370037708853 281405047184378441035205)
                ·
                  refine ⟨52763446347070957694101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281405047184378441035205 52763446347070957694101)
                  ·
                    rfl

theorem cell21_231202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_231202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231202 prefixEnd_231202 := by exact prefixLift 231202
  have htrace : WordTrace (prefixWord ++ tailWord_231202) baseStart_231202 baseEnd_231202 := by
    simpa [prefixWord, tailWord_231202, baseEnd_231202] using wordTrace_append hprefix tailTrace_231202
  have hstable : (prefixWord ++ tailWord_231202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231202).length < 2 ^ (prefixWord ++ tailWord_231202).sum := by decide
  have hdescent : baseEnd_231202 < baseStart_231202 := by decide
  rcases family_descends (prefixWord ++ tailWord_231202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231222 : List Nat := [5, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_231222 : Nat := 118140960795 + 231222 * 2 ^ 59
def prefixEnd_231222 : Nat := 4983230072969 + 3 ^ 40 * 231222 * 2
def baseEnd_231222 : Nat := 52768010619555367360727

theorem tailTrace_231222 : CollatzResearch.WordTrace tailWord_231222 prefixEnd_231222 52768010619555367360727 := by
  unfold tailWord_231222
  simp only [CollatzResearch.WordTrace]
  refine ⟨527084948020603651173995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5622239445553105612522613 527084948020603651173995)
  ·
    refine ⟨790627422030905476760993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 527084948020603651173995 790627422030905476760993)
    ·
      refine ⟨592970566523179107570745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 790627422030905476760993 592970566523179107570745)
      ·
        refine ⟨444727924892384330678059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592970566523179107570745 444727924892384330678059)
        ·
          refine ⟨667091887338576496017089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444727924892384330678059 667091887338576496017089)
          ·
            refine ⟨500318915503932372012817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667091887338576496017089 500318915503932372012817)
            ·
              refine ⟨375239186627949279009613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500318915503932372012817 375239186627949279009613)
              ·
                refine ⟨140714694985480979628605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375239186627949279009613 140714694985480979628605)
                ·
                  refine ⟨52768010619555367360727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140714694985480979628605 52768010619555367360727)
                  ·
                    rfl

theorem cell21_231222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_231222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231222 prefixEnd_231222 := by exact prefixLift 231222
  have htrace : WordTrace (prefixWord ++ tailWord_231222) baseStart_231222 baseEnd_231222 := by
    simpa [prefixWord, tailWord_231222, baseEnd_231222] using wordTrace_append hprefix tailTrace_231222
  have hstable : (prefixWord ++ tailWord_231222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231222).length < 2 ^ (prefixWord ++ tailWord_231222).sum := by decide
  have hdescent : baseEnd_231222 < baseStart_231222 := by decide
  rcases family_descends (prefixWord ++ tailWord_231222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231278 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_231278 : Nat := 118140960795 + 231278 * 2 ^ 59
def prefixEnd_231278 : Nat := 4983230072969 + 3 ^ 40 * 231278 * 2
def baseEnd_231278 : Nat := 52780790582511714427279

theorem tailTrace_231278 : CollatzResearch.WordTrace tailWord_231278 prefixEnd_231278 52780790582511714427279 := by
  unfold tailWord_231278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054425207015847497852811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5623601104084519988548325 1054425207015847497852811)
  ·
    refine ⟨1581637810523771246779217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1054425207015847497852811 1581637810523771246779217)
    ·
      refine ⟨1186228357892828435084413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1581637810523771246779217 1186228357892828435084413)
      ·
        refine ⟨444835634209810663156655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1186228357892828435084413 444835634209810663156655)
        ·
          refine ⟨667253451314715994734983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444835634209810663156655 667253451314715994734983)
          ·
            refine ⟨1000880176972073992102475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667253451314715994734983 1000880176972073992102475)
            ·
              refine ⟨1501320265458110988153713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000880176972073992102475 1501320265458110988153713)
              ·
                refine ⟨1125990199093583241115285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501320265458110988153713 1125990199093583241115285)
                ·
                  refine ⟨52780790582511714427279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1125990199093583241115285 52780790582511714427279)
                  ·
                    rfl

theorem cell21_231278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_231278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231278 prefixEnd_231278 := by exact prefixLift 231278
  have htrace : WordTrace (prefixWord ++ tailWord_231278) baseStart_231278 baseEnd_231278 := by
    simpa [prefixWord, tailWord_231278, baseEnd_231278] using wordTrace_append hprefix tailTrace_231278
  have hstable : (prefixWord ++ tailWord_231278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231278).length < 2 ^ (prefixWord ++ tailWord_231278).sum := by decide
  have hdescent : baseEnd_231278 < baseStart_231278 := by decide
  rcases family_descends (prefixWord ++ tailWord_231278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231357 : List Nat := [1, 4, 1, 2, 3, 1, 4, 2, 3]
def baseStart_231357 : Nat := 118140960795 + 231357 * 2 ^ 59
def prefixEnd_231357 : Nat := 4983230072969 + 3 ^ 40 * 231357 * 2
def baseEnd_231357 : Nat := 52798819458825132610451

theorem tailTrace_231357 : CollatzResearch.WordTrace tailWord_231357 prefixEnd_231357 52798819458825132610451 := by
  unfold tailWord_231357
  simp only [CollatzResearch.WordTrace]
  refine ⟨8438283022840576474948325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5625522015227050983298883 8438283022840576474948325)
  ·
    refine ⟨1582178066782608089052811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8438283022840576474948325 1582178066782608089052811)
    ·
      refine ⟨2373267100173912133579217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582178066782608089052811 2373267100173912133579217)
      ·
        refine ⟨1779950325130434100184413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2373267100173912133579217 1779950325130434100184413)
        ·
          refine ⟨667481371923912787569155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1779950325130434100184413 667481371923912787569155)
          ·
            refine ⟨1001222057885869181353733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667481371923912787569155 1001222057885869181353733)
            ·
              refine ⟨187729135853600471503825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1001222057885869181353733 187729135853600471503825)
              ·
                refine ⟨140796851890200353627869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187729135853600471503825 140796851890200353627869)
                ·
                  refine ⟨52798819458825132610451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140796851890200353627869 52798819458825132610451)
                  ·
                    rfl

theorem cell21_231357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_231357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231357 prefixEnd_231357 := by exact prefixLift 231357
  have htrace : WordTrace (prefixWord ++ tailWord_231357) baseStart_231357 baseEnd_231357 := by
    simpa [prefixWord, tailWord_231357, baseEnd_231357] using wordTrace_append hprefix tailTrace_231357
  have hstable : (prefixWord ++ tailWord_231357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231357).length < 2 ^ (prefixWord ++ tailWord_231357).sum := by decide
  have hdescent : baseEnd_231357 < baseStart_231357 := by decide
  rcases family_descends (prefixWord ++ tailWord_231357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231368 : List Nat := [2, 1, 3, 1, 4, 1, 3, 6]
def baseStart_231368 : Nat := 118140960795 + 231368 * 2 ^ 59
def prefixEnd_231368 : Nat := 4983230072969 + 3 ^ 40 * 231368 * 2
def baseEnd_231368 : Nat := 17600443269563852642365

theorem tailTrace_231368 : CollatzResearch.WordTrace tailWord_231368 prefixEnd_231368 17600443269563852642365 := by
  unfold tailWord_231368
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219342112900362676799379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5625789483867150235732505 4219342112900362676799379)
  ·
    refine ⟨6329013169350544015199069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4219342112900362676799379 6329013169350544015199069)
    ·
      refine ⟨2373379938506454005699651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6329013169350544015199069 2373379938506454005699651)
      ·
        refine ⟨3560069907759681008549477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373379938506454005699651 3560069907759681008549477)
        ·
          refine ⟨667513107704940189103027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3560069907759681008549477 667513107704940189103027)
          ·
            refine ⟨1001269661557410283654541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667513107704940189103027 1001269661557410283654541)
            ·
              refine ⟨375476123084028856370453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1001269661557410283654541 375476123084028856370453)
              ·
                refine ⟨17600443269563852642365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 375476123084028856370453 17600443269563852642365)
                ·
                  rfl

theorem cell21_231368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_231368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231368 prefixEnd_231368 := by exact prefixLift 231368
  have htrace : WordTrace (prefixWord ++ tailWord_231368) baseStart_231368 baseEnd_231368 := by
    simpa [prefixWord, tailWord_231368, baseEnd_231368] using wordTrace_append hprefix tailTrace_231368
  have hstable : (prefixWord ++ tailWord_231368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231368).length < 2 ^ (prefixWord ++ tailWord_231368).sum := by decide
  have hdescent : baseEnd_231368 < baseStart_231368 := by decide
  rcases family_descends (prefixWord ++ tailWord_231368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231385 : List Nat := [1, 2, 1, 2, 6, 1, 3, 5]
def baseStart_231385 : Nat := 118140960795 + 231385 * 2 ^ 59
def prefixEnd_231385 : Nat := 4983230072969 + 3 ^ 40 * 231385 * 2
def baseEnd_231385 : Nat := 17601736480101102047909

theorem tailTrace_231385 : CollatzResearch.WordTrace tailWord_231385 prefixEnd_231385 17601736480101102047909 := by
  unfold tailWord_231385
  simp only [CollatzResearch.WordTrace]
  refine ⟨8439304266739137256967609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5626202844492758171311739 8439304266739137256967609)
  ·
    refine ⟨6329478200054352942725707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8439304266739137256967609 6329478200054352942725707)
    ·
      refine ⟨9494217300081529414088561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6329478200054352942725707 9494217300081529414088561)
      ·
        refine ⟨7120662975061147060566421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9494217300081529414088561 7120662975061147060566421)
        ·
          refine ⟨333781076955991268464051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7120662975061147060566421 333781076955991268464051)
          ·
            refine ⟨500671615433986902696077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333781076955991268464051 500671615433986902696077)
            ·
              refine ⟨187751855787745088511029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 500671615433986902696077 187751855787745088511029)
              ·
                refine ⟨17601736480101102047909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187751855787745088511029 17601736480101102047909)
                ·
                  rfl

theorem cell21_231385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 5].length) (baseStart_231385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231385 prefixEnd_231385 := by exact prefixLift 231385
  have htrace : WordTrace (prefixWord ++ tailWord_231385) baseStart_231385 baseEnd_231385 := by
    simpa [prefixWord, tailWord_231385, baseEnd_231385] using wordTrace_append hprefix tailTrace_231385
  have hstable : (prefixWord ++ tailWord_231385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231385).length < 2 ^ (prefixWord ++ tailWord_231385).sum := by decide
  have hdescent : baseEnd_231385 < baseStart_231385 := by decide
  rcases family_descends (prefixWord ++ tailWord_231385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231405 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 4]
def baseStart_231405 : Nat := 118140960795 + 231405 * 2 ^ 59
def prefixEnd_231405 : Nat := 4983230072969 + 3 ^ 40 * 231405 * 2
def baseEnd_231405 : Nat := 52809773712787715810353

theorem tailTrace_231405 : CollatzResearch.WordTrace tailWord_231405 prefixEnd_231405 52809773712787715810353 := by
  unfold tailWord_231405
  simp only [CollatzResearch.WordTrace]
  refine ⟨8440033726666680672695669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5626689151111120448463779 8440033726666680672695669)
  ·
    refine ⟨791253161875001313065219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8440033726666680672695669 791253161875001313065219)
    ·
      refine ⟨1186879742812501969597829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791253161875001313065219 1186879742812501969597829)
      ·
        refine ⟨222539951777344119299593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1186879742812501969597829 222539951777344119299593)
        ·
          refine ⟨166904963833008089474695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222539951777344119299593 166904963833008089474695)
          ·
            refine ⟨250357445749512134212043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166904963833008089474695 250357445749512134212043)
            ·
              refine ⟨375536168624268201318065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250357445749512134212043 375536168624268201318065)
              ·
                refine ⟨281652126468201150988549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375536168624268201318065 281652126468201150988549)
                ·
                  refine ⟨52809773712787715810353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281652126468201150988549 52809773712787715810353)
                  ·
                    rfl

theorem cell21_231405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_231405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231405 prefixEnd_231405 := by exact prefixLift 231405
  have htrace : WordTrace (prefixWord ++ tailWord_231405) baseStart_231405 baseEnd_231405 := by
    simpa [prefixWord, tailWord_231405, baseEnd_231405] using wordTrace_append hprefix tailTrace_231405
  have hstable : (prefixWord ++ tailWord_231405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231405).length < 2 ^ (prefixWord ++ tailWord_231405).sum := by decide
  have hdescent : baseEnd_231405 < baseStart_231405 := by decide
  rcases family_descends (prefixWord ++ tailWord_231405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231475 : List Nat := [1, 1, 1, 2, 4, 1, 2, 6, 3]
def baseStart_231475 : Nat := 118140960795 + 231475 * 2 ^ 59
def prefixEnd_231475 : Nat := 4983230072969 + 3 ^ 40 * 231475 * 2
def baseEnd_231475 : Nat := 52825748666483149643543

theorem tailTrace_231475 : CollatzResearch.WordTrace tailWord_231475 prefixEnd_231475 52825748666483149643543 := by
  unfold tailWord_231475
  simp only [CollatzResearch.WordTrace]
  refine ⟨8442586836413082627743879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5628391224275388418495919 8442586836413082627743879)
  ·
    refine ⟨12663880254619623941615819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8442586836413082627743879 12663880254619623941615819)
    ·
      refine ⟨18995820381929435912423729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12663880254619623941615819 18995820381929435912423729)
      ·
        refine ⟨14246865286447076934317797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18995820381929435912423729 14246865286447076934317797)
        ·
          refine ⟨2671287241208826925184587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14246865286447076934317797 2671287241208826925184587)
          ·
            refine ⟨4006930861813240387776881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671287241208826925184587 4006930861813240387776881)
            ·
              refine ⟨3005198146359930290832661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4006930861813240387776881 3005198146359930290832661)
              ·
                refine ⟨140868663110621732382781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3005198146359930290832661 140868663110621732382781)
                ·
                  refine ⟨52825748666483149643543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140868663110621732382781 52825748666483149643543)
                  ·
                    rfl

theorem cell21_231475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 3].length) (baseStart_231475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231475 prefixEnd_231475 := by exact prefixLift 231475
  have htrace : WordTrace (prefixWord ++ tailWord_231475) baseStart_231475 baseEnd_231475 := by
    simpa [prefixWord, tailWord_231475, baseEnd_231475] using wordTrace_append hprefix tailTrace_231475
  have hstable : (prefixWord ++ tailWord_231475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231475).length < 2 ^ (prefixWord ++ tailWord_231475).sum := by decide
  have hdescent : baseEnd_231475 < baseStart_231475 := by decide
  rcases family_descends (prefixWord ++ tailWord_231475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231610 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_231610 : Nat := 118140960795 + 231610 * 2 ^ 59
def prefixEnd_231610 : Nat := 4983230072969 + 3 ^ 40 * 231610 * 2
def baseEnd_231610 : Nat := 52856557505752914893267

theorem tailTrace_231610 : CollatzResearch.WordTrace tailWord_231610 prefixEnd_231610 52856557505752914893267 := by
  unfold tailWord_231610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111877672731000170977071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5631673793949333789272189 2111877672731000170977071)
  ·
    refine ⟨3167816509096500256465607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2111877672731000170977071 3167816509096500256465607)
    ·
      refine ⟨4751724763644750384698411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3167816509096500256465607 4751724763644750384698411)
      ·
        refine ⟨7127587145467125577047617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4751724763644750384698411 7127587145467125577047617)
        ·
          refine ⟨5345690359100344182785713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7127587145467125577047617 5345690359100344182785713)
          ·
            refine ⟨4009267769325258137089285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5345690359100344182785713 4009267769325258137089285)
            ·
              refine ⟨751737706748485900704241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4009267769325258137089285 751737706748485900704241)
              ·
                refine ⟨563803280061364425528181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751737706748485900704241 563803280061364425528181)
                ·
                  refine ⟨52856557505752914893267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 563803280061364425528181 52856557505752914893267)
                  ·
                    rfl

theorem cell21_231610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_231610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231610 prefixEnd_231610 := by exact prefixLift 231610
  have htrace : WordTrace (prefixWord ++ tailWord_231610) baseStart_231610 baseEnd_231610 := by
    simpa [prefixWord, tailWord_231610, baseEnd_231610] using wordTrace_append hprefix tailTrace_231610
  have hstable : (prefixWord ++ tailWord_231610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231610).length < 2 ^ (prefixWord ++ tailWord_231610).sum := by decide
  have hdescent : baseEnd_231610 < baseStart_231610 := by decide
  rcases family_descends (prefixWord ++ tailWord_231610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231650 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 4]
def baseStart_231650 : Nat := 118140960795 + 231650 * 2 ^ 59
def prefixEnd_231650 : Nat := 4983230072969 + 3 ^ 40 * 231650 * 2
def baseEnd_231650 : Nat := 52865686050721734226519

theorem tailTrace_231650 : CollatzResearch.WordTrace tailWord_231650 prefixEnd_231650 52865686050721734226519 := by
  unfold tailWord_231650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112242402694771878841101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5632646407186058343576269 2112242402694771878841101)
  ·
    refine ⟨792090901010539454565413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2112242402694771878841101 792090901010539454565413)
    ·
      refine ⟨148517043939476147731015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 792090901010539454565413 148517043939476147731015)
      ·
        refine ⟨222775565909214221596523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148517043939476147731015 222775565909214221596523)
        ·
          refine ⟨334163348863821332394785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222775565909214221596523 334163348863821332394785)
          ·
            refine ⟨250622511647865999296089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334163348863821332394785 250622511647865999296089)
            ·
              refine ⟨187966883735899499472067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250622511647865999296089 187966883735899499472067)
              ·
                refine ⟨281950325603849249208101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187966883735899499472067 281950325603849249208101)
                ·
                  refine ⟨52865686050721734226519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281950325603849249208101 52865686050721734226519)
                  ·
                    rfl

theorem cell21_231650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_231650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231650 prefixEnd_231650 := by exact prefixLift 231650
  have htrace : WordTrace (prefixWord ++ tailWord_231650) baseStart_231650 baseEnd_231650 := by
    simpa [prefixWord, tailWord_231650, baseEnd_231650] using wordTrace_append hprefix tailTrace_231650
  have hstable : (prefixWord ++ tailWord_231650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231650).length < 2 ^ (prefixWord ++ tailWord_231650).sum := by decide
  have hdescent : baseEnd_231650 < baseStart_231650 := by decide
  rcases family_descends (prefixWord ++ tailWord_231650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231762 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_231762 : Nat := 118140960795 + 231762 * 2 ^ 59
def prefixEnd_231762 : Nat := 4983230072969 + 3 ^ 40 * 231762 * 2
def baseEnd_231762 : Nat := 52891245976634428359623

theorem tailTrace_231762 : CollatzResearch.WordTrace tailWord_231762 prefixEnd_231762 52891245976634428359623 := by
  unfold tailWord_231762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2113263646593332660860385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5635369724248887095627693 2113263646593332660860385)
  ·
    refine ⟨1584947734944999495645289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2113263646593332660860385 1584947734944999495645289)
    ·
      refine ⟨1188710801208749621733967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1584947734944999495645289 1188710801208749621733967)
      ·
        refine ⟨1783066201813124432600951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188710801208749621733967 1783066201813124432600951)
        ·
          refine ⟨2674599302719686648901427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783066201813124432600951 2674599302719686648901427)
          ·
            refine ⟨4011898954079529973352141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674599302719686648901427 4011898954079529973352141)
            ·
              refine ⟨1504462107779823740007053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4011898954079529973352141 1504462107779823740007053)
              ·
                refine ⟨564173290417433902502645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1504462107779823740007053 564173290417433902502645)
                ·
                  refine ⟨52891245976634428359623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 564173290417433902502645 52891245976634428359623)
                  ·
                    rfl

theorem cell21_231762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_231762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231762 prefixEnd_231762 := by exact prefixLift 231762
  have htrace : WordTrace (prefixWord ++ tailWord_231762) baseStart_231762 baseEnd_231762 := by
    simpa [prefixWord, tailWord_231762, baseEnd_231762] using wordTrace_append hprefix tailTrace_231762
  have hstable : (prefixWord ++ tailWord_231762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231762).length < 2 ^ (prefixWord ++ tailWord_231762).sum := by decide
  have hdescent : baseEnd_231762 < baseStart_231762 := by decide
  rcases family_descends (prefixWord ++ tailWord_231762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231869 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 4]
def baseStart_231869 : Nat := 118140960795 + 231869 * 2 ^ 59
def prefixEnd_231869 : Nat := 4983230072969 + 3 ^ 40 * 231869 * 2
def baseEnd_231869 : Nat := 52915664834426020076071

theorem tailTrace_231869 : CollatzResearch.WordTrace tailWord_231869 prefixEnd_231869 52915664834426020076071 := by
  unfold tailWord_231869
  simp only [CollatzResearch.WordTrace]
  refine ⟨8456957196985687917586661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5637971464657125278391107 8456957196985687917586661)
  ·
    refine ⟨1585679474434816484547499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8456957196985687917586661 1585679474434816484547499)
    ·
      refine ⟨2378519211652224726821249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1585679474434816484547499 2378519211652224726821249)
      ·
        refine ⟨1783889408739168545115937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2378519211652224726821249 1783889408739168545115937)
        ·
          refine ⟨1337917056554376408836953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1783889408739168545115937 1337917056554376408836953)
          ·
            refine ⟨1003437792415782306627715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1337917056554376408836953 1003437792415782306627715)
            ·
              refine ⟨1505156688623673459941573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003437792415782306627715 1505156688623673459941573)
              ·
                refine ⟨282216879116938773739045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1505156688623673459941573 282216879116938773739045)
                ·
                  refine ⟨52915664834426020076071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282216879116938773739045 52915664834426020076071)
                  ·
                    rfl

theorem cell21_231869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_231869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231869 prefixEnd_231869 := by exact prefixLift 231869
  have htrace : WordTrace (prefixWord ++ tailWord_231869) baseStart_231869 baseEnd_231869 := by
    simpa [prefixWord, tailWord_231869, baseEnd_231869] using wordTrace_append hprefix tailTrace_231869
  have hstable : (prefixWord ++ tailWord_231869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231869).length < 2 ^ (prefixWord ++ tailWord_231869).sum := by decide
  have hdescent : baseEnd_231869 < baseStart_231869 := by decide
  rcases family_descends (prefixWord ++ tailWord_231869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231906 : List Nat := [3, 3, 3, 2, 1, 1, 2, 3, 3]
def baseStart_231906 : Nat := 118140960795 + 231906 * 2 ^ 59
def prefixEnd_231906 : Nat := 4983230072969 + 3 ^ 40 * 231906 * 2
def baseEnd_231906 : Nat := 52924108738522177959329

theorem tailTrace_231906 : CollatzResearch.WordTrace tailWord_231906 prefixEnd_231906 52924108738522177959329 := by
  unfold tailWord_231906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2114576674462910809170893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5638871131901095491122381 2114576674462910809170893)
  ·
    refine ⟨792966252923591553439085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2114576674462910809170893 792966252923591553439085)
    ·
      refine ⟨297362344846346832539657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 792966252923591553439085 297362344846346832539657)
      ·
        refine ⟨223021758634760124404743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297362344846346832539657 223021758634760124404743)
        ·
          refine ⟨334532637952140186607115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223021758634760124404743 334532637952140186607115)
          ·
            refine ⟨501798956928210279910673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334532637952140186607115 501798956928210279910673)
            ·
              refine ⟨376349217696157709933005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501798956928210279910673 376349217696157709933005)
              ·
                refine ⟨141130956636059141224877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376349217696157709933005 141130956636059141224877)
                ·
                  refine ⟨52924108738522177959329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141130956636059141224877 52924108738522177959329)
                  ·
                    rfl

theorem cell21_231906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_231906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231906 prefixEnd_231906 := by exact prefixLift 231906
  have htrace : WordTrace (prefixWord ++ tailWord_231906) baseStart_231906 baseEnd_231906 := by
    simpa [prefixWord, tailWord_231906, baseEnd_231906] using wordTrace_append hprefix tailTrace_231906
  have hstable : (prefixWord ++ tailWord_231906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231906).length < 2 ^ (prefixWord ++ tailWord_231906).sum := by decide
  have hdescent : baseEnd_231906 < baseStart_231906 := by decide
  rcases family_descends (prefixWord ++ tailWord_231906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231928 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_231928 : Nat := 118140960795 + 231928 * 2 ^ 59
def prefixEnd_231928 : Nat := 4983230072969 + 3 ^ 40 * 231928 * 2
def baseEnd_231928 : Nat := 52929129438255028592617

theorem tailTrace_231928 : CollatzResearch.WordTrace tailWord_231928 prefixEnd_231928 52929129438255028592617 := by
  unfold tailWord_231928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229554551885970496992219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5639406069181293995989625 4229554551885970496992219)
  ·
    refine ⟨6344331827828955745488329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4229554551885970496992219 6344331827828955745488329)
    ·
      refine ⟨4758248870871716809116247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6344331827828955745488329 4758248870871716809116247)
      ·
        refine ⟨7137373306307575213674371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758248870871716809116247 7137373306307575213674371)
        ·
          refine ⟨10706059959461362820511557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7137373306307575213674371 10706059959461362820511557)
          ·
            refine ⟨2007386242399005528845917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10706059959461362820511557 2007386242399005528845917)
            ·
              refine ⟨752769840899627073317219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2007386242399005528845917 752769840899627073317219)
              ·
                refine ⟨1129154761349440609975829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752769840899627073317219 1129154761349440609975829)
                ·
                  refine ⟨52929129438255028592617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1129154761349440609975829 52929129438255028592617)
                  ·
                    rfl

theorem cell21_231928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_231928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231928 prefixEnd_231928 := by exact prefixLift 231928
  have htrace : WordTrace (prefixWord ++ tailWord_231928) baseStart_231928 baseEnd_231928 := by
    simpa [prefixWord, tailWord_231928, baseEnd_231928] using wordTrace_append hprefix tailTrace_231928
  have hstable : (prefixWord ++ tailWord_231928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231928).length < 2 ^ (prefixWord ++ tailWord_231928).sum := by decide
  have hdescent : baseEnd_231928 < baseStart_231928 := by decide
  rcases family_descends (prefixWord ++ tailWord_231928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231973 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 7]
def baseStart_231973 : Nat := 118140960795 + 231973 * 2 ^ 59
def prefixEnd_231973 : Nat := 4983230072969 + 3 ^ 40 * 231973 * 2
def baseEnd_231973 : Nat := 52939399051344950342525

theorem tailTrace_231973 : CollatzResearch.WordTrace tailWord_231973 prefixEnd_231973 52939399051344950342525 := by
  unfold tailWord_231973
  simp only [CollatzResearch.WordTrace]
  refine ⟨8460750388608913679372573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5640500259072609119581715 8460750388608913679372573)
  ·
    refine ⟨3172781395728342629764715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8460750388608913679372573 3172781395728342629764715)
    ·
      refine ⟨4759172093592513944647073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3172781395728342629764715 4759172093592513944647073)
      ·
        refine ⟨3569379070194385458485305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4759172093592513944647073 3569379070194385458485305)
        ·
          refine ⟨2677034302645789093863979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3569379070194385458485305 2677034302645789093863979)
          ·
            refine ⟨4015551453968683640795969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677034302645789093863979 4015551453968683640795969)
            ·
              refine ⟨3011663590476512730596977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4015551453968683640795969 3011663590476512730596977)
              ·
                refine ⟨2258747692857384547947733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011663590476512730596977 2258747692857384547947733)
                ·
                  refine ⟨52939399051344950342525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2258747692857384547947733 52939399051344950342525)
                  ·
                    rfl

theorem cell21_231973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_231973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231973 prefixEnd_231973 := by exact prefixLift 231973
  have htrace : WordTrace (prefixWord ++ tailWord_231973) baseStart_231973 baseEnd_231973 := by
    simpa [prefixWord, tailWord_231973, baseEnd_231973] using wordTrace_append hprefix tailTrace_231973
  have hstable : (prefixWord ++ tailWord_231973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231973).length < 2 ^ (prefixWord ++ tailWord_231973).sum := by decide
  have hdescent : baseEnd_231973 < baseStart_231973 := by decide
  rcases family_descends (prefixWord ++ tailWord_231973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231976 : List Nat := [2, 1, 5, 2, 1, 3, 7]
def baseStart_231976 : Nat := 118140960795 + 231976 * 2 ^ 59
def prefixEnd_231976 : Nat := 4983230072969 + 3 ^ 40 * 231976 * 2
def baseEnd_231976 : Nat := 5882231521357512421391

theorem tailTrace_231976 : CollatzResearch.WordTrace tailWord_231976 prefixEnd_231976 5882231521357512421391 := by
  unfold tailWord_231976
  simp only [CollatzResearch.WordTrace]
  refine ⟨4230429903799022595865891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5640573205065363461154521 4230429903799022595865891)
  ·
    refine ⟨6345644855698533893798837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4230429903799022595865891 6345644855698533893798837)
    ·
      refine ⟨594904205221737552543641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6345644855698533893798837 594904205221737552543641)
      ·
        refine ⟨446178153916303164407731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594904205221737552543641 446178153916303164407731)
        ·
          refine ⟨669267230874454746611597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446178153916303164407731 669267230874454746611597)
          ·
            refine ⟨250975211577920529979349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 669267230874454746611597 250975211577920529979349)
            ·
              refine ⟨5882231521357512421391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 250975211577920529979349 5882231521357512421391)
              ·
                rfl

theorem cell21_231976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 7].length) (baseStart_231976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_231976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_231976 prefixEnd_231976 := by exact prefixLift 231976
  have htrace : WordTrace (prefixWord ++ tailWord_231976) baseStart_231976 baseEnd_231976 := by
    simpa [prefixWord, tailWord_231976, baseEnd_231976] using wordTrace_append hprefix tailTrace_231976
  have hstable : (prefixWord ++ tailWord_231976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231976).length < 2 ^ (prefixWord ++ tailWord_231976).sum := by decide
  have hdescent : baseEnd_231976 < baseStart_231976 := by decide
  rcases family_descends (prefixWord ++ tailWord_231976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232097 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 6]
def baseStart_232097 : Nat := 118140960795 + 232097 * 2 ^ 59
def prefixEnd_232097 : Nat := 4983230072969 + 3 ^ 40 * 232097 * 2
def baseEnd_232097 : Nat := 52967697540748290275605

theorem tailTrace_232097 : CollatzResearch.WordTrace tailWord_232097 prefixEnd_232097 52967697540748290275605 := by
  unfold tailWord_232097
  simp only [CollatzResearch.WordTrace]
  refine ⟨8465273040159682856886545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5643515360106455237924363 8465273040159682856886545)
  ·
    refine ⟨6348954780119762142664909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8465273040159682856886545 6348954780119762142664909)
    ·
      refine ⟨2380858042544910803499341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6348954780119762142664909 2380858042544910803499341)
      ·
        refine ⟨892821765954341551312253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2380858042544910803499341 892821765954341551312253)
        ·
          refine ⟨334808162232878081742095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 892821765954341551312253 334808162232878081742095)
          ·
            refine ⟨502212243349317122613143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334808162232878081742095 502212243349317122613143)
            ·
              refine ⟨753318365023975683919715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502212243349317122613143 753318365023975683919715)
              ·
                refine ⟨1129977547535963525879573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753318365023975683919715 1129977547535963525879573)
                ·
                  refine ⟨52967697540748290275605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1129977547535963525879573 52967697540748290275605)
                  ·
                    rfl

theorem cell21_232097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_232097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232097 prefixEnd_232097 := by exact prefixLift 232097
  have htrace : WordTrace (prefixWord ++ tailWord_232097) baseStart_232097 baseEnd_232097 := by
    simpa [prefixWord, tailWord_232097, baseEnd_232097] using wordTrace_append hprefix tailTrace_232097
  have hstable : (prefixWord ++ tailWord_232097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232097).length < 2 ^ (prefixWord ++ tailWord_232097).sum := by decide
  have hdescent : baseEnd_232097 < baseStart_232097 := by decide
  rcases family_descends (prefixWord ++ tailWord_232097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232128 : List Nat := [2, 1, 1, 2, 4, 4, 2, 5]
def baseStart_232128 : Nat := 118140960795 + 232128 * 2 ^ 59
def prefixEnd_232128 : Nat := 4983230072969 + 3 ^ 40 * 232128 * 2
def baseEnd_232128 : Nat := 17658257387699708419625

theorem tailTrace_232128 : CollatzResearch.WordTrace tailWord_232128 prefixEnd_232128 17658257387699708419625 := by
  unfold tailWord_232128
  simp only [CollatzResearch.WordTrace]
  refine ⟨4233201851523687575632519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5644269135364916767510025 4233201851523687575632519)
  ·
    refine ⟨6349802777285531363448779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4233201851523687575632519 6349802777285531363448779)
    ·
      refine ⟨9524704165928297045173169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6349802777285531363448779 9524704165928297045173169)
      ·
        refine ⟨7143528124446222783879877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9524704165928297045173169 7143528124446222783879877)
        ·
          refine ⟨1339411523333666771977477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7143528124446222783879877 1339411523333666771977477)
          ·
            refine ⟨251139660625062519745777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1339411523333666771977477 251139660625062519745777)
            ·
              refine ⟨188354745468796889809333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251139660625062519745777 188354745468796889809333)
              ·
                refine ⟨17658257387699708419625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188354745468796889809333 17658257387699708419625)
                ·
                  rfl

theorem cell21_232128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_232128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232128 prefixEnd_232128 := by exact prefixLift 232128
  have htrace : WordTrace (prefixWord ++ tailWord_232128) baseStart_232128 baseEnd_232128 := by
    simpa [prefixWord, tailWord_232128, baseEnd_232128] using wordTrace_append hprefix tailTrace_232128
  have hstable : (prefixWord ++ tailWord_232128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232128).length < 2 ^ (prefixWord ++ tailWord_232128).sum := by decide
  have hdescent : baseEnd_232128 < baseStart_232128 := by decide
  rcases family_descends (prefixWord ++ tailWord_232128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232173 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 4]
def baseStart_232173 : Nat := 118140960795 + 232173 * 2 ^ 59
def prefixEnd_232173 : Nat := 4983230072969 + 3 ^ 40 * 232173 * 2
def baseEnd_232173 : Nat := 52985041776189047008783

theorem tailTrace_232173 : CollatzResearch.WordTrace tailWord_232173 prefixEnd_232173 52985041776189047008783 := by
  unfold tailWord_232173
  simp only [CollatzResearch.WordTrace]
  refine ⟨8468044987884347836653173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5645363325256231891102115 8468044987884347836653173)
  ·
    refine ⟨793879217614157609686235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8468044987884347836653173 793879217614157609686235)
    ·
      refine ⟨1190818826421236414529353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 793879217614157609686235 1190818826421236414529353)
      ·
        refine ⟨893114119815927310897015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1190818826421236414529353 893114119815927310897015)
        ·
          refine ⟨1339671179723890966345523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893114119815927310897015 1339671179723890966345523)
          ·
            refine ⟨2009506769585836449518285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339671179723890966345523 2009506769585836449518285)
            ·
              refine ⟨753565038594688668569357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2009506769585836449518285 753565038594688668569357)
              ·
                refine ⟨282586889473008250713509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 753565038594688668569357 282586889473008250713509)
                ·
                  refine ⟨52985041776189047008783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282586889473008250713509 52985041776189047008783)
                  ·
                    rfl

theorem cell21_232173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_232173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232173 prefixEnd_232173 := by exact prefixLift 232173
  have htrace : WordTrace (prefixWord ++ tailWord_232173) baseStart_232173 baseEnd_232173 := by
    simpa [prefixWord, tailWord_232173, baseEnd_232173] using wordTrace_append hprefix tailTrace_232173
  have hstable : (prefixWord ++ tailWord_232173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232173).length < 2 ^ (prefixWord ++ tailWord_232173).sum := by decide
  have hdescent : baseEnd_232173 < baseStart_232173 := by decide
  rcases family_descends (prefixWord ++ tailWord_232173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232210 : List Nat := [3, 2, 4, 1, 2, 2, 2, 2, 3]
def baseStart_232210 : Nat := 118140960795 + 232210 * 2 ^ 59
def prefixEnd_232210 : Nat := 4983230072969 + 3 ^ 40 * 232210 * 2
def baseEnd_232210 : Nat := 52993485680285204892041

theorem tailTrace_232210 : CollatzResearch.WordTrace tailWord_232210 prefixEnd_232210 52993485680285204892041 := by
  unfold tailWord_232210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2117348622187575788937521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5646262992500202103833389 2117348622187575788937521)
  ·
    refine ⟨1588011466640681841703141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2117348622187575788937521 1588011466640681841703141)
    ·
      refine ⟨297752149995127845319339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1588011466640681841703141 297752149995127845319339)
      ·
        refine ⟨446628224992691767979009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297752149995127845319339 446628224992691767979009)
        ·
          refine ⟨334971168744518825984257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446628224992691767979009 334971168744518825984257)
          ·
            refine ⟨251228376558389119488193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334971168744518825984257 251228376558389119488193)
            ·
              refine ⟨188421282418791839616145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251228376558389119488193 188421282418791839616145)
              ·
                refine ⟨141315961814093879712109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188421282418791839616145 141315961814093879712109)
                ·
                  refine ⟨52993485680285204892041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141315961814093879712109 52993485680285204892041)
                  ·
                    rfl

theorem cell21_232210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_232210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232210 prefixEnd_232210 := by exact prefixLift 232210
  have htrace : WordTrace (prefixWord ++ tailWord_232210) baseStart_232210 baseEnd_232210 := by
    simpa [prefixWord, tailWord_232210, baseEnd_232210] using wordTrace_append hprefix tailTrace_232210
  have hstable : (prefixWord ++ tailWord_232210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232210).length < 2 ^ (prefixWord ++ tailWord_232210).sum := by decide
  have hdescent : baseEnd_232210 < baseStart_232210 := by decide
  rcases family_descends (prefixWord ++ tailWord_232210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232221 : List Nat := [1, 4, 2, 4, 1, 2, 1, 6]
def baseStart_232221 : Nat := 118140960795 + 232221 * 2 ^ 59
def prefixEnd_232221 : Nat := 4983230072969 + 3 ^ 40 * 232221 * 2
def baseEnd_232221 : Nat := 17665332010050543402895

theorem tailTrace_232221 : CollatzResearch.WordTrace tailWord_232221 prefixEnd_232221 17665332010050543402895 := by
  unfold tailWord_232221
  simp only [CollatzResearch.WordTrace]
  refine ⟨8469795691710452034400517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5646530461140301356267011 8469795691710452034400517)
  ·
    refine ⟨1588086692195709756450097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8469795691710452034400517 1588086692195709756450097)
    ·
      refine ⟨1191065019146782317337573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1588086692195709756450097 1191065019146782317337573)
      ·
        refine ⟨223324691090021684500795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1191065019146782317337573 223324691090021684500795)
        ·
          refine ⟨334987036635032526751193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223324691090021684500795 334987036635032526751193)
          ·
            refine ⟨251240277476274395063395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334987036635032526751193 251240277476274395063395)
            ·
              refine ⟨376860416214411592595093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251240277476274395063395 376860416214411592595093)
              ·
                refine ⟨17665332010050543402895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 376860416214411592595093 17665332010050543402895)
                ·
                  rfl

theorem cell21_232221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 6].length) (baseStart_232221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232221 prefixEnd_232221 := by exact prefixLift 232221
  have htrace : WordTrace (prefixWord ++ tailWord_232221) baseStart_232221 baseEnd_232221 := by
    simpa [prefixWord, tailWord_232221, baseEnd_232221] using wordTrace_append hprefix tailTrace_232221
  have hstable : (prefixWord ++ tailWord_232221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232221).length < 2 ^ (prefixWord ++ tailWord_232221).sum := by decide
  have hdescent : baseEnd_232221 < baseStart_232221 := by decide
  rcases family_descends (prefixWord ++ tailWord_232221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232328 : List Nat := [2, 1, 3, 3, 2, 2, 3, 2, 3]
def baseStart_232328 : Nat := 118140960795 + 232328 * 2 ^ 59
def prefixEnd_232328 : Nat := 4983230072969 + 3 ^ 40 * 232328 * 2
def baseEnd_232328 : Nat := 53020414887943221925133

theorem tailTrace_232328 : CollatzResearch.WordTrace tailWord_232328 prefixEnd_232328 53020414887943221925133 := by
  unfold tailWord_232328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236849151161404654272819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5649132201548539539030425 4236849151161404654272819)
  ·
    refine ⟨6355273726742106981409229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4236849151161404654272819 6355273726742106981409229)
    ·
      refine ⟨2383227647528290118028461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6355273726742106981409229 2383227647528290118028461)
      ·
        refine ⟨893710367823108794260673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2383227647528290118028461 893710367823108794260673)
        ·
          refine ⟨670282775867331595695505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 893710367823108794260673 670282775867331595695505)
          ·
            refine ⟨502712081900498696771629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670282775867331595695505 502712081900498696771629)
            ·
              refine ⟨188517030712687011289361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502712081900498696771629 188517030712687011289361)
              ·
                refine ⟨141387773034515258467021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188517030712687011289361 141387773034515258467021)
                ·
                  refine ⟨53020414887943221925133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141387773034515258467021 53020414887943221925133)
                  ·
                    rfl

theorem cell21_232328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 3].length) (baseStart_232328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232328 prefixEnd_232328 := by exact prefixLift 232328
  have htrace : WordTrace (prefixWord ++ tailWord_232328) baseStart_232328 baseEnd_232328 := by
    simpa [prefixWord, tailWord_232328, baseEnd_232328] using wordTrace_append hprefix tailTrace_232328
  have hstable : (prefixWord ++ tailWord_232328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232328).length < 2 ^ (prefixWord ++ tailWord_232328).sum := by decide
  have hdescent : baseEnd_232328 < baseStart_232328 := by decide
  rcases family_descends (prefixWord ++ tailWord_232328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232367 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 6]
def baseStart_232367 : Nat := 118140960795 + 232367 * 2 ^ 59
def prefixEnd_232367 : Nat := 4983230072969 + 3 ^ 40 * 232367 * 2
def baseEnd_232367 : Nat := 53029315219287820775053

theorem tailTrace_232367 : CollatzResearch.WordTrace tailWord_232367 prefixEnd_232367 53029315219287820775053 := by
  unfold tailWord_232367
  simp only [CollatzResearch.WordTrace]
  refine ⟨8475120749181518969215355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5650080499454345979476903 8475120749181518969215355)
  ·
    refine ⟨12712681123772278453823033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8475120749181518969215355 12712681123772278453823033)
    ·
      refine ⟨9534510842829208840367275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12712681123772278453823033 9534510842829208840367275)
      ·
        refine ⟨14301766264243813260550913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9534510842829208840367275 14301766264243813260550913)
        ·
          refine ⟨10726324698182859945413185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14301766264243813260550913 10726324698182859945413185)
          ·
            refine ⟨8044743523637144959059889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10726324698182859945413185 8044743523637144959059889)
            ·
              refine ⟨6033557642727858719294917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8044743523637144959059889 6033557642727858719294917)
              ·
                refine ⟨1131292058011473509867797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6033557642727858719294917 1131292058011473509867797)
                ·
                  refine ⟨53029315219287820775053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1131292058011473509867797 53029315219287820775053)
                  ·
                    rfl

theorem cell21_232367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_232367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232367 prefixEnd_232367 := by exact prefixLift 232367
  have htrace : WordTrace (prefixWord ++ tailWord_232367) baseStart_232367 baseEnd_232367 := by
    simpa [prefixWord, tailWord_232367, baseEnd_232367] using wordTrace_append hprefix tailTrace_232367
  have hstable : (prefixWord ++ tailWord_232367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232367).length < 2 ^ (prefixWord ++ tailWord_232367).sum := by decide
  have hdescent : baseEnd_232367 < baseStart_232367 := by decide
  rcases family_descends (prefixWord ++ tailWord_232367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232384 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 4]
def baseStart_232384 : Nat := 118140960795 + 232384 * 2 ^ 59
def prefixEnd_232384 : Nat := 4983230072969 + 3 ^ 40 * 232384 * 2
def baseEnd_232384 : Nat := 53033194850899568991685

theorem tailTrace_232384 : CollatzResearch.WordTrace tailWord_232384 prefixEnd_232384 53033194850899568991685 := by
  unfold tailWord_232384
  simp only [CollatzResearch.WordTrace]
  refine ⟨4237870395059965436292103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5650493860079953915056137 4237870395059965436292103)
  ·
    refine ⟨6356805592589948154438155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4237870395059965436292103 6356805592589948154438155)
    ·
      refine ⟨9535208388884922231657233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6356805592589948154438155 9535208388884922231657233)
      ·
        refine ⟨7151406291663691673742925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9535208388884922231657233 7151406291663691673742925)
        ·
          refine ⟨2681777359373884377653597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7151406291663691673742925 2681777359373884377653597)
          ·
            refine ⟨1005666509765206641620099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2681777359373884377653597 1005666509765206641620099)
            ·
              refine ⟨1508499764647809962430149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005666509765206641620099 1508499764647809962430149)
              ·
                refine ⟨282843705871464367955653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1508499764647809962430149 282843705871464367955653)
                ·
                  refine ⟨53033194850899568991685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282843705871464367955653 53033194850899568991685)
                  ·
                    rfl

theorem cell21_232384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_232384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232384 prefixEnd_232384 := by exact prefixLift 232384
  have htrace : WordTrace (prefixWord ++ tailWord_232384) baseStart_232384 baseEnd_232384 := by
    simpa [prefixWord, tailWord_232384, baseEnd_232384] using wordTrace_append hprefix tailTrace_232384
  have hstable : (prefixWord ++ tailWord_232384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232384).length < 2 ^ (prefixWord ++ tailWord_232384).sum := by decide
  have hdescent : baseEnd_232384 < baseStart_232384 := by decide
  rcases family_descends (prefixWord ++ tailWord_232384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232474 : List Nat := [3, 1, 1, 3, 1, 2, 3, 7]
def baseStart_232474 : Nat := 118140960795 + 232474 * 2 ^ 59
def prefixEnd_232474 : Nat := 4983230072969 + 3 ^ 40 * 232474 * 2
def baseEnd_232474 : Nat := 17684578025693137497167

theorem tailTrace_232474 : CollatzResearch.WordTrace tailWord_232474 prefixEnd_232474 17684578025693137497167 := by
  unfold tailWord_232474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119755839948469060840119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5652682239862584162240317 2119755839948469060840119)
  ·
    refine ⟨3179633759922703591260179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2119755839948469060840119 3179633759922703591260179)
    ·
      refine ⟨4769450639884055386890269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3179633759922703591260179 4769450639884055386890269)
      ·
        refine ⟨1788543989956520770083851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4769450639884055386890269 1788543989956520770083851)
        ·
          refine ⟨2682815984934781155125777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788543989956520770083851 2682815984934781155125777)
          ·
            refine ⟨2012111988701085866344333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2682815984934781155125777 2012111988701085866344333)
            ·
              refine ⟨754541995762907199879125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2012111988701085866344333 754541995762907199879125)
              ·
                refine ⟨17684578025693137497167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 754541995762907199879125 17684578025693137497167)
                ·
                  rfl

theorem cell21_232474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_232474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232474 prefixEnd_232474 := by exact prefixLift 232474
  have htrace : WordTrace (prefixWord ++ tailWord_232474) baseStart_232474 baseEnd_232474 := by
    simpa [prefixWord, tailWord_232474, baseEnd_232474] using wordTrace_append hprefix tailTrace_232474
  have hstable : (prefixWord ++ tailWord_232474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232474).length < 2 ^ (prefixWord ++ tailWord_232474).sum := by decide
  have hdescent : baseEnd_232474 < baseStart_232474 := by decide
  rcases family_descends (prefixWord ++ tailWord_232474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232584 : List Nat := [2, 1, 3, 4, 2, 1, 3, 5]
def baseStart_232584 : Nat := 118140960795 + 232584 * 2 ^ 59
def prefixEnd_232584 : Nat := 4983230072969 + 3 ^ 40 * 232584 * 2
def baseEnd_232584 : Nat := 17692945858581221885981

theorem tailTrace_232584 : CollatzResearch.WordTrace tailWord_232584 prefixEnd_232584 17692945858581221885981 := by
  unfold tailWord_232584
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241517694697682514932403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5655356926263576686576537 4241517694697682514932403)
  ·
    refine ⟨6362276542046523772398605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4241517694697682514932403 6362276542046523772398605)
    ·
      refine ⟨2385853703267446414649477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6362276542046523772398605 2385853703267446414649477)
      ·
        refine ⟨447347569362646202746777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2385853703267446414649477 447347569362646202746777)
        ·
          refine ⟨335510677021984652060083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447347569362646202746777 335510677021984652060083)
          ·
            refine ⟨503266015532976978090125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335510677021984652060083 503266015532976978090125)
            ·
              refine ⟨188724755824866366783797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 503266015532976978090125 188724755824866366783797)
              ·
                refine ⟨17692945858581221885981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188724755824866366783797 17692945858581221885981)
                ·
                  rfl

theorem cell21_232584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_232584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232584 prefixEnd_232584 := by exact prefixLift 232584
  have htrace : WordTrace (prefixWord ++ tailWord_232584) baseStart_232584 baseEnd_232584 := by
    simpa [prefixWord, tailWord_232584, baseEnd_232584] using wordTrace_append hprefix tailTrace_232584
  have hstable : (prefixWord ++ tailWord_232584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232584).length < 2 ^ (prefixWord ++ tailWord_232584).sum := by decide
  have hdescent : baseEnd_232584 < baseStart_232584 := by decide
  rcases family_descends (prefixWord ++ tailWord_232584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232612 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 6]
def baseStart_232612 : Nat := 118140960795 + 232612 * 2 ^ 59
def prefixEnd_232612 : Nat := 4983230072969 + 3 ^ 40 * 232612 * 2
def baseEnd_232612 : Nat := 53085227557221839191219

theorem tailTrace_232612 : CollatzResearch.WordTrace tailWord_232612 prefixEnd_232612 53085227557221839191219 := by
  unfold tailWord_232612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4242028316646962905942045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5656037755529283874589393 4242028316646962905942045)
  ·
    refine ⟨1590760618742611089728267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4242028316646962905942045 1590760618742611089728267)
    ·
      refine ⟨2386140928113916634592401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1590760618742611089728267 2386140928113916634592401)
      ·
        refine ⟨1789605696085437475944301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2386140928113916634592401 1789605696085437475944301)
        ·
          refine ⟨671102136032039053479113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1789605696085437475944301 671102136032039053479113)
          ·
            refine ⟨503326602024029290109335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671102136032039053479113 503326602024029290109335)
            ·
              refine ⟨754989903036043935164003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503326602024029290109335 754989903036043935164003)
              ·
                refine ⟨1132484854554065902746005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754989903036043935164003 1132484854554065902746005)
                ·
                  refine ⟨53085227557221839191219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1132484854554065902746005 53085227557221839191219)
                  ·
                    rfl

theorem cell21_232612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_232612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232612 prefixEnd_232612 := by exact prefixLift 232612
  have htrace : WordTrace (prefixWord ++ tailWord_232612) baseStart_232612 baseEnd_232612 := by
    simpa [prefixWord, tailWord_232612, baseEnd_232612] using wordTrace_append hprefix tailTrace_232612
  have hstable : (prefixWord ++ tailWord_232612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232612).length < 2 ^ (prefixWord ++ tailWord_232612).sum := by decide
  have hdescent : baseEnd_232612 < baseStart_232612 := by decide
  rcases family_descends (prefixWord ++ tailWord_232612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232615 : List Nat := [1, 1, 6, 2, 1, 1, 2, 4, 3]
def baseStart_232615 : Nat := 118140960795 + 232615 * 2 ^ 59
def prefixEnd_232615 : Nat := 4983230072969 + 3 ^ 40 * 232615 * 2
def baseEnd_232615 : Nat := 53085912198094500641213

theorem tailTrace_232615 : CollatzResearch.WordTrace tailWord_232615 prefixEnd_232615 53085912198094500641213 := by
  unfold tailWord_232615
  simp only [CollatzResearch.WordTrace]
  refine ⟨8484166052283057324243299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5656110701522038216162199 8484166052283057324243299)
  ·
    refine ⟨12726249078424585986364949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8484166052283057324243299 12726249078424585986364949)
    ·
      refine ⟨596542925551152468110857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12726249078424585986364949 596542925551152468110857)
      ·
        refine ⟨447407194163364351083143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596542925551152468110857 447407194163364351083143)
        ·
          refine ⟨671110791245046526624715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447407194163364351083143 671110791245046526624715)
          ·
            refine ⟨1006666186867569789937073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671110791245046526624715 1006666186867569789937073)
            ·
              refine ⟨754999640150677342452805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006666186867569789937073 754999640150677342452805)
              ·
                refine ⟨141562432528252001709901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 754999640150677342452805 141562432528252001709901)
                ·
                  refine ⟨53085912198094500641213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141562432528252001709901 53085912198094500641213)
                  ·
                    rfl

theorem cell21_232615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 3].length) (baseStart_232615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232615 prefixEnd_232615 := by exact prefixLift 232615
  have htrace : WordTrace (prefixWord ++ tailWord_232615) baseStart_232615 baseEnd_232615 := by
    simpa [prefixWord, tailWord_232615, baseEnd_232615] using wordTrace_append hprefix tailTrace_232615
  have hstable : (prefixWord ++ tailWord_232615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232615).length < 2 ^ (prefixWord ++ tailWord_232615).sum := by decide
  have hdescent : baseEnd_232615 < baseStart_232615 := by decide
  rcases family_descends (prefixWord ++ tailWord_232615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232660 : List Nat := [2, 4, 1, 4, 1, 2, 7]
def baseStart_232660 : Nat := 118140960795 + 232660 * 2 ^ 59
def prefixEnd_232660 : Nat := 4983230072969 + 3 ^ 40 * 232660 * 2
def baseEnd_232660 : Nat := 5899575756798269154569

theorem tailTrace_232660 : CollatzResearch.WordTrace tailWord_232660 prefixEnd_232660 5899575756798269154569 := by
  unfold tailWord_232660
  simp only [CollatzResearch.WordTrace]
  refine ⟨4242903668560015004815717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5657204891413353339754289 4242903668560015004815717)
  ·
    refine ⟨795544437855002813402947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4242903668560015004815717 795544437855002813402947)
    ·
      refine ⟨1193316656782504220104421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795544437855002813402947 1193316656782504220104421)
      ·
        refine ⟨223746873146719541269579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1193316656782504220104421 223746873146719541269579)
        ·
          refine ⟨335620309720079311904369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223746873146719541269579 335620309720079311904369)
          ·
            refine ⟨251715232290059483928277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335620309720079311904369 251715232290059483928277)
            ·
              refine ⟨5899575756798269154569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 251715232290059483928277 5899575756798269154569)
              ·
                rfl

theorem cell21_232660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 7].length) (baseStart_232660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232660 prefixEnd_232660 := by exact prefixLift 232660
  have htrace : WordTrace (prefixWord ++ tailWord_232660) baseStart_232660 baseEnd_232660 := by
    simpa [prefixWord, tailWord_232660, baseEnd_232660] using wordTrace_append hprefix tailTrace_232660
  have hstable : (prefixWord ++ tailWord_232660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232660).length < 2 ^ (prefixWord ++ tailWord_232660).sum := by decide
  have hdescent : baseEnd_232660 < baseStart_232660 := by decide
  rcases family_descends (prefixWord ++ tailWord_232660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232671 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 6]
def baseStart_232671 : Nat := 118140960795 + 232671 * 2 ^ 59
def prefixEnd_232671 : Nat := 4983230072969 + 3 ^ 40 * 232671 * 2
def baseEnd_232671 : Nat := 53098692161050847707765

theorem tailTrace_232671 : CollatzResearch.WordTrace tailWord_232671 prefixEnd_232671 53098692161050847707765 := by
  unfold tailWord_232671
  simp only [CollatzResearch.WordTrace]
  refine ⟨8486208540080178888281867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5657472360053452592187911 8486208540080178888281867)
  ·
    refine ⟨12729312810120268332422801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8486208540080178888281867 12729312810120268332422801)
    ·
      refine ⟨9546984607590201249317101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12729312810120268332422801 9546984607590201249317101)
      ·
        refine ⟨3580119227846325468493913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9546984607590201249317101 3580119227846325468493913)
        ·
          refine ⟨2685089420884744101370435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3580119227846325468493913 2685089420884744101370435)
          ·
            refine ⟨4027634131327116152055653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685089420884744101370435 4027634131327116152055653)
            ·
              refine ⟨755181399623834278510435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4027634131327116152055653 755181399623834278510435)
              ·
                refine ⟨1132772099435751417765653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755181399623834278510435 1132772099435751417765653)
                ·
                  refine ⟨53098692161050847707765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1132772099435751417765653 53098692161050847707765)
                  ·
                    rfl

theorem cell21_232671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_232671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232671 prefixEnd_232671 := by exact prefixLift 232671
  have htrace : WordTrace (prefixWord ++ tailWord_232671) baseStart_232671 baseEnd_232671 := by
    simpa [prefixWord, tailWord_232671, baseEnd_232671] using wordTrace_append hprefix tailTrace_232671
  have hstable : (prefixWord ++ tailWord_232671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232671).length < 2 ^ (prefixWord ++ tailWord_232671).sum := by decide
  have hdescent : baseEnd_232671 < baseStart_232671 := by decide
  rcases family_descends (prefixWord ++ tailWord_232671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232736 : List Nat := [2, 1, 1, 5, 4, 1, 1, 6]
def baseStart_232736 : Nat := 118140960795 + 232736 * 2 ^ 59
def prefixEnd_232736 : Nat := 4983230072969 + 3 ^ 40 * 232736 * 2
def baseEnd_232736 : Nat := 17704508682208393041433

theorem tailTrace_232736 : CollatzResearch.WordTrace tailWord_232736 prefixEnd_232736 17704508682208393041433 := by
  unfold tailWord_232736
  simp only [CollatzResearch.WordTrace]
  refine ⟨4244289642422347494699031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5659052856563129992932041 4244289642422347494699031)
  ·
    refine ⟨6366434463633521242048547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4244289642422347494699031 6366434463633521242048547)
    ·
      refine ⟨9549651695450281863072821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6366434463633521242048547 9549651695450281863072821)
      ·
        refine ⟨895279846448463924663077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9549651695450281863072821 895279846448463924663077)
        ·
          refine ⟨167864971209086985874327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 895279846448463924663077 167864971209086985874327)
          ·
            refine ⟨251797456813630478811491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167864971209086985874327 251797456813630478811491)
            ·
              refine ⟨377696185220445718217237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251797456813630478811491 377696185220445718217237)
              ·
                refine ⟨17704508682208393041433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 377696185220445718217237 17704508682208393041433)
                ·
                  rfl

theorem cell21_232736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 6].length) (baseStart_232736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232736 prefixEnd_232736 := by exact prefixLift 232736
  have htrace : WordTrace (prefixWord ++ tailWord_232736) baseStart_232736 baseEnd_232736 := by
    simpa [prefixWord, tailWord_232736, baseEnd_232736] using wordTrace_append hprefix tailTrace_232736
  have hstable : (prefixWord ++ tailWord_232736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232736).length < 2 ^ (prefixWord ++ tailWord_232736).sum := by decide
  have hdescent : baseEnd_232736 < baseStart_232736 := by decide
  rcases family_descends (prefixWord ++ tailWord_232736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232837 : List Nat := [1, 3, 1, 1, 3, 1, 11]
def baseStart_232837 : Nat := 118140960795 + 232837 * 2 ^ 59
def prefixEnd_232837 : Nat := 4983230072969 + 3 ^ 40 * 232837 * 2
def baseEnd_232837 : Nat := 5904063958074605326751

theorem tailTrace_232837 : CollatzResearch.WordTrace tailWord_232837 prefixEnd_232837 5904063958074605326751 := by
  unfold tailWord_232837
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492263057478789238824765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5661508704985859492549843 8492263057478789238824765)
  ·
    refine ⟨3184598646554545964559287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8492263057478789238824765 3184598646554545964559287)
    ·
      refine ⟨4776897969831818946838931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3184598646554545964559287 4776897969831818946838931)
      ·
        refine ⟨7165346954747728420258397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4776897969831818946838931 7165346954747728420258397)
        ·
          refine ⟨2687005108030398157596899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7165346954747728420258397 2687005108030398157596899)
          ·
            refine ⟨4030507662045597236395349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687005108030398157596899 4030507662045597236395349)
            ·
              refine ⟨5904063958074605326751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4030507662045597236395349 5904063958074605326751)
              ·
                rfl

theorem cell21_232837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 11].length) (baseStart_232837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232837 prefixEnd_232837 := by exact prefixLift 232837
  have htrace : WordTrace (prefixWord ++ tailWord_232837) baseStart_232837 baseEnd_232837 := by
    simpa [prefixWord, tailWord_232837, baseEnd_232837] using wordTrace_append hprefix tailTrace_232837
  have hstable : (prefixWord ++ tailWord_232837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232837).length < 2 ^ (prefixWord ++ tailWord_232837).sum := by decide
  have hdescent : baseEnd_232837 < baseStart_232837 := by decide
  rcases family_descends (prefixWord ++ tailWord_232837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232857 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 4]
def baseStart_232857 : Nat := 118140960795 + 232857 * 2 ^ 59
def prefixEnd_232857 : Nat := 4983230072969 + 3 ^ 40 * 232857 * 2
def baseEnd_232857 : Nat := 53141139895155857607385

theorem tailTrace_232857 : CollatzResearch.WordTrace tailWord_232857 prefixEnd_232857 53141139895155857607385 := by
  unfold tailWord_232857
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492992517406332654552825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5661995011604221769701883 8492992517406332654552825)
  ·
    refine ⟨6369744388054749490914619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8492992517406332654552825 6369744388054749490914619)
    ·
      refine ⟨9554616582082124236371929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6369744388054749490914619 9554616582082124236371929)
      ·
        refine ⟨7165962436561593177278947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9554616582082124236371929 7165962436561593177278947)
        ·
          refine ⟨10748943654842389765918421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7165962436561593177278947 10748943654842389765918421)
          ·
            refine ⟨251928366910368510138713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10748943654842389765918421 251928366910368510138713)
            ·
              refine ⟨188946275182776382604035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251928366910368510138713 188946275182776382604035)
              ·
                refine ⟨283419412774164573906053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188946275182776382604035 283419412774164573906053)
                ·
                  refine ⟨53141139895155857607385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283419412774164573906053 53141139895155857607385)
                  ·
                    rfl

theorem cell21_232857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_232857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232857 prefixEnd_232857 := by exact prefixLift 232857
  have htrace : WordTrace (prefixWord ++ tailWord_232857) baseStart_232857 baseEnd_232857 := by
    simpa [prefixWord, tailWord_232857, baseEnd_232857] using wordTrace_append hprefix tailTrace_232857
  have hstable : (prefixWord ++ tailWord_232857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232857).length < 2 ^ (prefixWord ++ tailWord_232857).sum := by decide
  have hdescent : baseEnd_232857 < baseStart_232857 := by decide
  rcases family_descends (prefixWord ++ tailWord_232857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232868 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_232868 : Nat := 118140960795 + 232868 * 2 ^ 59
def prefixEnd_232868 : Nat := 4983230072969 + 3 ^ 40 * 232868 * 2
def baseEnd_232868 : Nat := 53143650245022282924029

theorem tailTrace_232868 : CollatzResearch.WordTrace tailWord_232868 prefixEnd_232868 53143650245022282924029 := by
  unfold tailWord_232868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4246696860183240766601629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5662262480244321022135505 4246696860183240766601629)
  ·
    refine ⟨1592511322568715287475611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4246696860183240766601629 1592511322568715287475611)
    ·
      refine ⟨2388766983853072931213417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1592511322568715287475611 2388766983853072931213417)
      ·
        refine ⟨1791575237889804698410063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2388766983853072931213417 1791575237889804698410063)
        ·
          refine ⟨2687362856834707047615095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791575237889804698410063 2687362856834707047615095)
          ·
            refine ⟨4031044285252060571422643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687362856834707047615095 4031044285252060571422643)
            ·
              refine ⟨6046566427878090857133965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4031044285252060571422643 6046566427878090857133965)
              ·
                refine ⟨2267462410454284071425237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6046566427878090857133965 2267462410454284071425237)
                ·
                  refine ⟨53143650245022282924029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2267462410454284071425237 53143650245022282924029)
                  ·
                    rfl

theorem cell21_232868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_232868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232868 prefixEnd_232868 := by exact prefixLift 232868
  have htrace : WordTrace (prefixWord ++ tailWord_232868) baseStart_232868 baseEnd_232868 := by
    simpa [prefixWord, tailWord_232868, baseEnd_232868] using wordTrace_append hprefix tailTrace_232868
  have hstable : (prefixWord ++ tailWord_232868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232868).length < 2 ^ (prefixWord ++ tailWord_232868).sum := by decide
  have hdescent : baseEnd_232868 < baseStart_232868 := by decide
  rcases family_descends (prefixWord ++ tailWord_232868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232899 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 4]
def baseStart_232899 : Nat := 118140960795 + 232899 * 2 ^ 59
def prefixEnd_232899 : Nat := 4983230072969 + 3 ^ 40 * 232899 * 2
def baseEnd_232899 : Nat := 53150724867373117907299

theorem tailTrace_232899 : CollatzResearch.WordTrace tailWord_232899 prefixEnd_232899 53150724867373117907299 := by
  unfold tailWord_232899
  simp only [CollatzResearch.WordTrace]
  refine ⟨8494524383254173827581751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5663016255502782551721167 8494524383254173827581751)
  ·
    refine ⟨12741786574881260741372627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8494524383254173827581751 12741786574881260741372627)
    ·
      refine ⟨19112679862321891112058941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12741786574881260741372627 19112679862321891112058941)
      ·
        refine ⟨7167254948370709167022103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19112679862321891112058941 7167254948370709167022103)
        ·
          refine ⟨10750882422556063750533155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7167254948370709167022103 10750882422556063750533155)
          ·
            refine ⟨16126323633834095625799733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10750882422556063750533155 16126323633834095625799733)
            ·
              refine ⟨1511842840671946464918725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16126323633834095625799733 1511842840671946464918725)
              ·
                refine ⟨283470532625989962172261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1511842840671946464918725 283470532625989962172261)
                ·
                  refine ⟨53150724867373117907299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 283470532625989962172261 53150724867373117907299)
                  ·
                    rfl

theorem cell21_232899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 4].length) (baseStart_232899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232899 prefixEnd_232899 := by exact prefixLift 232899
  have htrace : WordTrace (prefixWord ++ tailWord_232899) baseStart_232899 baseEnd_232899 := by
    simpa [prefixWord, tailWord_232899, baseEnd_232899] using wordTrace_append hprefix tailTrace_232899
  have hstable : (prefixWord ++ tailWord_232899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232899).length < 2 ^ (prefixWord ++ tailWord_232899).sum := by decide
  have hdescent : baseEnd_232899 < baseStart_232899 := by decide
  rcases family_descends (prefixWord ++ tailWord_232899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232995 : List Nat := [1, 1, 1, 4, 5, 2, 1, 3, 3]
def baseStart_232995 : Nat := 118140960795 + 232995 * 2 ^ 59
def prefixEnd_232995 : Nat := 4983230072969 + 3 ^ 40 * 232995 * 2
def baseEnd_232995 : Nat := 53172633375298284307103

theorem tailTrace_232995 : CollatzResearch.WordTrace tailWord_232995 prefixEnd_232995 53172633375298284307103 := by
  unfold tailWord_232995
  simp only [CollatzResearch.WordTrace]
  refine ⟨8498025790906382223076439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5665350527270921482050959 8498025790906382223076439)
  ·
    refine ⟨12747038686359573334614659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8498025790906382223076439 12747038686359573334614659)
    ·
      refine ⟨19120558029539360001921989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12747038686359573334614659 19120558029539360001921989)
      ·
        refine ⟨3585104630538630000360373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19120558029539360001921989 3585104630538630000360373)
        ·
          refine ⟨336103559112996562533785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3585104630538630000360373 336103559112996562533785)
          ·
            refine ⟨252077669334747421900339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336103559112996562533785 252077669334747421900339)
            ·
              refine ⟨378116504002121132850509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252077669334747421900339 378116504002121132850509)
              ·
                refine ⟨141793689000795424818941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378116504002121132850509 141793689000795424818941)
                ·
                  refine ⟨53172633375298284307103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141793689000795424818941 53172633375298284307103)
                  ·
                    rfl

theorem cell21_232995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 3].length) (baseStart_232995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_232995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_232995 prefixEnd_232995 := by exact prefixLift 232995
  have htrace : WordTrace (prefixWord ++ tailWord_232995) baseStart_232995 baseEnd_232995 := by
    simpa [prefixWord, tailWord_232995, baseEnd_232995] using wordTrace_append hprefix tailTrace_232995
  have hstable : (prefixWord ++ tailWord_232995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232995).length < 2 ^ (prefixWord ++ tailWord_232995).sum := by decide
  have hdescent : baseEnd_232995 < baseStart_232995 := by decide
  rcases family_descends (prefixWord ++ tailWord_232995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233006 : List Nat := [4, 1, 3, 1, 2, 1, 9]
def baseStart_233006 : Nat := 118140960795 + 233006 * 2 ^ 59
def prefixEnd_233006 : Nat := 4983230072969 + 3 ^ 40 * 233006 * 2
def baseEnd_233006 : Nat := 5908349302796078847083

theorem tailTrace_233006 : CollatzResearch.WordTrace tailWord_233006 prefixEnd_233006 5908349302796078847083 := by
  unfold tailWord_233006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1062303374233316387715859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5665617995911020734484581 1062303374233316387715859)
  ·
    refine ⟨1593455061349974581573789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1062303374233316387715859 1593455061349974581573789)
    ·
      refine ⟨597545648006240468090171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1593455061349974581573789 597545648006240468090171)
      ·
        refine ⟨896318472009360702135257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597545648006240468090171 896318472009360702135257)
        ·
          refine ⟨672238854007020526601443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896318472009360702135257 672238854007020526601443)
          ·
            refine ⟨1008358281010530789902165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672238854007020526601443 1008358281010530789902165)
            ·
              refine ⟨5908349302796078847083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1008358281010530789902165 5908349302796078847083)
              ·
                rfl

theorem cell21_233006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 9].length) (baseStart_233006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233006 prefixEnd_233006 := by exact prefixLift 233006
  have htrace : WordTrace (prefixWord ++ tailWord_233006) baseStart_233006 baseEnd_233006 := by
    simpa [prefixWord, tailWord_233006, baseEnd_233006] using wordTrace_append hprefix tailTrace_233006
  have hstable : (prefixWord ++ tailWord_233006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233006).length < 2 ^ (prefixWord ++ tailWord_233006).sum := by decide
  have hdescent : baseEnd_233006 < baseStart_233006 := by decide
  rcases family_descends (prefixWord ++ tailWord_233006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233164 : List Nat := [2, 2, 1, 5, 3, 1, 1, 3, 3]
def baseStart_233164 : Nat := 118140960795 + 233164 * 2 ^ 59
def prefixEnd_233164 : Nat := 4983230072969 + 3 ^ 40 * 233164 * 2
def baseEnd_233164 : Nat := 53211201477791545990091

theorem tailTrace_233164 : CollatzResearch.WordTrace tailWord_233164 prefixEnd_233164 53211201477791545990091 := by
  unfold tailWord_233164
  simp only [CollatzResearch.WordTrace]
  refine ⟨4252094863647062042989273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5669459818196082723985697 4252094863647062042989273)
  ·
    refine ⟨3189071147735296532241955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4252094863647062042989273 3189071147735296532241955)
    ·
      refine ⟨4783606721602944798362933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3189071147735296532241955 4783606721602944798362933)
      ·
        refine ⟨448463130150276074846525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4783606721602944798362933 448463130150276074846525)
        ·
          refine ⟨168173673806353528067447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448463130150276074846525 168173673806353528067447)
          ·
            refine ⟨252260510709530292101171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168173673806353528067447 252260510709530292101171)
            ·
              refine ⟨378390766064295438151757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252260510709530292101171 378390766064295438151757)
              ·
                refine ⟨141896537274110789306909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378390766064295438151757 141896537274110789306909)
                ·
                  refine ⟨53211201477791545990091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141896537274110789306909 53211201477791545990091)
                  ·
                    rfl

theorem cell21_233164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_233164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233164 prefixEnd_233164 := by exact prefixLift 233164
  have htrace : WordTrace (prefixWord ++ tailWord_233164) baseStart_233164 baseEnd_233164 := by
    simpa [prefixWord, tailWord_233164, baseEnd_233164] using wordTrace_append hprefix tailTrace_233164
  have hstable : (prefixWord ++ tailWord_233164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233164).length < 2 ^ (prefixWord ++ tailWord_233164).sum := by decide
  have hdescent : baseEnd_233164 < baseStart_233164 := by decide
  rcases family_descends (prefixWord ++ tailWord_233164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233217 : List Nat := [1, 2, 4, 1, 1, 1, 4, 7]
def baseStart_233217 : Nat := 118140960795 + 233217 * 2 ^ 59
def prefixEnd_233217 : Nat := 4983230072969 + 3 ^ 40 * 233217 * 2
def baseEnd_233217 : Nat := 17741098933291743868883

theorem tailTrace_233217 : CollatzResearch.WordTrace tailWord_233217 prefixEnd_233217 17741098933291743868883 := by
  unfold tailWord_233217
  simp only [CollatzResearch.WordTrace]
  refine ⟨8506122796102114137657905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5670748530734742758438603 8506122796102114137657905)
  ·
    refine ⟨6379592097076585603243429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8506122796102114137657905 6379592097076585603243429)
    ·
      refine ⟨1196173518201859800608143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6379592097076585603243429 1196173518201859800608143)
      ·
        refine ⟨1794260277302789700912215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196173518201859800608143 1794260277302789700912215)
        ·
          refine ⟨2691390415954184551368323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794260277302789700912215 2691390415954184551368323)
          ·
            refine ⟨4037085623931276827052485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691390415954184551368323 4037085623931276827052485)
            ·
              refine ⟨756953554487114405072341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4037085623931276827052485 756953554487114405072341)
              ·
                refine ⟨17741098933291743868883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 756953554487114405072341 17741098933291743868883)
                ·
                  rfl

theorem cell21_233217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 7].length) (baseStart_233217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233217 prefixEnd_233217 := by exact prefixLift 233217
  have htrace : WordTrace (prefixWord ++ tailWord_233217) baseStart_233217 baseEnd_233217 := by
    simpa [prefixWord, tailWord_233217, baseEnd_233217] using wordTrace_append hprefix tailTrace_233217
  have hstable : (prefixWord ++ tailWord_233217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233217).length < 2 ^ (prefixWord ++ tailWord_233217).sum := by decide
  have hdescent : baseEnd_233217 < baseStart_233217 := by decide
  rcases family_descends (prefixWord ++ tailWord_233217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233231 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 9]
def baseStart_233231 : Nat := 118140960795 + 233231 * 2 ^ 59
def prefixEnd_233231 : Nat := 4983230072969 + 3 ^ 40 * 233231 * 2
def baseEnd_233231 : Nat := 53226491790614318373287

theorem tailTrace_233231 : CollatzResearch.WordTrace tailWord_233231 prefixEnd_233231 53226491790614318373287 := by
  unfold tailWord_233231
  simp only [CollatzResearch.WordTrace]
  refine ⟨8506633418051394528667547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5671088945367596352445031 8506633418051394528667547)
  ·
    refine ⟨12759950127077091793001321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8506633418051394528667547 12759950127077091793001321)
    ·
      refine ⟨9569962595307818844750991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12759950127077091793001321 9569962595307818844750991)
      ·
        refine ⟨14354943892961728267126487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9569962595307818844750991 14354943892961728267126487)
        ·
          refine ⟨21532415839442592400689731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14354943892961728267126487 21532415839442592400689731)
          ·
            refine ⟨32298623759163888601034597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21532415839442592400689731 32298623759163888601034597)
            ·
              refine ⟨6055991954843229112693987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32298623759163888601034597 6055991954843229112693987)
              ·
                refine ⟨9083987932264843669040981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6055991954843229112693987 9083987932264843669040981)
                ·
                  refine ⟨53226491790614318373287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9083987932264843669040981 53226491790614318373287)
                  ·
                    rfl

theorem cell21_233231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_233231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233231 prefixEnd_233231 := by exact prefixLift 233231
  have htrace : WordTrace (prefixWord ++ tailWord_233231) baseStart_233231 baseEnd_233231 := by
    simpa [prefixWord, tailWord_233231, baseEnd_233231] using wordTrace_append hprefix tailTrace_233231
  have hstable : (prefixWord ++ tailWord_233231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233231).length < 2 ^ (prefixWord ++ tailWord_233231).sum := by decide
  have hdescent : baseEnd_233231 < baseStart_233231 := by decide
  rcases family_descends (prefixWord ++ tailWord_233231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233234 : List Nat := [3, 2, 4, 1, 1, 10]
def baseStart_233234 : Nat := 118140960795 + 233234 * 2 ^ 59
def prefixEnd_233234 : Nat := 4983230072969 + 3 ^ 40 * 233234 * 2
def baseEnd_233234 : Nat := 1971376904869888141603

theorem tailTrace_233234 : CollatzResearch.WordTrace tailWord_233234 prefixEnd_233234 1971376904869888141603 := by
  unfold tailWord_233234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2126685709260131510256689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5671161891360350694017837 2126685709260131510256689)
  ·
    refine ⟨1595014281945098632692517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2126685709260131510256689 1595014281945098632692517)
    ·
      refine ⟨299065177864705993629847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1595014281945098632692517 299065177864705993629847)
      ·
        refine ⟨448597766797058990444771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299065177864705993629847 448597766797058990444771)
        ·
          refine ⟨672896650195588485667157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448597766797058990444771 672896650195588485667157)
          ·
            refine ⟨1971376904869888141603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 672896650195588485667157 1971376904869888141603)
            ·
              rfl

theorem cell21_233234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 10].length) (baseStart_233234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233234 prefixEnd_233234 := by exact prefixLift 233234
  have htrace : WordTrace (prefixWord ++ tailWord_233234) baseStart_233234 baseEnd_233234 := by
    simpa [prefixWord, tailWord_233234, baseEnd_233234] using wordTrace_append hprefix tailTrace_233234
  have hstable : (prefixWord ++ tailWord_233234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233234).length < 2 ^ (prefixWord ++ tailWord_233234).sum := by decide
  have hdescent : baseEnd_233234 < baseStart_233234 := by decide
  rcases family_descends (prefixWord ++ tailWord_233234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233248 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_233248 : Nat := 118140960795 + 233248 * 2 ^ 59
def prefixEnd_233248 : Nat := 4983230072969 + 3 ^ 40 * 233248 * 2
def baseEnd_233248 : Nat := 53230371422226066589919

theorem tailTrace_233248 : CollatzResearch.WordTrace tailWord_233248 prefixEnd_233248 53230371422226066589919 := by
  unfold tailWord_233248
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253626729494903216018199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5671502305993204288024265 4253626729494903216018199)
  ·
    refine ⟨6380440094242354824027299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4253626729494903216018199 6380440094242354824027299)
    ·
      refine ⟨9570660141363532236040949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6380440094242354824027299 9570660141363532236040949)
      ·
        refine ⟨897249388252831147128839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9570660141363532236040949 897249388252831147128839)
        ·
          refine ⟨1345874082379246720693259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897249388252831147128839 1345874082379246720693259)
          ·
            refine ⟨2018811123568870081039889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1345874082379246720693259 2018811123568870081039889)
            ·
              refine ⟨1514108342676652560779917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2018811123568870081039889 1514108342676652560779917)
              ·
                refine ⟨567790628503744710292469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1514108342676652560779917 567790628503744710292469)
                ·
                  refine ⟨53230371422226066589919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 567790628503744710292469 53230371422226066589919)
                  ·
                    rfl

theorem cell21_233248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_233248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233248 prefixEnd_233248 := by exact prefixLift 233248
  have htrace : WordTrace (prefixWord ++ tailWord_233248) baseStart_233248 baseEnd_233248 := by
    simpa [prefixWord, tailWord_233248, baseEnd_233248] using wordTrace_append hprefix tailTrace_233248
  have hstable : (prefixWord ++ tailWord_233248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233248).length < 2 ^ (prefixWord ++ tailWord_233248).sum := by decide
  have hdescent : baseEnd_233248 < baseStart_233248 := by decide
  rcases family_descends (prefixWord ++ tailWord_233248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233324 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_233324 : Nat := 118140960795 + 233324 * 2 ^ 59
def prefixEnd_233324 : Nat := 4983230072969 + 3 ^ 40 * 233324 * 2
def baseEnd_233324 : Nat := 53247715657666823323097

theorem tailTrace_233324 : CollatzResearch.WordTrace tailWord_233324 prefixEnd_233324 53247715657666823323097 := by
  unfold tailWord_233324
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255012703357235705901513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5673350271142980941202017 4255012703357235705901513)
  ·
    refine ⟨3191259527517926779426135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4255012703357235705901513 3191259527517926779426135)
    ·
      refine ⟨4786889291276890169139203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3191259527517926779426135 4786889291276890169139203)
      ·
        refine ⟨7180333936915335253708805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4786889291276890169139203 7180333936915335253708805)
        ·
          refine ⟨1346312613171625360070401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7180333936915335253708805 1346312613171625360070401)
          ·
            refine ⟨1009734459878719020052801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346312613171625360070401 1009734459878719020052801)
            ·
              refine ⟨757300844909039265039601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009734459878719020052801 757300844909039265039601)
              ·
                refine ⟨567975633681779448779701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 757300844909039265039601 567975633681779448779701)
                ·
                  refine ⟨53247715657666823323097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 567975633681779448779701 53247715657666823323097)
                  ·
                    rfl

theorem cell21_233324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_233324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233324 prefixEnd_233324 := by exact prefixLift 233324
  have htrace : WordTrace (prefixWord ++ tailWord_233324) baseStart_233324 baseEnd_233324 := by
    simpa [prefixWord, tailWord_233324, baseEnd_233324] using wordTrace_append hprefix tailTrace_233324
  have hstable : (prefixWord ++ tailWord_233324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233324).length < 2 ^ (prefixWord ++ tailWord_233324).sum := by decide
  have hdescent : baseEnd_233324 < baseStart_233324 := by decide
  rcases family_descends (prefixWord ++ tailWord_233324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233338 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_233338 : Nat := 118140960795 + 233338 * 2 ^ 59
def prefixEnd_233338 : Nat := 4983230072969 + 3 ^ 40 * 233338 * 2
def baseEnd_233338 : Nat := 53250910648405910089735

theorem tailTrace_233338 : CollatzResearch.WordTrace tailWord_233338 prefixEnd_233338 53250910648405910089735 := by
  unfold tailWord_233338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2127634007165937950703167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5673690685775834535208445 2127634007165937950703167)
  ·
    refine ⟨3191451010748906926054751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2127634007165937950703167 3191451010748906926054751)
    ·
      refine ⟨4787176516123360389082127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3191451010748906926054751 4787176516123360389082127)
      ·
        refine ⟨7180764774185040583623191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4787176516123360389082127 7180764774185040583623191)
        ·
          refine ⟨10771147161277560875434787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7180764774185040583623191 10771147161277560875434787)
          ·
            refine ⟨16156720741916341313152181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10771147161277560875434787 16156720741916341313152181)
            ·
              refine ⟨1514692569554656998108017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16156720741916341313152181 1514692569554656998108017)
              ·
                refine ⟨1136019427165992748581013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1514692569554656998108017 1136019427165992748581013)
                ·
                  refine ⟨53250910648405910089735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1136019427165992748581013 53250910648405910089735)
                  ·
                    rfl

theorem cell21_233338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_233338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233338 prefixEnd_233338 := by exact prefixLift 233338
  have htrace : WordTrace (prefixWord ++ tailWord_233338) baseStart_233338 baseEnd_233338 := by
    simpa [prefixWord, tailWord_233338, baseEnd_233338] using wordTrace_append hprefix tailTrace_233338
  have hstable : (prefixWord ++ tailWord_233338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233338).length < 2 ^ (prefixWord ++ tailWord_233338).sum := by decide
  have hdescent : baseEnd_233338 < baseStart_233338 := by decide
  rcases family_descends (prefixWord ++ tailWord_233338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233372 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 4]
def baseStart_233372 : Nat := 118140960795 + 233372 * 2 ^ 59
def prefixEnd_233372 : Nat := 4983230072969 + 3 ^ 40 * 233372 * 2
def baseEnd_233372 : Nat := 53258669911629406522999

theorem tailTrace_233372 : CollatzResearch.WordTrace tailWord_233372 prefixEnd_233372 53258669911629406522999 := by
  unfold tailWord_233372
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255888055270287804775185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5674517407027050406366913 4255888055270287804775185)
  ·
    refine ⟨3191916041452715853581389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4255888055270287804775185 3191916041452715853581389)
    ·
      refine ⟨1196968515544768445093021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3191916041452715853581389 1196968515544768445093021)
      ·
        refine ⟨448863193329288166909883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1196968515544768445093021 448863193329288166909883)
        ·
          refine ⟨673294789993932250364825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448863193329288166909883 673294789993932250364825)
          ·
            refine ⟨504971092495449187773619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673294789993932250364825 504971092495449187773619)
            ·
              refine ⟨757456638743173781660429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504971092495449187773619 757456638743173781660429)
              ·
                refine ⟨284046239528690168122661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 757456638743173781660429 284046239528690168122661)
                ·
                  refine ⟨53258669911629406522999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284046239528690168122661 53258669911629406522999)
                  ·
                    rfl

theorem cell21_233372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_233372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233372 prefixEnd_233372 := by exact prefixLift 233372
  have htrace : WordTrace (prefixWord ++ tailWord_233372) baseStart_233372 baseEnd_233372 := by
    simpa [prefixWord, tailWord_233372, baseEnd_233372] using wordTrace_append hprefix tailTrace_233372
  have hstable : (prefixWord ++ tailWord_233372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233372).length < 2 ^ (prefixWord ++ tailWord_233372).sum := by decide
  have hdescent : baseEnd_233372 < baseStart_233372 := by decide
  rcases family_descends (prefixWord ++ tailWord_233372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233462 : List Nat := [5, 1, 1, 1, 4, 1, 8]
def baseStart_233462 : Nat := 118140960795 + 233462 * 2 ^ 59
def prefixEnd_233462 : Nat := 4983230072969 + 3 ^ 40 * 233462 * 2
def baseEnd_233462 : Nat := 5919912126423250002535

theorem tailTrace_233462 : CollatzResearch.WordTrace tailWord_233462 prefixEnd_233462 5919912126423250002535 := by
  unfold tailWord_233462
  simp only [CollatzResearch.WordTrace]
  refine ⟨532191167513407561270415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5676705786809680653551093 532191167513407561270415)
  ·
    refine ⟨798286751270111341905623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 532191167513407561270415 798286751270111341905623)
    ·
      refine ⟨1197430126905167012858435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 798286751270111341905623 1197430126905167012858435)
      ·
        refine ⟨1796145190357750519287653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197430126905167012858435 1796145190357750519287653)
        ·
          refine ⟨336777223192078222366435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1796145190357750519287653 336777223192078222366435)
          ·
            refine ⟨505165834788117333549653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336777223192078222366435 505165834788117333549653)
            ·
              refine ⟨5919912126423250002535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 505165834788117333549653 5919912126423250002535)
              ·
                rfl

theorem cell21_233462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 8].length) (baseStart_233462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233462 prefixEnd_233462 := by exact prefixLift 233462
  have htrace : WordTrace (prefixWord ++ tailWord_233462) baseStart_233462 baseEnd_233462 := by
    simpa [prefixWord, tailWord_233462, baseEnd_233462] using wordTrace_append hprefix tailTrace_233462
  have hstable : (prefixWord ++ tailWord_233462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233462).length < 2 ^ (prefixWord ++ tailWord_233462).sum := by decide
  have hdescent : baseEnd_233462 < baseStart_233462 := by decide
  rcases family_descends (prefixWord ++ tailWord_233462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233521 : List Nat := [1, 2, 2, 3, 1, 5, 7]
def baseStart_233521 : Nat := 118140960795 + 233521 * 2 ^ 59
def prefixEnd_233521 : Nat := 4983230072969 + 3 ^ 40 * 233521 * 2
def baseEnd_233521 : Nat := 5921408193515362059929

theorem tailTrace_233521 : CollatzResearch.WordTrace tailWord_233521 prefixEnd_233521 5921408193515362059929 := by
  unfold tailWord_233521
  simp only [CollatzResearch.WordTrace]
  refine ⟨8517210587000774056724417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5678140391333849371149611 8517210587000774056724417)
  ·
    refine ⟨6387907940250580542543313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8517210587000774056724417 6387907940250580542543313)
    ·
      refine ⟨4790930955187935406907485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6387907940250580542543313 4790930955187935406907485)
      ·
        refine ⟨1796599108195475777590307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4790930955187935406907485 1796599108195475777590307)
        ·
          refine ⟨2694898662293213666385461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796599108195475777590307 2694898662293213666385461)
          ·
            refine ⟨252646749589988781223637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2694898662293213666385461 252646749589988781223637)
            ·
              refine ⟨5921408193515362059929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 252646749589988781223637 5921408193515362059929)
              ·
                rfl

theorem cell21_233521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 7].length) (baseStart_233521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233521 prefixEnd_233521 := by exact prefixLift 233521
  have htrace : WordTrace (prefixWord ++ tailWord_233521) baseStart_233521 baseEnd_233521 := by
    simpa [prefixWord, tailWord_233521, baseEnd_233521] using wordTrace_append hprefix tailTrace_233521
  have hstable : (prefixWord ++ tailWord_233521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233521).length < 2 ^ (prefixWord ++ tailWord_233521).sum := by decide
  have hdescent : baseEnd_233521 < baseStart_233521 := by decide
  rcases family_descends (prefixWord ++ tailWord_233521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233580 : List Nat := [2, 2, 1, 1, 3, 12]
def baseStart_233580 : Nat := 118140960795 + 233580 * 2 ^ 59
def prefixEnd_233580 : Nat := 4983230072969 + 3 ^ 40 * 233580 * 2
def baseEnd_233580 : Nat := 1974301420202491372441

theorem tailTrace_233580 : CollatzResearch.WordTrace tailWord_233580 prefixEnd_233580 1974301420202491372441 := by
  unfold tailWord_233580
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259681246893513566561097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5679574995858018088748129 4259681246893513566561097)
  ·
    refine ⟨3194760935170135174920823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4259681246893513566561097 3194760935170135174920823)
    ·
      refine ⟨4792141402755202762381235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3194760935170135174920823 4792141402755202762381235)
      ·
        refine ⟨7188212104132804143571853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4792141402755202762381235 7188212104132804143571853)
        ·
          refine ⟨2695579539049801553839445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7188212104132804143571853 2695579539049801553839445)
          ·
            refine ⟨1974301420202491372441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2695579539049801553839445 1974301420202491372441)
            ·
              rfl

theorem cell21_233580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 12].length) (baseStart_233580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233580 prefixEnd_233580 := by exact prefixLift 233580
  have htrace : WordTrace (prefixWord ++ tailWord_233580) baseStart_233580 baseEnd_233580 := by
    simpa [prefixWord, tailWord_233580, baseEnd_233580] using wordTrace_append hprefix tailTrace_233580
  have hstable : (prefixWord ++ tailWord_233580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233580).length < 2 ^ (prefixWord ++ tailWord_233580).sum := by decide
  have hdescent : baseEnd_233580 < baseStart_233580 := by decide
  rcases family_descends (prefixWord ++ tailWord_233580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233583 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 4]
def baseStart_233583 : Nat := 118140960795 + 233583 * 2 ^ 59
def prefixEnd_233583 : Nat := 4983230072969 + 3 ^ 40 * 233583 * 2
def baseEnd_233583 : Nat := 53306822986339928505901

theorem tailTrace_233583 : CollatzResearch.WordTrace tailWord_233583 prefixEnd_233583 53306822986339928505901 := by
  unfold tailWord_233583
  simp only [CollatzResearch.WordTrace]
  refine ⟨8519471912776158645481403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5679647941850772430320935 8519471912776158645481403)
  ·
    refine ⟨12779207869164237968222105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8519471912776158645481403 12779207869164237968222105)
    ·
      refine ⟨9584405901873178476166579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12779207869164237968222105 9584405901873178476166579)
      ·
        refine ⟨14376608852809767714249869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9584405901873178476166579 14376608852809767714249869)
        ·
          refine ⟨5391228319803662892843701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14376608852809767714249869 5391228319803662892843701)
          ·
            refine ⟨505427654981593396204097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5391228319803662892843701 505427654981593396204097)
            ·
              refine ⟨379070741236195047153073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505427654981593396204097 379070741236195047153073)
              ·
                refine ⟨284303055927146285364805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379070741236195047153073 284303055927146285364805)
                ·
                  refine ⟨53306822986339928505901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284303055927146285364805 53306822986339928505901)
                  ·
                    rfl

theorem cell21_233583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 4].length) (baseStart_233583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233583 prefixEnd_233583 := by exact prefixLift 233583
  have htrace : WordTrace (prefixWord ++ tailWord_233583) baseStart_233583 baseEnd_233583 := by
    simpa [prefixWord, tailWord_233583, baseEnd_233583] using wordTrace_append hprefix tailTrace_233583
  have hstable : (prefixWord ++ tailWord_233583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233583).length < 2 ^ (prefixWord ++ tailWord_233583).sum := by decide
  have hdescent : baseEnd_233583 < baseStart_233583 := by decide
  rcases family_descends (prefixWord ++ tailWord_233583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233586 : List Nat := [3, 2, 1, 2, 2, 2, 4, 2, 3]
def baseStart_233586 : Nat := 118140960795 + 233586 * 2 ^ 59
def prefixEnd_233586 : Nat := 4983230072969 + 3 ^ 40 * 233586 * 2
def baseEnd_233586 : Nat := 53307507627212589955895

theorem tailTrace_233586 : CollatzResearch.WordTrace tailWord_233586 prefixEnd_233586 53307507627212589955895 := by
  unfold tailWord_233586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2129895332941322539460153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5679720887843526771893741 2129895332941322539460153)
  ·
    refine ⟨1597421499705991904595115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2129895332941322539460153 1597421499705991904595115)
    ·
      refine ⟨2396132249558987856892673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597421499705991904595115 2396132249558987856892673)
      ·
        refine ⟨1797099187169240892669505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2396132249558987856892673 1797099187169240892669505)
        ·
          refine ⟨1347824390376930669502129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1797099187169240892669505 1347824390376930669502129)
          ·
            refine ⟨1010868292782698002126597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347824390376930669502129 1010868292782698002126597)
            ·
              refine ⟨189537804896755875398737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1010868292782698002126597 189537804896755875398737)
              ·
                refine ⟨142153353672566906549053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189537804896755875398737 142153353672566906549053)
                ·
                  refine ⟨53307507627212589955895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142153353672566906549053 53307507627212589955895)
                  ·
                    rfl

theorem cell21_233586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_233586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233586 prefixEnd_233586 := by exact prefixLift 233586
  have htrace : WordTrace (prefixWord ++ tailWord_233586) baseStart_233586 baseEnd_233586 := by
    simpa [prefixWord, tailWord_233586, baseEnd_233586] using wordTrace_append hprefix tailTrace_233586
  have hstable : (prefixWord ++ tailWord_233586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233586).length < 2 ^ (prefixWord ++ tailWord_233586).sum := by decide
  have hdescent : baseEnd_233586 < baseStart_233586 := by decide
  rcases family_descends (prefixWord ++ tailWord_233586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233597 : List Nat := [1, 4, 1, 1, 3, 2, 3, 6]
def baseStart_233597 : Nat := 118140960795 + 233597 * 2 ^ 59
def prefixEnd_233597 : Nat := 4983230072969 + 3 ^ 40 * 233597 * 2
def baseEnd_233597 : Nat := 17770005992359671757513

theorem tailTrace_233597 : CollatzResearch.WordTrace tailWord_233597 prefixEnd_233597 17770005992359671757513 := by
  unfold tailWord_233597
  simp only [CollatzResearch.WordTrace]
  refine ⟨8519982534725439036491045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5679988356483626024327363 8519982534725439036491045)
  ·
    refine ⟨1597496725261019819342071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8519982534725439036491045 1597496725261019819342071)
    ·
      refine ⟨2396245087891529729013107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597496725261019819342071 2396245087891529729013107)
      ·
        refine ⟨3594367631837294593519661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396245087891529729013107 3594367631837294593519661)
        ·
          refine ⟨1347887861938985472569873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3594367631837294593519661 1347887861938985472569873)
          ·
            refine ⟨1010915896454239104427405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1347887861938985472569873 1010915896454239104427405)
            ·
              refine ⟨379093461170339664160277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1010915896454239104427405 379093461170339664160277)
              ·
                refine ⟨17770005992359671757513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 379093461170339664160277 17770005992359671757513)
                ·
                  rfl

theorem cell21_233597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 6].length) (baseStart_233597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233597 prefixEnd_233597 := by exact prefixLift 233597
  have htrace : WordTrace (prefixWord ++ tailWord_233597) baseStart_233597 baseEnd_233597 := by
    simpa [prefixWord, tailWord_233597, baseEnd_233597] using wordTrace_append hprefix tailTrace_233597
  have hstable : (prefixWord ++ tailWord_233597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233597).length < 2 ^ (prefixWord ++ tailWord_233597).sum := by decide
  have hdescent : baseEnd_233597 < baseStart_233597 := by decide
  rcases family_descends (prefixWord ++ tailWord_233597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233645 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 5]
def baseStart_233645 : Nat := 118140960795 + 233645 * 2 ^ 59
def prefixEnd_233645 : Nat := 4983230072969 + 3 ^ 40 * 233645 * 2
def baseEnd_233645 : Nat := 53320972231041598472441

theorem tailTrace_233645 : CollatzResearch.WordTrace tailWord_233645 prefixEnd_233645 53320972231041598472441 := by
  unfold tailWord_233645
  simp only [CollatzResearch.WordTrace]
  refine ⟨8521733238551543234238389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5681155492367695489492259 8521733238551543234238389)
  ·
    refine ⟨798912491114207178209849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8521733238551543234238389 798912491114207178209849)
    ·
      refine ⟨599184368335655383657387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798912491114207178209849 599184368335655383657387)
      ·
        refine ⟨898776552503483075486081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599184368335655383657387 898776552503483075486081)
        ·
          refine ⟨674082414377612306614561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898776552503483075486081 674082414377612306614561)
          ·
            refine ⟨505561810783209229960921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674082414377612306614561 505561810783209229960921)
            ·
              refine ⟨379171358087406922470691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505561810783209229960921 379171358087406922470691)
              ·
                refine ⟨568757037131110383706037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379171358087406922470691 568757037131110383706037)
                ·
                  refine ⟨53320972231041598472441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 568757037131110383706037 53320972231041598472441)
                  ·
                    rfl

theorem cell21_233645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_233645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233645 prefixEnd_233645 := by exact prefixLift 233645
  have htrace : WordTrace (prefixWord ++ tailWord_233645) baseStart_233645 baseEnd_233645 := by
    simpa [prefixWord, tailWord_233645, baseEnd_233645] using wordTrace_append hprefix tailTrace_233645
  have hstable : (prefixWord ++ tailWord_233645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233645).length < 2 ^ (prefixWord ++ tailWord_233645).sum := by decide
  have hdescent : baseEnd_233645 < baseStart_233645 := by decide
  rcases family_descends (prefixWord ++ tailWord_233645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233656 : List Nat := [2, 1, 2, 1, 2, 1, 4, 8]
def baseStart_233656 : Nat := 118140960795 + 233656 * 2 ^ 59
def prefixEnd_233656 : Nat := 4983230072969 + 3 ^ 40 * 233656 * 2
def baseEnd_233656 : Nat := 17774494193636007929695

theorem tailTrace_233656 : CollatzResearch.WordTrace tailWord_233656 prefixEnd_233656 17774494193636007929695 := by
  unfold tailWord_233656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261067220755846056444411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5681422961007794741925881 4261067220755846056444411)
  ·
    refine ⟨6391600831133769084666617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4261067220755846056444411 6391600831133769084666617)
    ·
      refine ⟨4793700623350326813499963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6391600831133769084666617 4793700623350326813499963)
      ·
        refine ⟨7190550935025490220249945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4793700623350326813499963 7190550935025490220249945)
        ·
          refine ⟨5392913201269117665187459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7190550935025490220249945 5392913201269117665187459)
          ·
            refine ⟨8089369801903676497781189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392913201269117665187459 8089369801903676497781189)
            ·
              refine ⟨1516756837856939343333973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8089369801903676497781189 1516756837856939343333973)
              ·
                refine ⟨17774494193636007929695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1516756837856939343333973 17774494193636007929695)
                ·
                  rfl

theorem cell21_233656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_233656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233656 prefixEnd_233656 := by exact prefixLift 233656
  have htrace : WordTrace (prefixWord ++ tailWord_233656) baseStart_233656 baseEnd_233656 := by
    simpa [prefixWord, tailWord_233656, baseEnd_233656] using wordTrace_append hprefix tailTrace_233656
  have hstable : (prefixWord ++ tailWord_233656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233656).length < 2 ^ (prefixWord ++ tailWord_233656).sum := by decide
  have hdescent : baseEnd_233656 < baseStart_233656 := by decide
  rcases family_descends (prefixWord ++ tailWord_233656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233659 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 4]
def baseStart_233659 : Nat := 118140960795 + 233659 * 2 ^ 59
def prefixEnd_233659 : Nat := 4983230072969 + 3 ^ 40 * 233659 * 2
def baseEnd_233659 : Nat := 53324167221780685239079

theorem tailTrace_233659 : CollatzResearch.WordTrace tailWord_233659 prefixEnd_233659 53324167221780685239079 := by
  unfold tailWord_233659
  simp only [CollatzResearch.WordTrace]
  refine ⟨8522243860500823625248031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5681495907000549083498687 8522243860500823625248031)
  ·
    refine ⟨12783365790751235437872047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8522243860500823625248031 12783365790751235437872047)
    ·
      refine ⟨19175048686126853156808071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12783365790751235437872047 19175048686126853156808071)
      ·
        refine ⟨28762573029190279735212107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19175048686126853156808071 28762573029190279735212107)
        ·
          refine ⟨43143859543785419602818161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28762573029190279735212107 43143859543785419602818161)
          ·
            refine ⟨32357894657839064702113621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43143859543785419602818161 32357894657839064702113621)
            ·
              refine ⟨189597039010775769738947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 32357894657839064702113621 189597039010775769738947)
              ·
                refine ⟨284395558516163654608421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189597039010775769738947 284395558516163654608421)
                ·
                  refine ⟨53324167221780685239079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284395558516163654608421 53324167221780685239079)
                  ·
                    rfl

theorem cell21_233659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 4].length) (baseStart_233659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233659 prefixEnd_233659 := by exact prefixLift 233659
  have htrace : WordTrace (prefixWord ++ tailWord_233659) baseStart_233659 baseEnd_233659 := by
    simpa [prefixWord, tailWord_233659, baseEnd_233659] using wordTrace_append hprefix tailTrace_233659
  have hstable : (prefixWord ++ tailWord_233659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233659).length < 2 ^ (prefixWord ++ tailWord_233659).sum := by decide
  have hdescent : baseEnd_233659 < baseStart_233659 := by decide
  rcases family_descends (prefixWord ++ tailWord_233659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233704 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 5]
def baseStart_233704 : Nat := 118140960795 + 233704 * 2 ^ 59
def prefixEnd_233704 : Nat := 4983230072969 + 3 ^ 40 * 233704 * 2
def baseEnd_233704 : Nat := 53334436834870606988987

theorem tailTrace_233704 : CollatzResearch.WordTrace tailWord_233704 prefixEnd_233704 53334436834870606988987 := by
  unfold tailWord_233704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261942572668898155318083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5682590096891864207090777 4261942572668898155318083)
  ·
    refine ⟨6392913859003347232977125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4261942572668898155318083 6392913859003347232977125)
    ·
      refine ⟨1198671348563127606183211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6392913859003347232977125 1198671348563127606183211)
      ·
        refine ⟨1798007022844691409274817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1198671348563127606183211 1798007022844691409274817)
        ·
          refine ⟨1348505267133518556956113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1798007022844691409274817 1348505267133518556956113)
          ·
            refine ⟨1011378950350138917717085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1348505267133518556956113 1011378950350138917717085)
            ·
              refine ⟨379267106381302094143907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1011378950350138917717085 379267106381302094143907)
              ·
                refine ⟨568900659571953141215861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379267106381302094143907 568900659571953141215861)
                ·
                  refine ⟨53334436834870606988987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 568900659571953141215861 53334436834870606988987)
                  ·
                    rfl

theorem cell21_233704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_233704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233704 prefixEnd_233704 := by exact prefixLift 233704
  have htrace : WordTrace (prefixWord ++ tailWord_233704) baseStart_233704 baseEnd_233704 := by
    simpa [prefixWord, tailWord_233704, baseEnd_233704] using wordTrace_append hprefix tailTrace_233704
  have hstable : (prefixWord ++ tailWord_233704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233704).length < 2 ^ (prefixWord ++ tailWord_233704).sum := by decide
  have hdescent : baseEnd_233704 < baseStart_233704 := by decide
  rcases family_descends (prefixWord ++ tailWord_233704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233763 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 5]
def baseStart_233763 : Nat := 118140960795 + 233763 * 2 ^ 59
def prefixEnd_233763 : Nat := 4983230072969 + 3 ^ 40 * 233763 * 2
def baseEnd_233763 : Nat := 53347901438699615505533

theorem tailTrace_233763 : CollatzResearch.WordTrace tailWord_233763 prefixEnd_233763 53347901438699615505533 := by
  unfold tailWord_233763
  simp only [CollatzResearch.WordTrace]
  refine ⟨8526037052124049387033943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5684024701416032924689295 8526037052124049387033943)
  ·
    refine ⟨12789055578186074080550915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8526037052124049387033943 12789055578186074080550915)
    ·
      refine ⟨19183583367279111120826373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12789055578186074080550915 19183583367279111120826373)
      ·
        refine ⟨3596921881364833335154945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19183583367279111120826373 3596921881364833335154945)
        ·
          refine ⟨2697691411023625001366209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3596921881364833335154945 2697691411023625001366209)
          ·
            refine ⟨2023268558267718751024657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2697691411023625001366209 2023268558267718751024657)
            ·
              refine ⟨1517451418700789063268493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023268558267718751024657 1517451418700789063268493)
              ·
                refine ⟨569044282012795898725685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1517451418700789063268493 569044282012795898725685)
                ·
                  refine ⟨53347901438699615505533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 569044282012795898725685 53347901438699615505533)
                  ·
                    rfl

theorem cell21_233763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_233763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233763 prefixEnd_233763 := by exact prefixLift 233763
  have htrace : WordTrace (prefixWord ++ tailWord_233763) baseStart_233763 baseEnd_233763 := by
    simpa [prefixWord, tailWord_233763, baseEnd_233763] using wordTrace_append hprefix tailTrace_233763
  have hstable : (prefixWord ++ tailWord_233763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233763).length < 2 ^ (prefixWord ++ tailWord_233763).sum := by decide
  have hdescent : baseEnd_233763 < baseStart_233763 := by decide
  rcases family_descends (prefixWord ++ tailWord_233763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233780 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 7]
def baseStart_233780 : Nat := 118140960795 + 233780 * 2 ^ 59
def prefixEnd_233780 : Nat := 4983230072969 + 3 ^ 40 * 233780 * 2
def baseEnd_233780 : Nat := 53351781070311363722165

theorem tailTrace_233780 : CollatzResearch.WordTrace tailWord_233780 prefixEnd_233780 53351781070311363722165 := by
  unfold tailWord_233780
  simp only [CollatzResearch.WordTrace]
  refine ⟨4263328546531230645201397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5684438062041640860268529 4263328546531230645201397)
  ·
    refine ⟨399687051237302872987631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4263328546531230645201397 399687051237302872987631)
    ·
      refine ⟨599530576855954309481447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399687051237302872987631 599530576855954309481447)
      ·
        refine ⟨899295865283931464222171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599530576855954309481447 899295865283931464222171)
        ·
          refine ⟨1348943797925897196333257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899295865283931464222171 1348943797925897196333257)
          ·
            refine ⟨1011707848444422897249943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1348943797925897196333257 1011707848444422897249943)
            ·
              refine ⟨1517561772666634345874915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011707848444422897249943 1517561772666634345874915)
              ·
                refine ⟨2276342658999951518812373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517561772666634345874915 2276342658999951518812373)
                ·
                  refine ⟨53351781070311363722165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2276342658999951518812373 53351781070311363722165)
                  ·
                    rfl

theorem cell21_233780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_233780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233780 prefixEnd_233780 := by exact prefixLift 233780
  have htrace : WordTrace (prefixWord ++ tailWord_233780) baseStart_233780 baseEnd_233780 := by
    simpa [prefixWord, tailWord_233780, baseEnd_233780] using wordTrace_append hprefix tailTrace_233780
  have hstable : (prefixWord ++ tailWord_233780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233780).length < 2 ^ (prefixWord ++ tailWord_233780).sum := by decide
  have hdescent : baseEnd_233780 < baseStart_233780 := by decide
  rcases family_descends (prefixWord ++ tailWord_233780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233808 : List Nat := [2, 1, 1, 1, 1, 7, 8]
def baseStart_233808 : Nat := 118140960795 + 233808 * 2 ^ 59
def prefixEnd_233808 : Nat := 4983230072969 + 3 ^ 40 * 233808 * 2
def baseEnd_233808 : Nat := 5928685672421059695049

theorem tailTrace_233808 : CollatzResearch.WordTrace tailWord_233808 prefixEnd_233808 5928685672421059695049 := by
  unfold tailWord_233808
  simp only [CollatzResearch.WordTrace]
  refine ⟨4263839168480511036211039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5685118891307348048281385 4263839168480511036211039)
  ·
    refine ⟨6395758752720766554316559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4263839168480511036211039 6395758752720766554316559)
    ·
      refine ⟨9593638129081149831474839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6395758752720766554316559 9593638129081149831474839)
      ·
        refine ⟨14390457193621724747212259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9593638129081149831474839 14390457193621724747212259)
        ·
          refine ⟨21585685790432587120818389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14390457193621724747212259 21585685790432587120818389)
          ·
            refine ⟨505914510713263760644181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 21585685790432587120818389 505914510713263760644181)
            ·
              refine ⟨5928685672421059695049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 505914510713263760644181 5928685672421059695049)
              ·
                rfl

theorem cell21_233808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 8].length) (baseStart_233808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233808 prefixEnd_233808 := by exact prefixLift 233808
  have htrace : WordTrace (prefixWord ++ tailWord_233808) baseStart_233808 baseEnd_233808 := by
    simpa [prefixWord, tailWord_233808, baseEnd_233808] using wordTrace_append hprefix tailTrace_233808
  have hstable : (prefixWord ++ tailWord_233808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233808).length < 2 ^ (prefixWord ++ tailWord_233808).sum := by decide
  have hdescent : baseEnd_233808 < baseStart_233808 := by decide
  rcases family_descends (prefixWord ++ tailWord_233808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233842 : List Nat := [3, 2, 1, 2, 1, 5, 2, 5]
def baseStart_233842 : Nat := 118140960795 + 233842 * 2 ^ 59
def prefixEnd_233842 : Nat := 4983230072969 + 3 ^ 40 * 233842 * 2
def baseEnd_233842 : Nat := 17788643438337677896235

theorem tailTrace_233842 : CollatzResearch.WordTrace tailWord_233842 prefixEnd_233842 17788643438337677896235 := by
  unfold tailWord_233842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132229604709461469789945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5685945612558563919439853 2132229604709461469789945)
  ·
    refine ⟨1599172203532096102342459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2132229604709461469789945 1599172203532096102342459)
    ·
      refine ⟨2398758305298144153513689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1599172203532096102342459 2398758305298144153513689)
      ·
        refine ⟨1799068728973608115135267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2398758305298144153513689 1799068728973608115135267)
        ·
          refine ⟨2698603093460412172702901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1799068728973608115135267 2698603093460412172702901)
          ·
            refine ⟨252994040011913641190897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2698603093460412172702901 252994040011913641190897)
            ·
              refine ⟨189745530008935230893173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252994040011913641190897 189745530008935230893173)
              ·
                refine ⟨17788643438337677896235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189745530008935230893173 17788643438337677896235)
                ·
                  rfl

theorem cell21_233842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_233842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233842 prefixEnd_233842 := by exact prefixLift 233842
  have htrace : WordTrace (prefixWord ++ tailWord_233842) baseStart_233842 baseEnd_233842 := by
    simpa [prefixWord, tailWord_233842, baseEnd_233842] using wordTrace_append hprefix tailTrace_233842
  have hstable : (prefixWord ++ tailWord_233842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233842).length < 2 ^ (prefixWord ++ tailWord_233842).sum := by decide
  have hdescent : baseEnd_233842 < baseStart_233842 := by decide
  rcases family_descends (prefixWord ++ tailWord_233842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233924 : List Nat := [2, 3, 3, 2, 3, 1, 2, 2, 3]
def baseStart_233924 : Nat := 118140960795 + 233924 * 2 ^ 59
def prefixEnd_233924 : Nat := 4983230072969 + 3 ^ 40 * 233924 * 2
def baseEnd_233924 : Nat := 53384643832199113321871

theorem tailTrace_233924 : CollatzResearch.WordTrace tailWord_233924 prefixEnd_233924 53384643832199113321871 := by
  unfold tailWord_233924
  simp only [CollatzResearch.WordTrace]
  refine ⟨4265954602270386941822413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5687939469693849255763217 4265954602270386941822413)
  ·
    refine ⟨1599732975851395103183405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4265954602270386941822413 1599732975851395103183405)
    ·
      refine ⟨599899865944273163693777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1599732975851395103183405 599899865944273163693777)
      ·
        refine ⟨449924899458204872770333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 599899865944273163693777 449924899458204872770333)
        ·
          refine ⟨168721837296826827288875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449924899458204872770333 168721837296826827288875)
          ·
            refine ⟨253082755945240240933313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168721837296826827288875 253082755945240240933313)
            ·
              refine ⟨189812066958930180699985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253082755945240240933313 189812066958930180699985)
              ·
                refine ⟨142359050219197635524989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189812066958930180699985 142359050219197635524989)
                ·
                  refine ⟨53384643832199113321871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142359050219197635524989 53384643832199113321871)
                  ·
                    rfl

theorem cell21_233924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_233924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233924 prefixEnd_233924 := by exact prefixLift 233924
  have htrace : WordTrace (prefixWord ++ tailWord_233924) baseStart_233924 baseEnd_233924 := by
    simpa [prefixWord, tailWord_233924, baseEnd_233924] using wordTrace_append hprefix tailTrace_233924
  have hstable : (prefixWord ++ tailWord_233924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233924).length < 2 ^ (prefixWord ++ tailWord_233924).sum := by decide
  have hdescent : baseEnd_233924 < baseStart_233924 := by decide
  rcases family_descends (prefixWord ++ tailWord_233924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233929 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 6]
def baseStart_233929 : Nat := 118140960795 + 233929 * 2 ^ 59
def prefixEnd_233929 : Nat := 4983230072969 + 3 ^ 40 * 233929 * 2
def baseEnd_233929 : Nat := 53385784900320215738527

theorem tailTrace_233929 : CollatzResearch.WordTrace tailWord_233929 prefixEnd_233929 53385784900320215738527 := by
  unfold tailWord_233929
  simp only [CollatzResearch.WordTrace]
  refine ⟨8532091569522659737576841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5688061046348439825051227 8532091569522659737576841)
  ·
    refine ⟨6399068677141994803182631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8532091569522659737576841 6399068677141994803182631)
    ·
      refine ⟨9598603015712992204773947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6399068677141994803182631 9598603015712992204773947)
      ·
        refine ⟨14397904523569488307160921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9598603015712992204773947 14397904523569488307160921)
        ·
          refine ⟨10798428392677116230370691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14397904523569488307160921 10798428392677116230370691)
          ·
            refine ⟨16197642589015674345556037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10798428392677116230370691 16197642589015674345556037)
            ·
              refine ⟨3037057985440438939791757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16197642589015674345556037 3037057985440438939791757)
              ·
                refine ⟨1138896744540164602421909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3037057985440438939791757 1138896744540164602421909)
                ·
                  refine ⟨53385784900320215738527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1138896744540164602421909 53385784900320215738527)
                  ·
                    rfl

theorem cell21_233929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_233929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233929 prefixEnd_233929 := by exact prefixLift 233929
  have htrace : WordTrace (prefixWord ++ tailWord_233929) baseStart_233929 baseEnd_233929 := by
    simpa [prefixWord, tailWord_233929, baseEnd_233929] using wordTrace_append hprefix tailTrace_233929
  have hstable : (prefixWord ++ tailWord_233929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233929).length < 2 ^ (prefixWord ++ tailWord_233929).sum := by decide
  have hdescent : baseEnd_233929 < baseStart_233929 := by decide
  rcases family_descends (prefixWord ++ tailWord_233929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233946 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_233946 : Nat := 118140960795 + 233946 * 2 ^ 59
def prefixEnd_233946 : Nat := 4983230072969 + 3 ^ 40 * 233946 * 2
def baseEnd_233946 : Nat := 53389664531931963955159

theorem tailTrace_233946 : CollatzResearch.WordTrace tailWord_233946 prefixEnd_233946 53389664531931963955159 := by
  unfold tailWord_233946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133177902615267910236423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5688474406974047760630461 2133177902615267910236423)
  ·
    refine ⟨3199766853922901865354635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2133177902615267910236423 3199766853922901865354635)
    ·
      refine ⟨4799650280884352798031953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3199766853922901865354635 4799650280884352798031953)
      ·
        refine ⟨3599737710663264598523965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4799650280884352798031953 3599737710663264598523965)
        ·
          refine ⟨1349901641498724224446487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3599737710663264598523965 1349901641498724224446487)
          ·
            refine ⟨2024852462248086336669731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349901641498724224446487 2024852462248086336669731)
            ·
              refine ⟨3037278693372129505004597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024852462248086336669731 3037278693372129505004597)
              ·
                refine ⟨284744877503637141094181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3037278693372129505004597 284744877503637141094181)
                ·
                  refine ⟨53389664531931963955159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284744877503637141094181 53389664531931963955159)
                  ·
                    rfl

theorem cell21_233946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_233946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_233946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_233946 prefixEnd_233946 := by exact prefixLift 233946
  have htrace : WordTrace (prefixWord ++ tailWord_233946) baseStart_233946 baseEnd_233946 := by
    simpa [prefixWord, tailWord_233946, baseEnd_233946] using wordTrace_append hprefix tailTrace_233946
  have hstable : (prefixWord ++ tailWord_233946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233946).length < 2 ^ (prefixWord ++ tailWord_233946).sum := by decide
  have hdescent : baseEnd_233946 < baseStart_233946 := by decide
  rcases family_descends (prefixWord ++ tailWord_233946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234084 : List Nat := [2, 3, 1, 1, 2, 2, 2, 5, 3]
def baseStart_234084 : Nat := 118140960795 + 234084 * 2 ^ 59
def prefixEnd_234084 : Nat := 4983230072969 + 3 ^ 40 * 234084 * 2
def baseEnd_234084 : Nat := 53421158012074390654877

theorem tailTrace_234084 : CollatzResearch.WordTrace tailWord_234084 prefixEnd_234084 53421158012074390654877 := by
  unfold tailWord_234084
  simp only [CollatzResearch.WordTrace]
  refine ⟨4268872441980560604734653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5691829922640747472979537 4268872441980560604734653)
  ·
    refine ⟨1600827165742710226775495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4268872441980560604734653 1600827165742710226775495)
    ·
      refine ⟨2401240748614065340163243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600827165742710226775495 2401240748614065340163243)
      ·
        refine ⟨3601861122921098010244865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401240748614065340163243 3601861122921098010244865)
        ·
          refine ⟨2701395842190823507683649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3601861122921098010244865 2701395842190823507683649)
          ·
            refine ⟨2026046881643117630762737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701395842190823507683649 2026046881643117630762737)
            ·
              refine ⟨1519535161232338223072053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026046881643117630762737 1519535161232338223072053)
              ·
                refine ⟨142456421365531708413005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1519535161232338223072053 142456421365531708413005)
                ·
                  refine ⟨53421158012074390654877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142456421365531708413005 53421158012074390654877)
                  ·
                    rfl

theorem cell21_234084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_234084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234084 prefixEnd_234084 := by exact prefixLift 234084
  have htrace : WordTrace (prefixWord ++ tailWord_234084) baseStart_234084 baseEnd_234084 := by
    simpa [prefixWord, tailWord_234084, baseEnd_234084] using wordTrace_append hprefix tailTrace_234084
  have hstable : (prefixWord ++ tailWord_234084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234084).length < 2 ^ (prefixWord ++ tailWord_234084).sum := by decide
  have hdescent : baseEnd_234084 < baseStart_234084 := by decide
  rcases family_descends (prefixWord ++ tailWord_234084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234112 : List Nat := [2, 1, 1, 2, 1, 5, 3, 6]
def baseStart_234112 : Nat := 118140960795 + 234112 * 2 ^ 59
def prefixEnd_234112 : Nat := 4983230072969 + 3 ^ 40 * 234112 * 2
def baseEnd_234112 : Nat := 17809182664517521396051

theorem tailTrace_234112 : CollatzResearch.WordTrace tailWord_234112 prefixEnd_234112 17809182664517521396051 := by
  unfold tailWord_234112
  simp only [CollatzResearch.WordTrace]
  refine ⟨4269383063929840995744295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5692510751906454660992393 4269383063929840995744295)
  ·
    refine ⟨6404074595894761493616443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4269383063929840995744295 6404074595894761493616443)
    ·
      refine ⟨9606111893842142240424665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6404074595894761493616443 9606111893842142240424665)
      ·
        refine ⟨7204583920381606680318499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9606111893842142240424665 7204583920381606680318499)
        ·
          refine ⟨10806875880572410020477749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7204583920381606680318499 10806875880572410020477749)
          ·
            refine ⟨1013144613803663439419789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10806875880572410020477749 1013144613803663439419789)
            ·
              refine ⟨379929230176373789782421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1013144613803663439419789 379929230176373789782421)
              ·
                refine ⟨17809182664517521396051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 379929230176373789782421 17809182664517521396051)
                ·
                  rfl

theorem cell21_234112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_234112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234112 prefixEnd_234112 := by exact prefixLift 234112
  have htrace : WordTrace (prefixWord ++ tailWord_234112) baseStart_234112 baseEnd_234112 := by
    simpa [prefixWord, tailWord_234112, baseEnd_234112] using wordTrace_append hprefix tailTrace_234112
  have hstable : (prefixWord ++ tailWord_234112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234112).length < 2 ^ (prefixWord ++ tailWord_234112).sum := by decide
  have hdescent : baseEnd_234112 < baseStart_234112 := by decide
  rcases family_descends (prefixWord ++ tailWord_234112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234194 : List Nat := [3, 2, 2, 2, 3, 2, 1, 3, 3]
def baseStart_234194 : Nat := 118140960795 + 234194 * 2 ^ 59
def prefixEnd_234194 : Nat := 4983230072969 + 3 ^ 40 * 234194 * 2
def baseEnd_234194 : Nat := 53446261510738643821319

theorem tailTrace_234194 : CollatzResearch.WordTrace tailWord_234194 prefixEnd_234194 53446261510738643821319 := by
  unfold tailWord_234194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2135439228390652498993409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5694504609041739997315757 2135439228390652498993409)
  ·
    refine ⟨1601579421292989374245057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2135439228390652498993409 1601579421292989374245057)
    ·
      refine ⟨1201184565969742030683793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1601579421292989374245057 1201184565969742030683793)
      ·
        refine ⟨900888424477306523012845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1201184565969742030683793 900888424477306523012845)
        ·
          refine ⟨337833159178989946129817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 900888424477306523012845 337833159178989946129817)
          ·
            refine ⟨253374869384242459597363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337833159178989946129817 253374869384242459597363)
            ·
              refine ⟨380062304076363689396045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253374869384242459597363 380062304076363689396045)
              ·
                refine ⟨142523364028636383523517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380062304076363689396045 142523364028636383523517)
                ·
                  refine ⟨53446261510738643821319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142523364028636383523517 53446261510738643821319)
                  ·
                    rfl

theorem cell21_234194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_234194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234194 prefixEnd_234194 := by exact prefixLift 234194
  have htrace : WordTrace (prefixWord ++ tailWord_234194) baseStart_234194 baseEnd_234194 := by
    simpa [prefixWord, tailWord_234194, baseEnd_234194] using wordTrace_append hprefix tailTrace_234194
  have hstable : (prefixWord ++ tailWord_234194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234194).length < 2 ^ (prefixWord ++ tailWord_234194).sum := by decide
  have hdescent : baseEnd_234194 < baseStart_234194 := by decide
  rcases family_descends (prefixWord ++ tailWord_234194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234312 : List Nat := [2, 1, 3, 1, 1, 3, 4, 3, 3]
def baseStart_234312 : Nat := 118140960795 + 234312 * 2 ^ 59
def prefixEnd_234312 : Nat := 4983230072969 + 3 ^ 40 * 234312 * 2
def baseEnd_234312 : Nat := 53473190718396660854411

theorem tailTrace_234312 : CollatzResearch.WordTrace tailWord_234312 prefixEnd_234312 53473190718396660854411 := by
  unfold tailWord_234312
  simp only [CollatzResearch.WordTrace]
  refine ⟨4273030363567558074384595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5697373818090077432512793 4273030363567558074384595)
  ·
    refine ⟨6409545545351337111576893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4273030363567558074384595 6409545545351337111576893)
    ·
      refine ⟨2403579579506751416841335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6409545545351337111576893 2403579579506751416841335)
      ·
        refine ⟨3605369369260127125262003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2403579579506751416841335 3605369369260127125262003)
        ·
          refine ⟨5408054053890190687893005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605369369260127125262003 5408054053890190687893005)
          ·
            refine ⟨2028020270208821507959877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5408054053890190687893005 2028020270208821507959877)
            ·
              refine ⟨380253800664154032742477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2028020270208821507959877 380253800664154032742477)
              ·
                refine ⟨142595175249057762278429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380253800664154032742477 142595175249057762278429)
                ·
                  refine ⟨53473190718396660854411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142595175249057762278429 53473190718396660854411)
                  ·
                    rfl

theorem cell21_234312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 3].length) (baseStart_234312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234312 prefixEnd_234312 := by exact prefixLift 234312
  have htrace : WordTrace (prefixWord ++ tailWord_234312) baseStart_234312 baseEnd_234312 := by
    simpa [prefixWord, tailWord_234312, baseEnd_234312] using wordTrace_append hprefix tailTrace_234312
  have hstable : (prefixWord ++ tailWord_234312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234312).length < 2 ^ (prefixWord ++ tailWord_234312).sum := by decide
  have hdescent : baseEnd_234312 < baseStart_234312 := by decide
  rcases family_descends (prefixWord ++ tailWord_234312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234343 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 4]
def baseStart_234343 : Nat := 118140960795 + 234343 * 2 ^ 59
def prefixEnd_234343 : Nat := 4983230072969 + 3 ^ 40 * 234343 * 2
def baseEnd_234343 : Nat := 53480265340747495837681

theorem tailTrace_234343 : CollatzResearch.WordTrace tailWord_234343 prefixEnd_234343 53480265340747495837681 := by
  unfold tailWord_234343
  simp only [CollatzResearch.WordTrace]
  refine ⟨8547191390022808443147683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5698127593348538962098455 8547191390022808443147683)
  ·
    refine ⟨12820787085034212664721525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8547191390022808443147683 12820787085034212664721525)
    ·
      refine ⟨1201948789221957437317643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12820787085034212664721525 1201948789221957437317643)
      ·
        refine ⟨1802923183832936155976465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201948789221957437317643 1802923183832936155976465)
        ·
          refine ⟨1352192387874702116982349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802923183832936155976465 1352192387874702116982349)
          ·
            refine ⟨507072145453013293868381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1352192387874702116982349 507072145453013293868381)
            ·
              refine ⟨190152054544879985200643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507072145453013293868381 190152054544879985200643)
              ·
                refine ⟨285228081817319977800965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190152054544879985200643 285228081817319977800965)
                ·
                  refine ⟨53480265340747495837681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285228081817319977800965 53480265340747495837681)
                  ·
                    rfl

theorem cell21_234343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 4].length) (baseStart_234343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234343 prefixEnd_234343 := by exact prefixLift 234343
  have htrace : WordTrace (prefixWord ++ tailWord_234343) baseStart_234343 baseEnd_234343 := by
    simpa [prefixWord, tailWord_234343, baseEnd_234343] using wordTrace_append hprefix tailTrace_234343
  have hstable : (prefixWord ++ tailWord_234343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234343).length < 2 ^ (prefixWord ++ tailWord_234343).sum := by decide
  have hdescent : baseEnd_234343 < baseStart_234343 := by decide
  rcases family_descends (prefixWord ++ tailWord_234343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234357 : List Nat := [1, 3, 4, 1, 1, 2, 4, 5]
def baseStart_234357 : Nat := 118140960795 + 234357 * 2 ^ 59
def prefixEnd_234357 : Nat := 4983230072969 + 3 ^ 40 * 234357 * 2
def baseEnd_234357 : Nat := 17827820110495527534773

theorem tailTrace_234357 : CollatzResearch.WordTrace tailWord_234357 prefixEnd_234357 17827820110495527534773 := by
  unfold tailWord_234357
  simp only [CollatzResearch.WordTrace]
  refine ⟨8547702011972088834157325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5698468007981392556104883 8547702011972088834157325)
  ·
    refine ⟨3205388254489533312808997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8547702011972088834157325 3205388254489533312808997)
    ·
      refine ⟨601010297716787496151687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3205388254489533312808997 601010297716787496151687)
      ·
        refine ⟨901515446575181244227531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601010297716787496151687 901515446575181244227531)
        ·
          refine ⟨1352273169862771866341297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 901515446575181244227531 1352273169862771866341297)
          ·
            refine ⟨1014204877397078899755973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1352273169862771866341297 1014204877397078899755973)
            ·
              refine ⟨190163414511952293704245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1014204877397078899755973 190163414511952293704245)
              ·
                refine ⟨17827820110495527534773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190163414511952293704245 17827820110495527534773)
                ·
                  rfl

theorem cell21_234357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 5].length) (baseStart_234357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234357 prefixEnd_234357 := by exact prefixLift 234357
  have htrace : WordTrace (prefixWord ++ tailWord_234357) baseStart_234357 baseEnd_234357 := by
    simpa [prefixWord, tailWord_234357, baseEnd_234357] using wordTrace_append hprefix tailTrace_234357
  have hstable : (prefixWord ++ tailWord_234357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234357).length < 2 ^ (prefixWord ++ tailWord_234357).sum := by decide
  have hdescent : baseEnd_234357 < baseStart_234357 := by decide
  rcases family_descends (prefixWord ++ tailWord_234357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234385 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 4]
def baseStart_234385 : Nat := 118140960795 + 234385 * 2 ^ 59
def prefixEnd_234385 : Nat := 4983230072969 + 3 ^ 40 * 234385 * 2
def baseEnd_234385 : Nat := 53489850312964756137595

theorem tailTrace_234385 : CollatzResearch.WordTrace tailWord_234385 prefixEnd_234385 53489850312964756137595 := by
  unfold tailWord_234385
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548723255870649616176609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5699148837247099744117739 8548723255870649616176609)
  ·
    refine ⟨6411542441902987212132457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8548723255870649616176609 6411542441902987212132457)
    ·
      refine ⟨4808656831427240409099343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6411542441902987212132457 4808656831427240409099343)
      ·
        refine ⟨7212985247140860613649015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808656831427240409099343 7212985247140860613649015)
        ·
          refine ⟨10819477870711290920473523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7212985247140860613649015 10819477870711290920473523)
          ·
            refine ⟨16229216806066936380710285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10819477870711290920473523 16229216806066936380710285)
            ·
              refine ⟨6085956302275101142766357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16229216806066936380710285 6085956302275101142766357)
              ·
                refine ⟨285279201669145366067173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6085956302275101142766357 285279201669145366067173)
                ·
                  refine ⟨53489850312964756137595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285279201669145366067173 53489850312964756137595)
                  ·
                    rfl

theorem cell21_234385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_234385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234385 prefixEnd_234385 := by exact prefixLift 234385
  have htrace : WordTrace (prefixWord ++ tailWord_234385) baseStart_234385 baseEnd_234385 := by
    simpa [prefixWord, tailWord_234385, baseEnd_234385] using wordTrace_append hprefix tailTrace_234385
  have hstable : (prefixWord ++ tailWord_234385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234385).length < 2 ^ (prefixWord ++ tailWord_234385).sum := by decide
  have hdescent : baseEnd_234385 < baseStart_234385 := by decide
  rcases family_descends (prefixWord ++ tailWord_234385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234436 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 4]
def baseStart_234436 : Nat := 118140960795 + 234436 * 2 ^ 59
def prefixEnd_234436 : Nat := 4983230072969 + 3 ^ 40 * 234436 * 2
def baseEnd_234436 : Nat := 53501489207800000787491

theorem tailTrace_234436 : CollatzResearch.WordTrace tailWord_234436 prefixEnd_234436 53501489207800000787491 := by
  unfold tailWord_234436
  simp only [CollatzResearch.WordTrace]
  refine ⟨4275291689342942663141581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5700388919123923550855441 4275291689342942663141581)
  ·
    refine ⟨1603234383503603498678093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4275291689342942663141581 1603234383503603498678093)
    ·
      refine ⟨601212893813851312004285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1603234383503603498678093 601212893813851312004285)
      ·
        refine ⟨225454835180194242001607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601212893813851312004285 225454835180194242001607)
        ·
          refine ⟨338182252770291363002411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225454835180194242001607 338182252770291363002411)
          ·
            refine ⟨507273379155437044503617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338182252770291363002411 507273379155437044503617)
            ·
              refine ⟨380455034366577783377713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507273379155437044503617 380455034366577783377713)
              ·
                refine ⟨285341275774933337533285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380455034366577783377713 285341275774933337533285)
                ·
                  refine ⟨53501489207800000787491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285341275774933337533285 53501489207800000787491)
                  ·
                    rfl

theorem cell21_234436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_234436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234436 prefixEnd_234436 := by exact prefixLift 234436
  have htrace : WordTrace (prefixWord ++ tailWord_234436) baseStart_234436 baseEnd_234436 := by
    simpa [prefixWord, tailWord_234436, baseEnd_234436] using wordTrace_append hprefix tailTrace_234436
  have hstable : (prefixWord ++ tailWord_234436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234436).length < 2 ^ (prefixWord ++ tailWord_234436).sum := by decide
  have hdescent : baseEnd_234436 < baseStart_234436 := by decide
  rcases family_descends (prefixWord ++ tailWord_234436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234557 : List Nat := [1, 4, 1, 3, 1, 3, 3, 2, 3]
def baseStart_234557 : Nat := 118140960795 + 234557 * 2 ^ 59
def prefixEnd_234557 : Nat := 4983230072969 + 3 ^ 40 * 234557 * 2
def baseEnd_234557 : Nat := 53529103056330679270577

theorem tailTrace_234557 : CollatzResearch.WordTrace tailWord_234557 prefixEnd_234557 53529103056330679270577 := by
  unfold tailWord_234557
  simp only [CollatzResearch.WordTrace]
  refine ⟨8554996611247522991437925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5703331074165015327625283 8554996611247522991437925)
  ·
    refine ⟨1604061864608910560894611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8554996611247522991437925 1604061864608910560894611)
    ·
      refine ⟨2406092796913365841341917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1604061864608910560894611 2406092796913365841341917)
      ·
        refine ⟨902284798842512190503219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2406092796913365841341917 902284798842512190503219)
        ·
          refine ⟨1353427198263768285754829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902284798842512190503219 1353427198263768285754829)
          ·
            refine ⟨507535199348913107158061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1353427198263768285754829 507535199348913107158061)
            ·
              refine ⟨190325699755842415184273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507535199348913107158061 190325699755842415184273)
              ·
                refine ⟨142744274816881811388205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190325699755842415184273 142744274816881811388205)
                ·
                  refine ⟨53529103056330679270577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142744274816881811388205 53529103056330679270577)
                  ·
                    rfl

theorem cell21_234557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_234557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234557 prefixEnd_234557 := by exact prefixLift 234557
  have htrace : WordTrace (prefixWord ++ tailWord_234557) baseStart_234557 baseEnd_234557 := by
    simpa [prefixWord, tailWord_234557, baseEnd_234557] using wordTrace_append hprefix tailTrace_234557
  have hstable : (prefixWord ++ tailWord_234557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234557).length < 2 ^ (prefixWord ++ tailWord_234557).sum := by decide
  have hdescent : baseEnd_234557 < baseStart_234557 := by decide
  rcases family_descends (prefixWord ++ tailWord_234557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234616 : List Nat := [2, 1, 2, 1, 1, 1, 8, 2, 3]
def baseStart_234616 : Nat := 118140960795 + 234616 * 2 ^ 59
def prefixEnd_234616 : Nat := 4983230072969 + 3 ^ 40 * 234616 * 2
def baseEnd_234616 : Nat := 53542567660159687787123

theorem tailTrace_234616 : CollatzResearch.WordTrace tailWord_234616 prefixEnd_234616 53542567660159687787123 := by
  unfold tailWord_234616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4278574259016888033917851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5704765678689184045223801 4278574259016888033917851)
  ·
    refine ⟨6417861388525332050876777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4278574259016888033917851 6417861388525332050876777)
    ·
      refine ⟨4813396041393999038157583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6417861388525332050876777 4813396041393999038157583)
      ·
        refine ⟨7220094062090998557236375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4813396041393999038157583 7220094062090998557236375)
        ·
          refine ⟨10830141093136497835854563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7220094062090998557236375 10830141093136497835854563)
          ·
            refine ⟨16245211639704746753781845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10830141093136497835854563 16245211639704746753781845)
            ·
              refine ⟨190373573902790001020881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 16245211639704746753781845 190373573902790001020881)
              ·
                refine ⟨142780180427092500765661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190373573902790001020881 142780180427092500765661)
                ·
                  refine ⟨53542567660159687787123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142780180427092500765661 53542567660159687787123)
                  ·
                    rfl

theorem cell21_234616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 3].length) (baseStart_234616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234616 prefixEnd_234616 := by exact prefixLift 234616
  have htrace : WordTrace (prefixWord ++ tailWord_234616) baseStart_234616 baseEnd_234616 := by
    simpa [prefixWord, tailWord_234616, baseEnd_234616] using wordTrace_append hprefix tailTrace_234616
  have hstable : (prefixWord ++ tailWord_234616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234616).length < 2 ^ (prefixWord ++ tailWord_234616).sum := by decide
  have hdescent : baseEnd_234616 < baseStart_234616 := by decide
  rcases family_descends (prefixWord ++ tailWord_234616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234672 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_234672 : Nat := 118140960795 + 234672 * 2 ^ 59
def prefixEnd_234672 : Nat := 4983230072969 + 3 ^ 40 * 234672 * 2
def baseEnd_234672 : Nat := 53555347623116034853675

theorem tailTrace_234672 : CollatzResearch.WordTrace tailWord_234672 prefixEnd_234672 53555347623116034853675 := by
  unfold tailWord_234672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4279595502915448815937135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5706127337220598421249513 4279595502915448815937135)
  ·
    refine ⟨6419393254373173223905703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4279595502915448815937135 6419393254373173223905703)
    ·
      refine ⟨9629089881559759835858555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6419393254373173223905703 9629089881559759835858555)
      ·
        refine ⟨14443634822339639753787833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9629089881559759835858555 14443634822339639753787833)
        ·
          refine ⟨10832726116754729815340875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14443634822339639753787833 10832726116754729815340875)
          ·
            refine ⟨16249089175132094723011313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10832726116754729815340875 16249089175132094723011313)
            ·
              refine ⟨12186816881349071042258485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16249089175132094723011313 12186816881349071042258485)
              ·
                refine ⟨1142514082626475410211733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12186816881349071042258485 1142514082626475410211733)
                ·
                  refine ⟨53555347623116034853675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1142514082626475410211733 53555347623116034853675)
                  ·
                    rfl

theorem cell21_234672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_234672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234672 prefixEnd_234672 := by exact prefixLift 234672
  have htrace : WordTrace (prefixWord ++ tailWord_234672) baseStart_234672 baseEnd_234672 := by
    simpa [prefixWord, tailWord_234672, baseEnd_234672] using wordTrace_append hprefix tailTrace_234672
  have hstable : (prefixWord ++ tailWord_234672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234672).length < 2 ^ (prefixWord ++ tailWord_234672).sum := by decide
  have hdescent : baseEnd_234672 < baseStart_234672 := by decide
  rcases family_descends (prefixWord ++ tailWord_234672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234675 : List Nat := [1, 1, 1, 2, 3, 2, 4, 4, 3]
def baseStart_234675 : Nat := 118140960795 + 234675 * 2 ^ 59
def prefixEnd_234675 : Nat := 4983230072969 + 3 ^ 40 * 234675 * 2
def baseEnd_234675 : Nat := 53556032263988696303669

theorem tailTrace_234675 : CollatzResearch.WordTrace tailWord_234675 prefixEnd_234675 53556032263988696303669 := by
  unfold tailWord_234675
  simp only [CollatzResearch.WordTrace]
  refine ⟨8559300424820029144233479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5706200283213352762822319 8559300424820029144233479)
  ·
    refine ⟨12838950637230043716350219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8559300424820029144233479 12838950637230043716350219)
    ·
      refine ⟨19258425955845065574525329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12838950637230043716350219 19258425955845065574525329)
      ·
        refine ⟨14443819466883799180893997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19258425955845065574525329 14443819466883799180893997)
        ·
          refine ⟨5416432300081424692835249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14443819466883799180893997 5416432300081424692835249)
          ·
            refine ⟨4062324225061068519626437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5416432300081424692835249 4062324225061068519626437)
            ·
              refine ⟨761685792198950347429957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4062324225061068519626437 761685792198950347429957)
              ·
                refine ⟨142816086037303190143117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 761685792198950347429957 142816086037303190143117)
                ·
                  refine ⟨53556032263988696303669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142816086037303190143117 53556032263988696303669)
                  ·
                    rfl

theorem cell21_234675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 3].length) (baseStart_234675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234675 prefixEnd_234675 := by exact prefixLift 234675
  have htrace : WordTrace (prefixWord ++ tailWord_234675) baseStart_234675 baseEnd_234675 := by
    simpa [prefixWord, tailWord_234675, baseEnd_234675] using wordTrace_append hprefix tailTrace_234675
  have hstable : (prefixWord ++ tailWord_234675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234675).length < 2 ^ (prefixWord ++ tailWord_234675).sum := by decide
  have hdescent : baseEnd_234675 < baseStart_234675 := by decide
  rcases family_descends (prefixWord ++ tailWord_234675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234709 : List Nat := [1, 3, 2, 4, 1, 3, 1, 3, 3]
def baseStart_234709 : Nat := 118140960795 + 234709 * 2 ^ 59
def prefixEnd_234709 : Nat := 4983230072969 + 3 ^ 40 * 234709 * 2
def baseEnd_234709 : Nat := 53563791527212192736933

theorem tailTrace_234709 : CollatzResearch.WordTrace tailWord_234709 prefixEnd_234709 53563791527212192736933 := by
  unfold tailWord_234709
  simp only [CollatzResearch.WordTrace]
  refine ⟨8560540506696852950971181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5707027004464568633980787 8560540506696852950971181)
  ·
    refine ⟨3210202690011319856614193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8560540506696852950971181 3210202690011319856614193)
    ·
      refine ⟨2407652017508489892460645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3210202690011319856614193 2407652017508489892460645)
      ·
        refine ⟨451434753282841854836371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2407652017508489892460645 451434753282841854836371)
        ·
          refine ⟨677152129924262782254557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451434753282841854836371 677152129924262782254557)
          ·
            refine ⟨253932048721598543345459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 677152129924262782254557 253932048721598543345459)
            ·
              refine ⟨380898073082397815018189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253932048721598543345459 380898073082397815018189)
              ·
                refine ⟨142836777405899180631821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380898073082397815018189 142836777405899180631821)
                ·
                  refine ⟨53563791527212192736933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142836777405899180631821 53563791527212192736933)
                  ·
                    rfl

theorem cell21_234709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_234709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234709 prefixEnd_234709 := by exact prefixLift 234709
  have htrace : WordTrace (prefixWord ++ tailWord_234709) baseStart_234709 baseEnd_234709 := by
    simpa [prefixWord, tailWord_234709, baseEnd_234709] using wordTrace_append hprefix tailTrace_234709
  have hstable : (prefixWord ++ tailWord_234709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234709).length < 2 ^ (prefixWord ++ tailWord_234709).sum := by decide
  have hdescent : baseEnd_234709 < baseStart_234709 := by decide
  rcases family_descends (prefixWord ++ tailWord_234709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234810 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_234810 : Nat := 118140960795 + 234810 * 2 ^ 59
def prefixEnd_234810 : Nat := 4983230072969 + 3 ^ 40 * 234810 * 2
def baseEnd_234810 : Nat := 53586841103258461553393

theorem tailTrace_234810 : CollatzResearch.WordTrace tailWord_234810 prefixEnd_234810 53586841103258461553393 := by
  unfold tailWord_234810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2141056069832736800099471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5709482852887298133598589 2141056069832736800099471)
  ·
    refine ⟨3211584104749105200149207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2141056069832736800099471 3211584104749105200149207)
    ·
      refine ⟨4817376157123657800223811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3211584104749105200149207 4817376157123657800223811)
      ·
        refine ⟨7226064235685486700335717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4817376157123657800223811 7226064235685486700335717)
        ·
          refine ⟨1354887044191028756312947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7226064235685486700335717 1354887044191028756312947)
          ·
            refine ⟨2032330566286543134469421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354887044191028756312947 2032330566286543134469421)
            ·
              refine ⟨762123962357453675426033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2032330566286543134469421 762123962357453675426033)
              ·
                refine ⟨571592971768090256569525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762123962357453675426033 571592971768090256569525)
                ·
                  refine ⟨53586841103258461553393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 571592971768090256569525 53586841103258461553393)
                  ·
                    rfl

theorem cell21_234810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_234810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234810 prefixEnd_234810 := by exact prefixLift 234810
  have htrace : WordTrace (prefixWord ++ tailWord_234810) baseStart_234810 baseEnd_234810 := by
    simpa [prefixWord, tailWord_234810, baseEnd_234810] using wordTrace_append hprefix tailTrace_234810
  have hstable : (prefixWord ++ tailWord_234810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234810).length < 2 ^ (prefixWord ++ tailWord_234810).sum := by decide
  have hdescent : baseEnd_234810 < baseStart_234810 := by decide
  rcases family_descends (prefixWord ++ tailWord_234810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234824 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_234824 : Nat := 118140960795 + 234824 * 2 ^ 59
def prefixEnd_234824 : Nat := 4983230072969 + 3 ^ 40 * 234824 * 2
def baseEnd_234824 : Nat := 53590036093997548320031

theorem tailTrace_234824 : CollatzResearch.WordTrace tailWord_234824 prefixEnd_234824 53590036093997548320031 := by
  unfold tailWord_234824
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282367450640113795703763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5709823267520151727605017 4282367450640113795703763)
  ·
    refine ⟨6423551175960170693555645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4282367450640113795703763 6423551175960170693555645)
    ·
      refine ⟨2408831690985064010083367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6423551175960170693555645 2408831690985064010083367)
      ·
        refine ⟨3613247536477596015125051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408831690985064010083367 3613247536477596015125051)
        ·
          refine ⟨5419871304716394022687577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3613247536477596015125051 5419871304716394022687577)
          ·
            refine ⟨4064903478537295517015683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5419871304716394022687577 4064903478537295517015683)
            ·
              refine ⟨6097355217805943275523525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064903478537295517015683 6097355217805943275523525)
              ·
                refine ⟨1143254103338614364160661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6097355217805943275523525 1143254103338614364160661)
                ·
                  refine ⟨53590036093997548320031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1143254103338614364160661 53590036093997548320031)
                  ·
                    rfl

theorem cell21_234824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_234824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234824 prefixEnd_234824 := by exact prefixLift 234824
  have htrace : WordTrace (prefixWord ++ tailWord_234824) baseStart_234824 baseEnd_234824 := by
    simpa [prefixWord, tailWord_234824, baseEnd_234824] using wordTrace_append hprefix tailTrace_234824
  have hstable : (prefixWord ++ tailWord_234824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234824).length < 2 ^ (prefixWord ++ tailWord_234824).sum := by decide
  have hdescent : baseEnd_234824 < baseStart_234824 := by decide
  rcases family_descends (prefixWord ++ tailWord_234824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234841 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 4]
def baseStart_234841 : Nat := 118140960795 + 234841 * 2 ^ 59
def prefixEnd_234841 : Nat := 4983230072969 + 3 ^ 40 * 234841 * 2
def baseEnd_234841 : Nat := 53593915725609296536663

theorem tailTrace_234841 : CollatzResearch.WordTrace tailWord_234841 prefixEnd_234841 53593915725609296536663 := by
  unfold tailWord_234841
  simp only [CollatzResearch.WordTrace]
  refine ⟨8565354942218639494776377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5710236628145759663184251 8565354942218639494776377)
  ·
    refine ⟨6424016206663979621082283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8565354942218639494776377 6424016206663979621082283)
    ·
      refine ⟨9636024309995969431623425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6424016206663979621082283 9636024309995969431623425)
      ·
        refine ⟨7227018232496977073717569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9636024309995969431623425 7227018232496977073717569)
        ·
          refine ⟨5420263674372732805288177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7227018232496977073717569 5420263674372732805288177)
          ·
            refine ⟨4065197755779549603966133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5420263674372732805288177 4065197755779549603966133)
            ·
              refine ⟨381112289604332775371825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4065197755779549603966133 381112289604332775371825)
              ·
                refine ⟨285834217203249581528869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381112289604332775371825 285834217203249581528869)
                ·
                  refine ⟨53593915725609296536663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285834217203249581528869 53593915725609296536663)
                  ·
                    rfl

theorem cell21_234841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_234841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_234841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_234841 prefixEnd_234841 := by exact prefixLift 234841
  have htrace : WordTrace (prefixWord ++ tailWord_234841) baseStart_234841 baseEnd_234841 := by
    simpa [prefixWord, tailWord_234841, baseEnd_234841] using wordTrace_append hprefix tailTrace_234841
  have hstable : (prefixWord ++ tailWord_234841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234841).length < 2 ^ (prefixWord ++ tailWord_234841).sum := by decide
  have hdescent : baseEnd_234841 < baseStart_234841 := by decide
  rcases family_descends (prefixWord ++ tailWord_234841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235010 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_235010 : Nat := 118140960795 + 235010 * 2 ^ 59
def prefixEnd_235010 : Nat := 4983230072969 + 3 ^ 40 * 235010 * 2
def baseEnd_235010 : Nat := 53632483828102558219651

theorem tailTrace_235010 : CollatzResearch.WordTrace tailWord_235010 prefixEnd_235010 53632483828102558219651 := by
  unfold tailWord_235010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142879719651595339419621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5714345919070920905118989 2142879719651595339419621)
  ·
    refine ⟨401789947434674126141179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2142879719651595339419621 401789947434674126141179)
    ·
      refine ⟨602684921152011189211769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401789947434674126141179 602684921152011189211769)
      ·
        refine ⟨452013690864008391908827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602684921152011189211769 452013690864008391908827)
        ·
          refine ⟨678020536296012587863241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452013690864008391908827 678020536296012587863241)
          ·
            refine ⟨508515402222009440897431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678020536296012587863241 508515402222009440897431)
            ·
              refine ⟨762773103333014161346147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508515402222009440897431 762773103333014161346147)
              ·
                refine ⟨1144159654999521242019221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762773103333014161346147 1144159654999521242019221)
                ·
                  refine ⟨53632483828102558219651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1144159654999521242019221 53632483828102558219651)
                  ·
                    rfl

theorem cell21_235010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_235010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235010 prefixEnd_235010 := by exact prefixLift 235010
  have htrace : WordTrace (prefixWord ++ tailWord_235010) baseStart_235010 baseEnd_235010 := by
    simpa [prefixWord, tailWord_235010, baseEnd_235010] using wordTrace_append hprefix tailTrace_235010
  have hstable : (prefixWord ++ tailWord_235010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235010).length < 2 ^ (prefixWord ++ tailWord_235010).sum := by decide
  have hdescent : baseEnd_235010 < baseStart_235010 := by decide
  rcases family_descends (prefixWord ++ tailWord_235010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235097 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 5]
def baseStart_235097 : Nat := 118140960795 + 235097 * 2 ^ 59
def prefixEnd_235097 : Nat := 4983230072969 + 3 ^ 40 * 235097 * 2
def baseEnd_235097 : Nat := 53652338413409740269473

theorem tailTrace_235097 : CollatzResearch.WordTrace tailWord_235097 prefixEnd_235097 53652338413409740269473 := by
  unfold tailWord_235097
  simp only [CollatzResearch.WordTrace]
  refine ⟨8574692029291195216095545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5716461352860796810730363 8574692029291195216095545)
  ·
    refine ⟨6431019021968396412071659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8574692029291195216095545 6431019021968396412071659)
    ·
      refine ⟨9646528532952594618107489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6431019021968396412071659 9646528532952594618107489)
      ·
        refine ⟨7234896399714445963580617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9646528532952594618107489 7234896399714445963580617)
        ·
          refine ⟨5426172299785834472685463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7234896399714445963580617 5426172299785834472685463)
          ·
            refine ⟨8139258449678751709028195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426172299785834472685463 8139258449678751709028195)
            ·
              refine ⟨12208887674518127563542293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8139258449678751709028195 12208887674518127563542293)
              ·
                refine ⟨572291609743037229541045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12208887674518127563542293 572291609743037229541045)
                ·
                  refine ⟨53652338413409740269473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 572291609743037229541045 53652338413409740269473)
                  ·
                    rfl

theorem cell21_235097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_235097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235097 prefixEnd_235097 := by exact prefixLift 235097
  have htrace : WordTrace (prefixWord ++ tailWord_235097) baseStart_235097 baseEnd_235097 := by
    simpa [prefixWord, tailWord_235097, baseEnd_235097] using wordTrace_append hprefix tailTrace_235097
  have hstable : (prefixWord ++ tailWord_235097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235097).length < 2 ^ (prefixWord ++ tailWord_235097).sum := by decide
  have hdescent : baseEnd_235097 < baseStart_235097 := by decide
  rcases family_descends (prefixWord ++ tailWord_235097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235266 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_235266 : Nat := 118140960795 + 235266 * 2 ^ 59
def prefixEnd_235266 : Nat := 4983230072969 + 3 ^ 40 * 235266 * 2
def baseEnd_235266 : Nat := 53690906515903001952461

theorem tailTrace_235266 : CollatzResearch.WordTrace tailWord_235266 prefixEnd_235266 53690906515903001952461 := by
  unfold tailWord_235266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2145213991419734269749413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5720570643785958052665101 2145213991419734269749413)
  ·
    refine ⟨402227623391200175578015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2145213991419734269749413 402227623391200175578015)
    ·
      refine ⟨603341435086800263367023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402227623391200175578015 603341435086800263367023)
      ·
        refine ⟨905012152630200395050535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603341435086800263367023 905012152630200395050535)
        ·
          refine ⟨1357518228945300592575803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905012152630200395050535 1357518228945300592575803)
          ·
            refine ⟨2036277343417950888863705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357518228945300592575803 2036277343417950888863705)
            ·
              refine ⟨1527208007563463166647779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2036277343417950888863705 1527208007563463166647779)
              ·
                refine ⟨2290812011345194749971669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527208007563463166647779 2290812011345194749971669)
                ·
                  refine ⟨53690906515903001952461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2290812011345194749971669 53690906515903001952461)
                  ·
                    rfl

theorem cell21_235266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_235266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235266 prefixEnd_235266 := by exact prefixLift 235266
  have htrace : WordTrace (prefixWord ++ tailWord_235266) baseStart_235266 baseEnd_235266 := by
    simpa [prefixWord, tailWord_235266, baseEnd_235266] using wordTrace_append hprefix tailTrace_235266
  have hstable : (prefixWord ++ tailWord_235266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235266).length < 2 ^ (prefixWord ++ tailWord_235266).sum := by decide
  have hdescent : baseEnd_235266 < baseStart_235266 := by decide
  rcases family_descends (prefixWord ++ tailWord_235266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235297 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 4]
def baseStart_235297 : Nat := 118140960795 + 235297 * 2 ^ 59
def prefixEnd_235297 : Nat := 4983230072969 + 3 ^ 40 * 235297 * 2
def baseEnd_235297 : Nat := 53697981138253836935731

theorem tailTrace_235297 : CollatzResearch.WordTrace tailWord_235297 prefixEnd_235297 53697981138253836935731 := by
  unfold tailWord_235297
  simp only [CollatzResearch.WordTrace]
  refine ⟨8581986628566629373376145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5721324419044419582250763 8581986628566629373376145)
  ·
    refine ⟨6436489971424972030032109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8581986628566629373376145 6436489971424972030032109)
    ·
      refine ⟨2413683739284364511262041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6436489971424972030032109 2413683739284364511262041)
      ·
        refine ⟨1810262804463273383446531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2413683739284364511262041 1810262804463273383446531)
        ·
          refine ⟨2715394206694910075169797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810262804463273383446531 2715394206694910075169797)
          ·
            refine ⟨509136413755295639094337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2715394206694910075169797 509136413755295639094337)
            ·
              refine ⟨381852310316471729320753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509136413755295639094337 381852310316471729320753)
              ·
                refine ⟨286389232737353796990565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381852310316471729320753 286389232737353796990565)
                ·
                  refine ⟨53697981138253836935731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286389232737353796990565 53697981138253836935731)
                  ·
                    rfl

theorem cell21_235297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_235297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235297 prefixEnd_235297 := by exact prefixLift 235297
  have htrace : WordTrace (prefixWord ++ tailWord_235297) baseStart_235297 baseEnd_235297 := by
    simpa [prefixWord, tailWord_235297, baseEnd_235297] using wordTrace_append hprefix tailTrace_235297
  have hstable : (prefixWord ++ tailWord_235297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235297).length < 2 ^ (prefixWord ++ tailWord_235297).sum := by decide
  have hdescent : baseEnd_235297 < baseStart_235297 := by decide
  rcases family_descends (prefixWord ++ tailWord_235297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235300 : List Nat := [2, 3, 1, 3, 2, 1, 4, 2, 3]
def baseStart_235300 : Nat := 118140960795 + 235300 * 2 ^ 59
def prefixEnd_235300 : Nat := 4983230072969 + 3 ^ 40 * 235300 * 2
def baseEnd_235300 : Nat := 53698665779126498385725

theorem tailTrace_235300 : CollatzResearch.WordTrace tailWord_235300 prefixEnd_235300 53698665779126498385725 := by
  unfold tailWord_235300
  simp only [CollatzResearch.WordTrace]
  refine ⟨4291048023777880442867677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5721397365037173923823569 4291048023777880442867677)
  ·
    refine ⟨1609143008916705166075379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4291048023777880442867677 1609143008916705166075379)
    ·
      refine ⟨2413714513375057749113069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1609143008916705166075379 2413714513375057749113069)
      ·
        refine ⟨905142942515646655917401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2413714513375057749113069 905142942515646655917401)
        ·
          refine ⟨678857206886734991938051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 905142942515646655917401 678857206886734991938051)
          ·
            refine ⟨1018285810330102487907077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678857206886734991938051 1018285810330102487907077)
            ·
              refine ⟨190928589436894216482577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1018285810330102487907077 190928589436894216482577)
              ·
                refine ⟨143196442077670662361933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190928589436894216482577 143196442077670662361933)
                ·
                  refine ⟨53698665779126498385725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143196442077670662361933 53698665779126498385725)
                  ·
                    rfl

theorem cell21_235300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_235300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235300 prefixEnd_235300 := by exact prefixLift 235300
  have htrace : WordTrace (prefixWord ++ tailWord_235300) baseStart_235300 baseEnd_235300 := by
    simpa [prefixWord, tailWord_235300, baseEnd_235300] using wordTrace_append hprefix tailTrace_235300
  have hstable : (prefixWord ++ tailWord_235300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235300).length < 2 ^ (prefixWord ++ tailWord_235300).sum := by decide
  have hdescent : baseEnd_235300 < baseStart_235300 := by decide
  rcases family_descends (prefixWord ++ tailWord_235300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235393 : List Nat := [1, 2, 4, 4, 1, 2, 1, 3, 3]
def baseStart_235393 : Nat := 118140960795 + 235393 * 2 ^ 59
def prefixEnd_235393 : Nat := 4983230072969 + 3 ^ 40 * 235393 * 2
def baseEnd_235393 : Nat := 53719889646179003335535

theorem tailTrace_235393 : CollatzResearch.WordTrace tailWord_235393 prefixEnd_235393 53719889646179003335535 := by
  unfold tailWord_235393
  simp only [CollatzResearch.WordTrace]
  refine ⟨8585488036218837768870833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5723658690812558512580555 8585488036218837768870833)
  ·
    refine ⟨6439116027164128326653125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8585488036218837768870833 6439116027164128326653125)
    ·
      refine ⟨1207334255093274061247461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6439116027164128326653125 1207334255093274061247461)
      ·
        refine ⟨226375172829988886483899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1207334255093274061247461 226375172829988886483899)
        ·
          refine ⟨339562759244983329725849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226375172829988886483899 339562759244983329725849)
          ·
            refine ⟨254672069433737497294387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339562759244983329725849 254672069433737497294387)
            ·
              refine ⟨382008104150606245941581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254672069433737497294387 382008104150606245941581)
              ·
                refine ⟨143253039056477342228093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382008104150606245941581 143253039056477342228093)
                ·
                  refine ⟨53719889646179003335535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143253039056477342228093 53719889646179003335535)
                  ·
                    rfl

theorem cell21_235393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 3].length) (baseStart_235393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235393 prefixEnd_235393 := by exact prefixLift 235393
  have htrace : WordTrace (prefixWord ++ tailWord_235393) baseStart_235393 baseEnd_235393 := by
    simpa [prefixWord, tailWord_235393, baseEnd_235393] using wordTrace_append hprefix tailTrace_235393
  have hstable : (prefixWord ++ tailWord_235393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235393).length < 2 ^ (prefixWord ++ tailWord_235393).sum := by decide
  have hdescent : baseEnd_235393 < baseStart_235393 := by decide
  rcases family_descends (prefixWord ++ tailWord_235393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235418 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_235418 : Nat := 118140960795 + 235418 * 2 ^ 59
def prefixEnd_235418 : Nat := 4983230072969 + 3 ^ 40 * 235418 * 2
def baseEnd_235418 : Nat := 53725594986784515418817

theorem tailTrace_235418 : CollatzResearch.WordTrace tailWord_235418 prefixEnd_235418 53725594986784515418817 := by
  unfold tailWord_235418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2146599965282066759632727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5724266574085511359020605 2146599965282066759632727)
  ·
    refine ⟨3219899947923100139449091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2146599965282066759632727 3219899947923100139449091)
    ·
      refine ⟨4829849921884650209173637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3219899947923100139449091 4829849921884650209173637)
      ·
        refine ⟨905596860353371914220057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4829849921884650209173637 905596860353371914220057)
        ·
          refine ⟨679197645265028935665043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 905596860353371914220057 679197645265028935665043)
          ·
            refine ⟨1018796467897543403497565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679197645265028935665043 1018796467897543403497565)
            ·
              refine ⟨382048675461578776311587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1018796467897543403497565 382048675461578776311587)
              ·
                refine ⟨573073013192368164467381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382048675461578776311587 573073013192368164467381)
                ·
                  refine ⟨53725594986784515418817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 573073013192368164467381 53725594986784515418817)
                  ·
                    rfl

theorem cell21_235418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_235418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235418 prefixEnd_235418 := by exact prefixLift 235418
  have htrace : WordTrace (prefixWord ++ tailWord_235418) baseStart_235418 baseEnd_235418 := by
    simpa [prefixWord, tailWord_235418, baseEnd_235418] using wordTrace_append hprefix tailTrace_235418
  have hstable : (prefixWord ++ tailWord_235418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235418).length < 2 ^ (prefixWord ++ tailWord_235418).sum := by decide
  have hdescent : baseEnd_235418 < baseStart_235418 := by decide
  rcases family_descends (prefixWord ++ tailWord_235418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235525 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 4]
def baseStart_235525 : Nat := 118140960795 + 235525 * 2 ^ 59
def prefixEnd_235525 : Nat := 4983230072969 + 3 ^ 40 * 235525 * 2
def baseEnd_235525 : Nat := 53750013844576107135265

theorem tailTrace_235525 : CollatzResearch.WordTrace tailWord_235525 prefixEnd_235525 53750013844576107135265 := by
  unfold tailWord_235525
  simp only [CollatzResearch.WordTrace]
  refine ⟨8590302471740624312676029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5726868314493749541784019 8590302471740624312676029)
  ·
    refine ⟨3221363426902734117253511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8590302471740624312676029 3221363426902734117253511)
    ·
      refine ⟨4832045140354101175880267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3221363426902734117253511 4832045140354101175880267)
      ·
        refine ⟨7248067710531151763820401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4832045140354101175880267 7248067710531151763820401)
        ·
          refine ⟨5436050782898363822865301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7248067710531151763820401 5436050782898363822865301)
          ·
            refine ⟨254814880448360804196811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5436050782898363822865301 254814880448360804196811)
            ·
              refine ⟨382222320672541206295217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254814880448360804196811 382222320672541206295217)
              ·
                refine ⟨286666740504405904721413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382222320672541206295217 286666740504405904721413)
                ·
                  refine ⟨53750013844576107135265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286666740504405904721413 53750013844576107135265)
                  ·
                    rfl

theorem cell21_235525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_235525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235525 prefixEnd_235525 := by exact prefixLift 235525
  have htrace : WordTrace (prefixWord ++ tailWord_235525) baseStart_235525 baseEnd_235525 := by
    simpa [prefixWord, tailWord_235525, baseEnd_235525] using wordTrace_append hprefix tailTrace_235525
  have hstable : (prefixWord ++ tailWord_235525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235525).length < 2 ^ (prefixWord ++ tailWord_235525).sum := by decide
  have hdescent : baseEnd_235525 < baseStart_235525 := by decide
  rcases family_descends (prefixWord ++ tailWord_235525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235536 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_235536 : Nat := 118140960795 + 235536 * 2 ^ 59
def prefixEnd_235536 : Nat := 4983230072969 + 3 ^ 40 * 235536 * 2
def baseEnd_235536 : Nat := 53752524194442532451909

theorem tailTrace_235536 : CollatzResearch.WordTrace tailWord_235536 prefixEnd_235536 53752524194442532451909 := by
  unfold tailWord_235536
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295351837350386595663231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5727135783133848794217641 4295351837350386595663231)
  ·
    refine ⟨6443027756025579893494847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4295351837350386595663231 6443027756025579893494847)
    ·
      refine ⟨9664541634038369840242271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6443027756025579893494847 9664541634038369840242271)
      ·
        refine ⟨14496812451057554760363407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9664541634038369840242271 14496812451057554760363407)
        ·
          refine ⟨21745218676586332140545111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14496812451057554760363407 21745218676586332140545111)
          ·
            refine ⟨32617828014879498210817667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21745218676586332140545111 32617828014879498210817667)
            ·
              refine ⟨48926742022319247316226501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32617828014879498210817667 48926742022319247316226501)
              ·
                refine ⟨9173764129184858871792469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48926742022319247316226501 9173764129184858871792469)
                ·
                  refine ⟨53752524194442532451909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9173764129184858871792469 53752524194442532451909)
                  ·
                    rfl

theorem cell21_235536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_235536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235536 prefixEnd_235536 := by exact prefixLift 235536
  have htrace : WordTrace (prefixWord ++ tailWord_235536) baseStart_235536 baseEnd_235536 := by
    simpa [prefixWord, tailWord_235536, baseEnd_235536] using wordTrace_append hprefix tailTrace_235536
  have hstable : (prefixWord ++ tailWord_235536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235536).length < 2 ^ (prefixWord ++ tailWord_235536).sum := by decide
  have hdescent : baseEnd_235536 < baseStart_235536 := by decide
  rcases family_descends (prefixWord ++ tailWord_235536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235598 : List Nat := [4, 1, 1, 1, 1, 4, 1, 8]
def baseStart_235598 : Nat := 118140960795 + 235598 * 2 ^ 59
def prefixEnd_235598 : Nat := 4983230072969 + 3 ^ 40 * 235598 * 2
def baseEnd_235598 : Nat := 17922224479714734139483

theorem tailTrace_235598 : CollatzResearch.WordTrace tailWord_235598 prefixEnd_235598 17922224479714734139483 := by
  unfold tailWord_235598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074120625059519722510431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5728643333650771853388965 1074120625059519722510431)
  ·
    refine ⟨1611180937589279583765647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1074120625059519722510431 1611180937589279583765647)
    ·
      refine ⟨2416771406383919375648471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1611180937589279583765647 2416771406383919375648471)
      ·
        refine ⟨3625157109575879063472707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416771406383919375648471 3625157109575879063472707)
        ·
          refine ⟨5437735664363818595209061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3625157109575879063472707 5437735664363818595209061)
          ·
            refine ⟨1019575437068215986601699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5437735664363818595209061 1019575437068215986601699)
            ·
              refine ⟨1529363155602323979902549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019575437068215986601699 1529363155602323979902549)
              ·
                refine ⟨17922224479714734139483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1529363155602323979902549 17922224479714734139483)
                ·
                  rfl

theorem cell21_235598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_235598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235598 prefixEnd_235598 := by exact prefixLift 235598
  have htrace : WordTrace (prefixWord ++ tailWord_235598) baseStart_235598 baseEnd_235598 := by
    simpa [prefixWord, tailWord_235598, baseEnd_235598] using wordTrace_append hprefix tailTrace_235598
  have hstable : (prefixWord ++ tailWord_235598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235598).length < 2 ^ (prefixWord ++ tailWord_235598).sum := by decide
  have hdescent : baseEnd_235598 < baseStart_235598 := by decide
  rcases family_descends (prefixWord ++ tailWord_235598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235694 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_235694 : Nat := 118140960795 + 235694 * 2 ^ 59
def prefixEnd_235694 : Nat := 4983230072969 + 3 ^ 40 * 235694 * 2
def baseEnd_235694 : Nat := 53788581947069368818253

theorem tailTrace_235694 : CollatzResearch.WordTrace tailWord_235694 prefixEnd_235694 53788581947069368818253 := by
  unfold tailWord_235694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074558301016045771947267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5730977605418910783718757 1074558301016045771947267)
  ·
    refine ⟨1611837451524068657920901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1074558301016045771947267 1611837451524068657920901)
    ·
      refine ⟨302219522160762873360169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1611837451524068657920901 302219522160762873360169)
      ·
        refine ⟨226664641620572155020127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302219522160762873360169 226664641620572155020127)
        ·
          refine ⟨339996962430858232530191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226664641620572155020127 339996962430858232530191)
          ·
            refine ⟨509995443646287348795287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339996962430858232530191 509995443646287348795287)
            ·
              refine ⟨764993165469431023192931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509995443646287348795287 764993165469431023192931)
              ·
                refine ⟨1147489748204146534789397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764993165469431023192931 1147489748204146534789397)
                ·
                  refine ⟨53788581947069368818253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1147489748204146534789397 53788581947069368818253)
                  ·
                    rfl

theorem cell21_235694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_235694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235694 prefixEnd_235694 := by exact prefixLift 235694
  have htrace : WordTrace (prefixWord ++ tailWord_235694) baseStart_235694 baseEnd_235694 := by
    simpa [prefixWord, tailWord_235694, baseEnd_235694] using wordTrace_append hprefix tailTrace_235694
  have hstable : (prefixWord ++ tailWord_235694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235694).length < 2 ^ (prefixWord ++ tailWord_235694).sum := by decide
  have hdescent : baseEnd_235694 < baseStart_235694 := by decide
  rcases family_descends (prefixWord ++ tailWord_235694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235705 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 5]
def baseStart_235705 : Nat := 118140960795 + 235705 * 2 ^ 59
def prefixEnd_235705 : Nat := 4983230072969 + 3 ^ 40 * 235705 * 2
def baseEnd_235705 : Nat := 53791092296935794134897

theorem tailTrace_235705 : CollatzResearch.WordTrace tailWord_235705 prefixEnd_235705 53791092296935794134897 := by
  unfold tailWord_235705
  simp only [CollatzResearch.WordTrace]
  refine ⟨8596867611088515054228569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5731245074059010036152379 8596867611088515054228569)
  ·
    refine ⟨6447650708316386290671427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8596867611088515054228569 6447650708316386290671427)
    ·
      refine ⟨9671476062474579436007141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6447650708316386290671427 9671476062474579436007141)
      ·
        refine ⟨1813401761713983644251339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9671476062474579436007141 1813401761713983644251339)
        ·
          refine ⟨2720102642570975466377009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813401761713983644251339 2720102642570975466377009)
          ·
            refine ⟨2040076981928231599782757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2720102642570975466377009 2040076981928231599782757)
            ·
              refine ⟨382514434111543424959267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2040076981928231599782757 382514434111543424959267)
              ·
                refine ⟨573771651167315137438901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382514434111543424959267 573771651167315137438901)
                ·
                  refine ⟨53791092296935794134897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 573771651167315137438901 53791092296935794134897)
                  ·
                    rfl

theorem cell21_235705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_235705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235705 prefixEnd_235705 := by exact prefixLift 235705
  have htrace : WordTrace (prefixWord ++ tailWord_235705) baseStart_235705 baseEnd_235705 := by
    simpa [prefixWord, tailWord_235705, baseEnd_235705] using wordTrace_append hprefix tailTrace_235705
  have hstable : (prefixWord ++ tailWord_235705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235705).length < 2 ^ (prefixWord ++ tailWord_235705).sum := by decide
  have hdescent : baseEnd_235705 < baseStart_235705 := by decide
  rcases family_descends (prefixWord ++ tailWord_235705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235812 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 4]
def baseStart_235812 : Nat := 118140960795 + 235812 * 2 ^ 59
def prefixEnd_235812 : Nat := 4983230072969 + 3 ^ 40 * 235812 * 2
def baseEnd_235812 : Nat := 53815511154727385851345

theorem tailTrace_235812 : CollatzResearch.WordTrace tailWord_235812 prefixEnd_235812 53815511154727385851345 := by
  unfold tailWord_235812
  simp only [CollatzResearch.WordTrace]
  refine ⟨4300385110850436164186845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5733846814467248218915793 4300385110850436164186845)
  ·
    refine ⟨1612644416568913561570067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4300385110850436164186845 1612644416568913561570067)
    ·
      refine ⟨2418966624853370342355101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612644416568913561570067 2418966624853370342355101)
      ·
        refine ⟨907112484320013878383163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2418966624853370342355101 907112484320013878383163)
        ·
          refine ⟨1360668726480020817574745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907112484320013878383163 1360668726480020817574745)
          ·
            refine ⟨1020501544860015613181059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1360668726480020817574745 1020501544860015613181059)
            ·
              refine ⟨1530752317290023419771589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020501544860015613181059 1530752317290023419771589)
              ·
                refine ⟨287016059491879391207173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1530752317290023419771589 287016059491879391207173)
                ·
                  refine ⟨53815511154727385851345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287016059491879391207173 53815511154727385851345)
                  ·
                    rfl

theorem cell21_235812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_235812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235812 prefixEnd_235812 := by exact prefixLift 235812
  have htrace : WordTrace (prefixWord ++ tailWord_235812) baseStart_235812 baseEnd_235812 := by
    simpa [prefixWord, tailWord_235812, baseEnd_235812] using wordTrace_append hprefix tailTrace_235812
  have hstable : (prefixWord ++ tailWord_235812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235812).length < 2 ^ (prefixWord ++ tailWord_235812).sum := by decide
  have hdescent : baseEnd_235812 < baseStart_235812 := by decide
  rcases family_descends (prefixWord ++ tailWord_235812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235874 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_235874 : Nat := 118140960795 + 235874 * 2 ^ 59
def prefixEnd_235874 : Nat := 4983230072969 + 3 ^ 40 * 235874 * 2
def baseEnd_235874 : Nat := 53829660399429055817885

theorem tailTrace_235874 : CollatzResearch.WordTrace tailWord_235874 prefixEnd_235874 53829660399429055817885 := by
  unfold tailWord_235874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2150757886869064229282669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5735354364984171278087117 2150757886869064229282669)
  ·
    refine ⟨806534207575899085981001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2150757886869064229282669 806534207575899085981001)
    ·
      refine ⟨604900655681924314485751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 806534207575899085981001 604900655681924314485751)
      ·
        refine ⟨907350983522886471728627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604900655681924314485751 907350983522886471728627)
        ·
          refine ⟨1361026475284329707592941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907350983522886471728627 1361026475284329707592941)
          ·
            refine ⟨510384928231623640347353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1361026475284329707592941 510384928231623640347353)
            ·
              refine ⟨382788696173717730260515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510384928231623640347353 382788696173717730260515)
              ·
                refine ⟨574183044260576595390773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382788696173717730260515 574183044260576595390773)
                ·
                  refine ⟨53829660399429055817885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 574183044260576595390773 53829660399429055817885)
                  ·
                    rfl

theorem cell21_235874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_235874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235874 prefixEnd_235874 := by exact prefixLift 235874
  have htrace : WordTrace (prefixWord ++ tailWord_235874) baseStart_235874 baseEnd_235874 := by
    simpa [prefixWord, tailWord_235874, baseEnd_235874] using wordTrace_append hprefix tailTrace_235874
  have hstable : (prefixWord ++ tailWord_235874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235874).length < 2 ^ (prefixWord ++ tailWord_235874).sum := by decide
  have hdescent : baseEnd_235874 < baseStart_235874 := by decide
  rcases family_descends (prefixWord ++ tailWord_235874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235894 : List Nat := [5, 1, 1, 4, 2, 1, 2, 5]
def baseStart_235894 : Nat := 118140960795 + 235894 * 2 ^ 59
def prefixEnd_235894 : Nat := 4983230072969 + 3 ^ 40 * 235894 * 2
def baseEnd_235894 : Nat := 17944741557304488494837

theorem tailTrace_235894 : CollatzResearch.WordTrace tailWord_235894 prefixEnd_235894 17944741557304488494837 := by
  unfold tailWord_235894
  simp only [CollatzResearch.WordTrace]
  refine ⟨537735062962737520803671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5735840671602533555239157 537735062962737520803671)
  ·
    refine ⟨806602594444106281205507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 537735062962737520803671 806602594444106281205507)
    ·
      refine ⟨1209903891666159421808261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 806602594444106281205507 1209903891666159421808261)
      ·
        refine ⟨226856979687404891589049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1209903891666159421808261 226856979687404891589049)
        ·
          refine ⟨170142734765553668691787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226856979687404891589049 170142734765553668691787)
          ·
            refine ⟨255214102148330503037681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170142734765553668691787 255214102148330503037681)
            ·
              refine ⟨191410576611247877278261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255214102148330503037681 191410576611247877278261)
              ·
                refine ⟨17944741557304488494837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191410576611247877278261 17944741557304488494837)
                ·
                  rfl

theorem cell21_235894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_235894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235894 prefixEnd_235894 := by exact prefixLift 235894
  have htrace : WordTrace (prefixWord ++ tailWord_235894) baseStart_235894 baseEnd_235894 := by
    simpa [prefixWord, tailWord_235894, baseEnd_235894] using wordTrace_append hprefix tailTrace_235894
  have hstable : (prefixWord ++ tailWord_235894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235894).length < 2 ^ (prefixWord ++ tailWord_235894).sum := by decide
  have hdescent : baseEnd_235894 < baseStart_235894 := by decide
  rcases family_descends (prefixWord ++ tailWord_235894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235992 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_235992 : Nat := 118140960795 + 235992 * 2 ^ 59
def prefixEnd_235992 : Nat := 4983230072969 + 3 ^ 40 * 235992 * 2
def baseEnd_235992 : Nat := 53856589607087072850977

theorem tailTrace_235992 : CollatzResearch.WordTrace tailWord_235992 prefixEnd_235992 53856589607087072850977 := by
  unfold tailWord_235992
  simp only [CollatzResearch.WordTrace]
  refine ⟨4303667680524381534963115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5738223574032508713284153 4303667680524381534963115)
  ·
    refine ⟨6455501520786572302444673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4303667680524381534963115 6455501520786572302444673)
    ·
      refine ⟨4841626140589929226833505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6455501520786572302444673 4841626140589929226833505)
      ·
        refine ⟨3631219605442446920125129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4841626140589929226833505 3631219605442446920125129)
        ·
          refine ⟨2723414704081835190093847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3631219605442446920125129 2723414704081835190093847)
          ·
            refine ⟨4085122056122752785140771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723414704081835190093847 4085122056122752785140771)
            ·
              refine ⟨6127683084184129177711157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4085122056122752785140771 6127683084184129177711157)
              ·
                refine ⟨574470289142262110410421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6127683084184129177711157 574470289142262110410421)
                ·
                  refine ⟨53856589607087072850977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 574470289142262110410421 53856589607087072850977)
                  ·
                    rfl

theorem cell21_235992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_235992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_235992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_235992 prefixEnd_235992 := by exact prefixLift 235992
  have htrace : WordTrace (prefixWord ++ tailWord_235992) baseStart_235992 baseEnd_235992 := by
    simpa [prefixWord, tailWord_235992, baseEnd_235992] using wordTrace_append hprefix tailTrace_235992
  have hstable : (prefixWord ++ tailWord_235992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235992).length < 2 ^ (prefixWord ++ tailWord_235992).sum := by decide
  have hdescent : baseEnd_235992 < baseStart_235992 := by decide
  rcases family_descends (prefixWord ++ tailWord_235992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236113 : List Nat := [1, 2, 2, 1, 3, 3, 1, 8]
def baseStart_236113 : Nat := 118140960795 + 236113 * 2 ^ 59
def prefixEnd_236113 : Nat := 4983230072969 + 3 ^ 40 * 236113 * 2
def baseEnd_236113 : Nat := 17961401151872583778021

theorem tailTrace_236113 : CollatzResearch.WordTrace tailWord_236113 prefixEnd_236113 17961401151872583778021 := by
  unfold tailWord_236113
  simp only [CollatzResearch.WordTrace]
  refine ⟨8611748593610400735080993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5741165729073600490053995 8611748593610400735080993)
  ·
    refine ⟨6458811445207800551310745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8611748593610400735080993 6458811445207800551310745)
    ·
      refine ⟨4844108583905850413483059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6458811445207800551310745 4844108583905850413483059)
      ·
        refine ⟨7266162875858775620224589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4844108583905850413483059 7266162875858775620224589)
        ·
          refine ⟨2724811078447040857584221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7266162875858775620224589 2724811078447040857584221)
          ·
            refine ⟨1021804154417640321594083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2724811078447040857584221 1021804154417640321594083)
            ·
              refine ⟨1532706231626460482391125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021804154417640321594083 1532706231626460482391125)
              ·
                refine ⟨17961401151872583778021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1532706231626460482391125 17961401151872583778021)
                ·
                  rfl

theorem cell21_236113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 8].length) (baseStart_236113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236113 prefixEnd_236113 := by exact prefixLift 236113
  have htrace : WordTrace (prefixWord ++ tailWord_236113) baseStart_236113 baseEnd_236113 := by
    simpa [prefixWord, tailWord_236113, baseEnd_236113] using wordTrace_append hprefix tailTrace_236113
  have hstable : (prefixWord ++ tailWord_236113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236113).length < 2 ^ (prefixWord ++ tailWord_236113).sum := by decide
  have hdescent : baseEnd_236113 < baseStart_236113 := by decide
  rcases family_descends (prefixWord ++ tailWord_236113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236116 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 4]
def baseStart_236116 : Nat := 118140960795 + 236116 * 2 ^ 59
def prefixEnd_236116 : Nat := 4983230072969 + 3 ^ 40 * 236116 * 2
def baseEnd_236116 : Nat := 53884888096490412784057

theorem tailTrace_236116 : CollatzResearch.WordTrace tailWord_236116 prefixEnd_236116 53884888096490412784057 := by
  unfold tailWord_236116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4305929006299766123720101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5741238675066354831626801 4305929006299766123720101)
  ·
    refine ⟨807361688681206148197519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4305929006299766123720101 807361688681206148197519)
    ·
      refine ⟨1211042533021809222296279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807361688681206148197519 1211042533021809222296279)
      ·
        refine ⟨1816563799532713833444419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1211042533021809222296279 1816563799532713833444419)
        ·
          refine ⟨2724845699299070750166629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816563799532713833444419 2724845699299070750166629)
          ·
            refine ⟨510908568618575765656243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2724845699299070750166629 510908568618575765656243)
            ·
              refine ⟨766362852927863648484365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510908568618575765656243 766362852927863648484365)
              ·
                refine ⟨287386069847948868181637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 766362852927863648484365 287386069847948868181637)
                ·
                  refine ⟨53884888096490412784057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287386069847948868181637 53884888096490412784057)
                  ·
                    rfl

theorem cell21_236116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_236116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236116 prefixEnd_236116 := by exact prefixLift 236116
  have htrace : WordTrace (prefixWord ++ tailWord_236116) baseStart_236116 baseEnd_236116 := by
    simpa [prefixWord, tailWord_236116, baseEnd_236116] using wordTrace_append hprefix tailTrace_236116
  have hstable : (prefixWord ++ tailWord_236116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236116).length < 2 ^ (prefixWord ++ tailWord_236116).sum := by decide
  have hdescent : baseEnd_236116 < baseStart_236116 := by decide
  rcases family_descends (prefixWord ++ tailWord_236116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236189 : List Nat := [1, 4, 2, 1, 1, 1, 2, 9]
def baseStart_236189 : Nat := 118140960795 + 236189 * 2 ^ 59
def prefixEnd_236189 : Nat := 4983230072969 + 3 ^ 40 * 236189 * 2
def baseEnd_236189 : Nat := 17967182563686169355747

theorem tailTrace_236189 : CollatzResearch.WordTrace tailWord_236189 prefixEnd_236189 17967182563686169355747 := by
  unfold tailWord_236189
  simp only [CollatzResearch.WordTrace]
  refine ⟨8614520541335065714847621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5743013694223377143231747 8614520541335065714847621)
  ·
    refine ⟨1615222601500324821533929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8614520541335065714847621 1615222601500324821533929)
    ·
      refine ⟨1211416951125243616150447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1615222601500324821533929 1211416951125243616150447)
      ·
        refine ⟨1817125426687865424225671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1211416951125243616150447 1817125426687865424225671)
        ·
          refine ⟨2725688140031798136338507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1817125426687865424225671 2725688140031798136338507)
          ·
            refine ⟨4088532210047697204507761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725688140031798136338507 4088532210047697204507761)
            ·
              refine ⟨3066399157535772903380821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4088532210047697204507761 3066399157535772903380821)
              ·
                refine ⟨17967182563686169355747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3066399157535772903380821 17967182563686169355747)
                ·
                  rfl

theorem cell21_236189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 9].length) (baseStart_236189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236189 prefixEnd_236189 := by exact prefixLift 236189
  have htrace : WordTrace (prefixWord ++ tailWord_236189) baseStart_236189 baseEnd_236189 := by
    simpa [prefixWord, tailWord_236189, baseEnd_236189] using wordTrace_append hprefix tailTrace_236189
  have hstable : (prefixWord ++ tailWord_236189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236189).length < 2 ^ (prefixWord ++ tailWord_236189).sum := by decide
  have hdescent : baseEnd_236189 < baseStart_236189 := by decide
  rcases family_descends (prefixWord ++ tailWord_236189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236333 : List Nat := [1, 5, 3, 2, 2, 1, 1, 6]
def baseStart_236333 : Nat := 118140960795 + 236333 * 2 ^ 59
def prefixEnd_236333 : Nat := 4983230072969 + 3 ^ 40 * 236333 * 2
def baseEnd_236333 : Nat := 17978136817648752555649

theorem tailTrace_236333 : CollatzResearch.WordTrace tailWord_236333 prefixEnd_236333 17978136817648752555649 := by
  unfold tailWord_236333
  simp only [CollatzResearch.WordTrace]
  refine ⟨8619772652813378308089653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5746515101875585538726435 8619772652813378308089653)
  ·
    refine ⟨808103686201254216383405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8619772652813378308089653 808103686201254216383405)
    ·
      refine ⟨303038882325470331143777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 808103686201254216383405 303038882325470331143777)
      ·
        refine ⟨227279161744102748357833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303038882325470331143777 227279161744102748357833)
        ·
          refine ⟨170459371308077061268375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227279161744102748357833 170459371308077061268375)
          ·
            refine ⟨255689056962115591902563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170459371308077061268375 255689056962115591902563)
            ·
              refine ⟨383533585443173387853845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255689056962115591902563 383533585443173387853845)
              ·
                refine ⟨17978136817648752555649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 383533585443173387853845 17978136817648752555649)
                ·
                  rfl

theorem cell21_236333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 6].length) (baseStart_236333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236333 prefixEnd_236333 := by exact prefixLift 236333
  have htrace : WordTrace (prefixWord ++ tailWord_236333) baseStart_236333 baseEnd_236333 := by
    simpa [prefixWord, tailWord_236333, baseEnd_236333] using wordTrace_append hprefix tailTrace_236333
  have hstable : (prefixWord ++ tailWord_236333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236333).length < 2 ^ (prefixWord ++ tailWord_236333).sum := by decide
  have hdescent : baseEnd_236333 < baseStart_236333 := by decide
  rcases family_descends (prefixWord ++ tailWord_236333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236389 : List Nat := [1, 3, 1, 3, 1, 1, 4, 4, 3]
def baseStart_236389 : Nat := 118140960795 + 236389 * 2 ^ 59
def prefixEnd_236389 : Nat := 4983230072969 + 3 ^ 40 * 236389 * 2
def baseEnd_236389 : Nat := 53947190415902604733499

theorem tailTrace_236389 : CollatzResearch.WordTrace tailWord_236389 prefixEnd_236389 53947190415902604733499 := by
  unfold tailWord_236389
  simp only [CollatzResearch.WordTrace]
  refine ⟨8621815140610499872128221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5747876760406999914752147 8621815140610499872128221)
  ·
    refine ⟨3233180677728937452048083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8621815140610499872128221 3233180677728937452048083)
    ·
      refine ⟨4849771016593406178072125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3233180677728937452048083 4849771016593406178072125)
      ·
        refine ⟨1818664131222527316777047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4849771016593406178072125 1818664131222527316777047)
        ·
          refine ⟨2727996196833790975165571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818664131222527316777047 2727996196833790975165571)
          ·
            refine ⟨4091994295250686462748357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727996196833790975165571 4091994295250686462748357)
            ·
              refine ⟨767248930359503711765317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4091994295250686462748357 767248930359503711765317)
              ·
                refine ⟨143859174442406945955997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767248930359503711765317 143859174442406945955997)
                ·
                  refine ⟨53947190415902604733499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143859174442406945955997 53947190415902604733499)
                  ·
                    rfl

theorem cell21_236389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_236389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236389 prefixEnd_236389 := by exact prefixLift 236389
  have htrace : WordTrace (prefixWord ++ tailWord_236389) baseStart_236389 baseEnd_236389 := by
    simpa [prefixWord, tailWord_236389, baseEnd_236389] using wordTrace_append hprefix tailTrace_236389
  have hstable : (prefixWord ++ tailWord_236389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236389).length < 2 ^ (prefixWord ++ tailWord_236389).sum := by decide
  have hdescent : baseEnd_236389 < baseStart_236389 := by decide
  rcases family_descends (prefixWord ++ tailWord_236389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236448 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 5]
def baseStart_236448 : Nat := 118140960795 + 236448 * 2 ^ 59
def prefixEnd_236448 : Nat := 4983230072969 + 3 ^ 40 * 236448 * 2
def baseEnd_236448 : Nat := 53960655019731613250045

theorem tailTrace_236448 : CollatzResearch.WordTrace tailWord_236448 prefixEnd_236448 53960655019731613250045 := by
  unfold tailWord_236448
  simp only [CollatzResearch.WordTrace]
  refine ⟨4311983523698376474262999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5749311364931168632350665 4311983523698376474262999)
  ·
    refine ⟨6467975285547564711394499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4311983523698376474262999 6467975285547564711394499)
    ·
      refine ⟨9701962928321347067091749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6467975285547564711394499 9701962928321347067091749)
      ·
        refine ⟨1819118049060252575079703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9701962928321347067091749 1819118049060252575079703)
        ·
          refine ⟨2728677073590378862619555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819118049060252575079703 2728677073590378862619555)
          ·
            refine ⟨4093015610385568293929333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728677073590378862619555 4093015610385568293929333)
            ·
              refine ⟨383720213473647027555875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4093015610385568293929333 383720213473647027555875)
              ·
                refine ⟨575580320210470541333813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383720213473647027555875 575580320210470541333813)
                ·
                  refine ⟨53960655019731613250045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 575580320210470541333813 53960655019731613250045)
                  ·
                    rfl

theorem cell21_236448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_236448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236448 prefixEnd_236448 := by exact prefixLift 236448
  have htrace : WordTrace (prefixWord ++ tailWord_236448) baseStart_236448 baseEnd_236448 := by
    simpa [prefixWord, tailWord_236448, baseEnd_236448] using wordTrace_append hprefix tailTrace_236448
  have hstable : (prefixWord ++ tailWord_236448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236448).length < 2 ^ (prefixWord ++ tailWord_236448).sum := by decide
  have hdescent : baseEnd_236448 < baseStart_236448 := by decide
  rcases family_descends (prefixWord ++ tailWord_236448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236555 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 4]
def baseStart_236555 : Nat := 118140960795 + 236555 * 2 ^ 59
def prefixEnd_236555 : Nat := 4983230072969 + 3 ^ 40 * 236555 * 2
def baseEnd_236555 : Nat := 53985073877523204966493

theorem tailTrace_236555 : CollatzResearch.WordTrace tailWord_236555 prefixEnd_236555 53985073877523204966493 := by
  unfold tailWord_236555
  simp only [CollatzResearch.WordTrace]
  refine ⟨8627869658009110222671119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5751913105339406815114079 8627869658009110222671119)
  ·
    refine ⟨12941804487013665334006679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8627869658009110222671119 12941804487013665334006679)
    ·
      refine ⟨19412706730520498001010019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12941804487013665334006679 19412706730520498001010019)
      ·
        refine ⟨29119060095780747001515029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19412706730520498001010019 29119060095780747001515029)
        ·
          refine ⟨1364955941989722515696017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29119060095780747001515029 1364955941989722515696017)
          ·
            refine ⟨1023716956492291886772013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364955941989722515696017 1023716956492291886772013)
            ·
              refine ⟨383893858684609457539505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1023716956492291886772013 383893858684609457539505)
              ·
                refine ⟨287920394013457093154629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 383893858684609457539505 287920394013457093154629)
                ·
                  refine ⟨53985073877523204966493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 287920394013457093154629 53985073877523204966493)
                  ·
                    rfl

theorem cell21_236555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 4].length) (baseStart_236555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236555 prefixEnd_236555 := by exact prefixLift 236555
  have htrace : WordTrace (prefixWord ++ tailWord_236555) baseStart_236555 baseEnd_236555 := by
    simpa [prefixWord, tailWord_236555, baseEnd_236555] using wordTrace_append hprefix tailTrace_236555
  have hstable : (prefixWord ++ tailWord_236555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236555).length < 2 ^ (prefixWord ++ tailWord_236555).sum := by decide
  have hdescent : baseEnd_236555 < baseStart_236555 := by decide
  rcases family_descends (prefixWord ++ tailWord_236555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236586 : List Nat := [3, 1, 4, 1, 3, 1, 1, 7]
def baseStart_236586 : Nat := 118140960795 + 236586 * 2 ^ 59
def prefixEnd_236586 : Nat := 4983230072969 + 3 ^ 40 * 236586 * 2
def baseEnd_236586 : Nat := 17997382833291346649921

theorem tailTrace_236586 : CollatzResearch.WordTrace tailWord_236586 prefixEnd_236586 17997382833291346649921 := by
  unfold tailWord_236586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157250080224200629262403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5752666880597868344699741 2157250080224200629262403)
  ·
    refine ⟨3235875120336300943893605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2157250080224200629262403 3235875120336300943893605)
    ·
      refine ⟨606726585063056426980051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3235875120336300943893605 606726585063056426980051)
      ·
        refine ⟨910089877594584640470077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606726585063056426980051 910089877594584640470077)
        ·
          refine ⟨341283704097969240176279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 910089877594584640470077 341283704097969240176279)
          ·
            refine ⟨511925556146953860264419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341283704097969240176279 511925556146953860264419)
            ·
              refine ⟨767888334220430790396629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511925556146953860264419 767888334220430790396629)
              ·
                refine ⟨17997382833291346649921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 767888334220430790396629 17997382833291346649921)
                ·
                  rfl

theorem cell21_236586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_236586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236586 prefixEnd_236586 := by exact prefixLift 236586
  have htrace : WordTrace (prefixWord ++ tailWord_236586) baseStart_236586 baseEnd_236586 := by
    simpa [prefixWord, tailWord_236586, baseEnd_236586] using wordTrace_append hprefix tailTrace_236586
  have hstable : (prefixWord ++ tailWord_236586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236586).length < 2 ^ (prefixWord ++ tailWord_236586).sum := by decide
  have hdescent : baseEnd_236586 < baseStart_236586 := by decide
  rcases family_descends (prefixWord ++ tailWord_236586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236721 : List Nat := [1, 2, 2, 5, 1, 2, 8]
def baseStart_236721 : Nat := 118140960795 + 236721 * 2 ^ 59
def prefixEnd_236721 : Nat := 4983230072969 + 3 ^ 40 * 236721 * 2
def baseEnd_236721 : Nat := 6002550815460422799943

theorem tailTrace_236721 : CollatzResearch.WordTrace tailWord_236721 prefixEnd_236721 6002550815460422799943 := by
  unfold tailWord_236721
  simp only [CollatzResearch.WordTrace]
  refine ⟨8633924175407720573214017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5755949450271813715476011 8633924175407720573214017)
  ·
    refine ⟨6475443131555790429910513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8633924175407720573214017 6475443131555790429910513)
    ·
      refine ⟨4856582348666842822432885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6475443131555790429910513 4856582348666842822432885)
      ·
        refine ⟨455304595187516514603083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4856582348666842822432885 455304595187516514603083)
        ·
          refine ⟨682956892781274771904625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455304595187516514603083 682956892781274771904625)
          ·
            refine ⟨512217669585956078928469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682956892781274771904625 512217669585956078928469)
            ·
              refine ⟨6002550815460422799943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 512217669585956078928469 6002550815460422799943)
              ·
                rfl

theorem cell21_236721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 8].length) (baseStart_236721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236721 prefixEnd_236721 := by exact prefixLift 236721
  have htrace : WordTrace (prefixWord ++ tailWord_236721) baseStart_236721 baseEnd_236721 := by
    simpa [prefixWord, tailWord_236721, baseEnd_236721] using wordTrace_append hprefix tailTrace_236721
  have hstable : (prefixWord ++ tailWord_236721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236721).length < 2 ^ (prefixWord ++ tailWord_236721).sum := by decide
  have hdescent : baseEnd_236721 < baseStart_236721 := by decide
  rcases family_descends (prefixWord ++ tailWord_236721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236735 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 5]
def baseStart_236735 : Nat := 118140960795 + 236735 * 2 ^ 59
def prefixEnd_236735 : Nat := 4983230072969 + 3 ^ 40 * 236735 * 2
def baseEnd_236735 : Nat := 54026152329882891966125

theorem tailTrace_236735 : CollatzResearch.WordTrace tailWord_236735 prefixEnd_236735 54026152329882891966125 := by
  unfold tailWord_236735
  simp only [CollatzResearch.WordTrace]
  refine ⟨8634434797357000964223659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5756289864904667309482439 8634434797357000964223659)
  ·
    refine ⟨12951652196035501446335489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8634434797357000964223659 12951652196035501446335489)
    ·
      refine ⟨9713739147026626084751617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12951652196035501446335489 9713739147026626084751617)
      ·
        refine ⟨7285304360269969563563713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9713739147026626084751617 7285304360269969563563713)
        ·
          refine ⟨5463978270202477172672785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7285304360269969563563713 5463978270202477172672785)
          ·
            refine ⟨4097983702651857879504589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5463978270202477172672785 4097983702651857879504589)
            ·
              refine ⟨1536743888494446704814221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4097983702651857879504589 1536743888494446704814221)
              ·
                refine ⟨576278958185417514305333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1536743888494446704814221 576278958185417514305333)
                ·
                  refine ⟨54026152329882891966125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 576278958185417514305333 54026152329882891966125)
                  ·
                    rfl

theorem cell21_236735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_236735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236735 prefixEnd_236735 := by exact prefixLift 236735
  have htrace : WordTrace (prefixWord ++ tailWord_236735) baseStart_236735 baseEnd_236735 := by
    simpa [prefixWord, tailWord_236735, baseEnd_236735] using wordTrace_append hprefix tailTrace_236735
  have hstable : (prefixWord ++ tailWord_236735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236735).length < 2 ^ (prefixWord ++ tailWord_236735).sum := by decide
  have hdescent : baseEnd_236735 < baseStart_236735 := by decide
  rcases family_descends (prefixWord ++ tailWord_236735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236769 : List Nat := [1, 2, 3, 1, 3, 2, 3, 3, 3]
def baseStart_236769 : Nat := 118140960795 + 236769 * 2 ^ 59
def prefixEnd_236769 : Nat := 4983230072969 + 3 ^ 40 * 236769 * 2
def baseEnd_236769 : Nat := 54033911593106388399389

theorem tailTrace_236769 : CollatzResearch.WordTrace tailWord_236769 prefixEnd_236769 54033911593106388399389 := by
  unfold tailWord_236769
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635674879233824770961361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5757116586155883180640907 8635674879233824770961361)
  ·
    refine ⟨6476756159425368578221021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8635674879233824770961361 6476756159425368578221021)
    ·
      refine ⟨2428783559784513216832883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6476756159425368578221021 2428783559784513216832883)
      ·
        refine ⟨3643175339676769825249325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428783559784513216832883 3643175339676769825249325)
        ·
          refine ⟨1366190752378788684468497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3643175339676769825249325 1366190752378788684468497)
          ·
            refine ⟨1024643064284091513351373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1366190752378788684468497 1024643064284091513351373)
            ·
              refine ⟨384241149106534317506765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1024643064284091513351373 384241149106534317506765)
              ·
                refine ⟨144090430914950369065037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384241149106534317506765 144090430914950369065037)
                ·
                  refine ⟨54033911593106388399389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144090430914950369065037 54033911593106388399389)
                  ·
                    rfl

theorem cell21_236769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 3].length) (baseStart_236769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236769 prefixEnd_236769 := by exact prefixLift 236769
  have htrace : WordTrace (prefixWord ++ tailWord_236769) baseStart_236769 baseEnd_236769 := by
    simpa [prefixWord, tailWord_236769, baseEnd_236769] using wordTrace_append hprefix tailTrace_236769
  have hstable : (prefixWord ++ tailWord_236769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236769).length < 2 ^ (prefixWord ++ tailWord_236769).sum := by decide
  have hdescent : baseEnd_236769 < baseStart_236769 := by decide
  rcases family_descends (prefixWord ++ tailWord_236769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236780 : List Nat := [2, 2, 1, 1, 2, 4, 9]
def baseStart_236780 : Nat := 118140960795 + 236780 * 2 ^ 59
def prefixEnd_236780 : Nat := 4983230072969 + 3 ^ 40 * 236780 * 2
def baseEnd_236780 : Nat := 6004046882552534857337

theorem tailTrace_236780 : CollatzResearch.WordTrace tailWord_236780 prefixEnd_236780 6004046882552534857337 := by
  unfold tailWord_236780
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318038041096986824805897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5757384054795982433074529 4318038041096986824805897)
  ·
    refine ⟨3238528530822740118604423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4318038041096986824805897 3238528530822740118604423)
    ·
      refine ⟨4857792796234110177906635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3238528530822740118604423 4857792796234110177906635)
      ·
        refine ⟨7286689194351165266859953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4857792796234110177906635 7286689194351165266859953)
        ·
          refine ⟨5465016895763373950144965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7286689194351165266859953 5465016895763373950144965)
          ·
            refine ⟨1024690667955632615652181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5465016895763373950144965 1024690667955632615652181)
            ·
              refine ⟨6004046882552534857337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1024690667955632615652181 6004046882552534857337)
              ·
                rfl

theorem cell21_236780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 9].length) (baseStart_236780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236780 prefixEnd_236780 := by exact prefixLift 236780
  have htrace : WordTrace (prefixWord ++ tailWord_236780) baseStart_236780 baseEnd_236780 := by
    simpa [prefixWord, tailWord_236780, baseEnd_236780] using wordTrace_append hprefix tailTrace_236780
  have hstable : (prefixWord ++ tailWord_236780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236780).length < 2 ^ (prefixWord ++ tailWord_236780).sum := by decide
  have hdescent : baseEnd_236780 < baseStart_236780 := by decide
  rcases family_descends (prefixWord ++ tailWord_236780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236786 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 5]
def baseStart_236786 : Nat := 118140960795 + 236786 * 2 ^ 59
def prefixEnd_236786 : Nat := 4983230072969 + 3 ^ 40 * 236786 * 2
def baseEnd_236786 : Nat := 54037791224718136616021

theorem tailTrace_236786 : CollatzResearch.WordTrace tailWord_236786 prefixEnd_236786 54037791224718136616021 := by
  unfold tailWord_236786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159073730043059168582553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5757529946781491116220141 2159073730043059168582553)
  ·
    refine ⟨1619305297532294376436915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2159073730043059168582553 1619305297532294376436915)
    ·
      refine ⟨2428957946298441564655373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1619305297532294376436915 2428957946298441564655373)
      ·
        refine ⟨910859229861915586745765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2428957946298441564655373 910859229861915586745765)
        ·
          refine ⟨170786105599109172514831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 910859229861915586745765 170786105599109172514831)
          ·
            refine ⟨256179158398663758772247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170786105599109172514831 256179158398663758772247)
            ·
              refine ⟨384268737597995638158371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256179158398663758772247 384268737597995638158371)
              ·
                refine ⟨576403106396993457237557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384268737597995638158371 576403106396993457237557)
                ·
                  refine ⟨54037791224718136616021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 576403106396993457237557 54037791224718136616021)
                  ·
                    rfl

theorem cell21_236786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_236786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236786 prefixEnd_236786 := by exact prefixLift 236786
  have htrace : WordTrace (prefixWord ++ tailWord_236786) baseStart_236786 baseEnd_236786 := by
    simpa [prefixWord, tailWord_236786, baseEnd_236786] using wordTrace_append hprefix tailTrace_236786
  have hstable : (prefixWord ++ tailWord_236786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236786).length < 2 ^ (prefixWord ++ tailWord_236786).sum := by decide
  have hdescent : baseEnd_236786 < baseStart_236786 := by decide
  rcases family_descends (prefixWord ++ tailWord_236786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236893 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 6]
def baseStart_236893 : Nat := 118140960795 + 236893 * 2 ^ 59
def prefixEnd_236893 : Nat := 4983230072969 + 3 ^ 40 * 236893 * 2
def baseEnd_236893 : Nat := 54062210082509728332469

theorem tailTrace_236893 : CollatzResearch.WordTrace tailWord_236893 prefixEnd_236893 54062210082509728332469 := by
  unfold tailWord_236893
  simp only [CollatzResearch.WordTrace]
  refine ⟨8640197530784593948475333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5760131687189729298983555 8640197530784593948475333)
  ·
    refine ⟨1620037037022111365339125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8640197530784593948475333 1620037037022111365339125)
    ·
      refine ⟨151878472220822940500543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1620037037022111365339125 151878472220822940500543)
      ·
        refine ⟨227817708331234410750815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151878472220822940500543 227817708331234410750815)
        ·
          refine ⟨341726562496851616126223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227817708331234410750815 341726562496851616126223)
          ·
            refine ⟨512589843745277424189335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341726562496851616126223 512589843745277424189335)
            ·
              refine ⟨768884765617916136284003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512589843745277424189335 768884765617916136284003)
              ·
                refine ⟨1153327148426874204426005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768884765617916136284003 1153327148426874204426005)
                ·
                  refine ⟨54062210082509728332469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1153327148426874204426005 54062210082509728332469)
                  ·
                    rfl

theorem cell21_236893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_236893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_236893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_236893 prefixEnd_236893 := by exact prefixLift 236893
  have htrace : WordTrace (prefixWord ++ tailWord_236893) baseStart_236893 baseEnd_236893 := by
    simpa [prefixWord, tailWord_236893, baseEnd_236893] using wordTrace_append hprefix tailTrace_236893
  have hstable : (prefixWord ++ tailWord_236893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236893).length < 2 ^ (prefixWord ++ tailWord_236893).sum := by decide
  have hdescent : baseEnd_236893 < baseStart_236893 := by decide
  rcases family_descends (prefixWord ++ tailWord_236893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237014 : List Nat := [5, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_237014 : Nat := 118140960795 + 237014 * 2 ^ 59
def prefixEnd_237014 : Nat := 4983230072969 + 3 ^ 40 * 237014 * 2
def baseEnd_237014 : Nat := 54089823931040406815555

theorem tailTrace_237014 : CollatzResearch.WordTrace tailWord_237014 prefixEnd_237014 54089823931040406815555 := by
  unfold tailWord_237014
  simp only [CollatzResearch.WordTrace]
  refine ⟨540288172709139475851881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5763073842230821075753397 540288172709139475851881)
  ·
    refine ⟨405216129531854606888911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 540288172709139475851881 405216129531854606888911)
    ·
      refine ⟨607824194297781910333367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405216129531854606888911 607824194297781910333367)
      ·
        refine ⟨911736291446672865500051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607824194297781910333367 911736291446672865500051)
        ·
          refine ⟨1367604437170009298250077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911736291446672865500051 1367604437170009298250077)
          ·
            refine ⟨512851663938753486843779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1367604437170009298250077 512851663938753486843779)
            ·
              refine ⟨769277495908130230265669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512851663938753486843779 769277495908130230265669)
              ·
                refine ⟨144239530482774418174813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 769277495908130230265669 144239530482774418174813)
                ·
                  refine ⟨54089823931040406815555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144239530482774418174813 54089823931040406815555)
                  ·
                    rfl

theorem cell21_237014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_237014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237014 prefixEnd_237014 := by exact prefixLift 237014
  have htrace : WordTrace (prefixWord ++ tailWord_237014) baseStart_237014 baseEnd_237014 := by
    simpa [prefixWord, tailWord_237014, baseEnd_237014] using wordTrace_append hprefix tailTrace_237014
  have hstable : (prefixWord ++ tailWord_237014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237014).length < 2 ^ (prefixWord ++ tailWord_237014).sum := by decide
  have hdescent : baseEnd_237014 < baseStart_237014 := by decide
  rcases family_descends (prefixWord ++ tailWord_237014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237025 : List Nat := [1, 2, 3, 1, 2, 5, 1, 6]
def baseStart_237025 : Nat := 118140960795 + 237025 * 2 ^ 59
def prefixEnd_237025 : Nat := 4983230072969 + 3 ^ 40 * 237025 * 2
def baseEnd_237025 : Nat := 18030778093635610710733

theorem tailTrace_237025 : CollatzResearch.WordTrace tailWord_237025 prefixEnd_237025 18030778093635610710733 := by
  unfold tailWord_237025
  simp only [CollatzResearch.WordTrace]
  refine ⟨8645011966306380492280529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5763341310870920328187019 8645011966306380492280529)
  ·
    refine ⟨6483758974729785369210397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8645011966306380492280529 6483758974729785369210397)
    ·
      refine ⟨2431409615523669513453899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6483758974729785369210397 2431409615523669513453899)
      ·
        refine ⟨3647114423285504270180849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431409615523669513453899 3647114423285504270180849)
        ·
          refine ⟨2735335817464128202635637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3647114423285504270180849 2735335817464128202635637)
          ·
            refine ⟨256437732887262018997091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2735335817464128202635637 256437732887262018997091)
            ·
              refine ⟨384656599330893028495637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256437732887262018997091 384656599330893028495637)
              ·
                refine ⟨18030778093635610710733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 384656599330893028495637 18030778093635610710733)
                ·
                  rfl

theorem cell21_237025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 6].length) (baseStart_237025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237025 prefixEnd_237025 := by exact prefixLift 237025
  have htrace : WordTrace (prefixWord ++ tailWord_237025) baseStart_237025 baseEnd_237025 := by
    simpa [prefixWord, tailWord_237025, baseEnd_237025] using wordTrace_append hprefix tailTrace_237025
  have hstable : (prefixWord ++ tailWord_237025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237025).length < 2 ^ (prefixWord ++ tailWord_237025).sum := by decide
  have hdescent : baseEnd_237025 < baseStart_237025 := by decide
  rcases family_descends (prefixWord ++ tailWord_237025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237042 : List Nat := [3, 2, 1, 4, 1, 2, 3, 5]
def baseStart_237042 : Nat := 118140960795 + 237042 * 2 ^ 59
def prefixEnd_237042 : Nat := 4983230072969 + 3 ^ 40 * 237042 * 2
def baseEnd_237042 : Nat := 18032071304172860116277

theorem tailTrace_237042 : CollatzResearch.WordTrace tailWord_237042 prefixEnd_237042 18032071304172860116277 := by
  unfold tailWord_237042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2161408001811198098912345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5763754671496528263766253 2161408001811198098912345)
  ·
    refine ⟨1621056001358398574184259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2161408001811198098912345 1621056001358398574184259)
    ·
      refine ⟨2431584002037597861276389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1621056001358398574184259 2431584002037597861276389)
      ·
        refine ⟨455922000382049598989323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2431584002037597861276389 455922000382049598989323)
        ·
          refine ⟨683883000573074398483985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455922000382049598989323 683883000573074398483985)
          ·
            refine ⟨512912250429805798862989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 683883000573074398483985 512912250429805798862989)
            ·
              refine ⟨192342093911177174573621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512912250429805798862989 192342093911177174573621)
              ·
                refine ⟨18032071304172860116277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192342093911177174573621 18032071304172860116277)
                ·
                  rfl

theorem cell21_237042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_237042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237042 prefixEnd_237042 := by exact prefixLift 237042
  have htrace : WordTrace (prefixWord ++ tailWord_237042) baseStart_237042 baseEnd_237042 := by
    simpa [prefixWord, tailWord_237042, baseEnd_237042] using wordTrace_append hprefix tailTrace_237042
  have hstable : (prefixWord ++ tailWord_237042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237042).length < 2 ^ (prefixWord ++ tailWord_237042).sum := by decide
  have hdescent : baseEnd_237042 < baseStart_237042 := by decide
  rcases family_descends (prefixWord ++ tailWord_237042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237084 : List Nat := [2, 2, 3, 1, 2, 1, 2, 8]
def baseStart_237084 : Nat := 118140960795 + 237084 * 2 ^ 59
def prefixEnd_237084 : Nat := 4983230072969 + 3 ^ 40 * 237084 * 2
def baseEnd_237084 : Nat := 18035266294911946882915

theorem tailTrace_237084 : CollatzResearch.WordTrace tailWord_237084 prefixEnd_237084 18035266294911946882915 := by
  unfold tailWord_237084
  simp only [CollatzResearch.WordTrace]
  refine ⟨4323581936546316784339153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5764775915395089045785537 4323581936546316784339153)
  ·
    refine ⟨3242686452409737588254365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4323581936546316784339153 3242686452409737588254365)
    ·
      refine ⟨1216007419653651595595387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3242686452409737588254365 1216007419653651595595387)
      ·
        refine ⟨1824011129480477393393081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216007419653651595595387 1824011129480477393393081)
        ·
          refine ⟨1368008347110358045044811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1824011129480477393393081 1368008347110358045044811)
          ·
            refine ⟨2052012520665537067567217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368008347110358045044811 2052012520665537067567217)
            ·
              refine ⟨1539009390499152800675413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2052012520665537067567217 1539009390499152800675413)
              ·
                refine ⟨18035266294911946882915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1539009390499152800675413 18035266294911946882915)
                ·
                  rfl

theorem cell21_237084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_237084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237084 prefixEnd_237084 := by exact prefixLift 237084
  have htrace : WordTrace (prefixWord ++ tailWord_237084) baseStart_237084 baseEnd_237084 := by
    simpa [prefixWord, tailWord_237084, baseEnd_237084] using wordTrace_append hprefix tailTrace_237084
  have hstable : (prefixWord ++ tailWord_237084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237084).length < 2 ^ (prefixWord ++ tailWord_237084).sum := by decide
  have hdescent : baseEnd_237084 < baseStart_237084 := by decide
  rcases family_descends (prefixWord ++ tailWord_237084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237132 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 5]
def baseStart_237132 : Nat := 118140960795 + 237132 * 2 ^ 59
def prefixEnd_237132 : Nat := 4983230072969 + 3 ^ 40 * 237132 * 2
def baseEnd_237132 : Nat := 54116753138698423848647

theorem tailTrace_237132 : CollatzResearch.WordTrace tailWord_237132 prefixEnd_237132 54116753138698423848647 := by
  unfold tailWord_237132
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324457288459368883212825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5765943051279158510950433 4324457288459368883212825)
  ·
    refine ⟨3243342966344526662409619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4324457288459368883212825 3243342966344526662409619)
    ·
      refine ⟨4865014449516789993614429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3243342966344526662409619 4865014449516789993614429)
      ·
        refine ⟨1824380418568796247605411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4865014449516789993614429 1824380418568796247605411)
        ·
          refine ⟨2736570627853194371408117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824380418568796247605411 2736570627853194371408117)
          ·
            refine ⟨256553496361236972319511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2736570627853194371408117 256553496361236972319511)
            ·
              refine ⟨384830244541855458479267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256553496361236972319511 384830244541855458479267)
              ·
                refine ⟨577245366812783187718901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384830244541855458479267 577245366812783187718901)
                ·
                  refine ⟨54116753138698423848647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 577245366812783187718901 54116753138698423848647)
                  ·
                    rfl

theorem cell21_237132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_237132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237132 prefixEnd_237132 := by exact prefixLift 237132
  have htrace : WordTrace (prefixWord ++ tailWord_237132) baseStart_237132 baseEnd_237132 := by
    simpa [prefixWord, tailWord_237132, baseEnd_237132] using wordTrace_append hprefix tailTrace_237132
  have hstable : (prefixWord ++ tailWord_237132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237132).length < 2 ^ (prefixWord ++ tailWord_237132).sum := by decide
  have hdescent : baseEnd_237132 < baseStart_237132 := by decide
  rcases family_descends (prefixWord ++ tailWord_237132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237239 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 4]
def baseStart_237239 : Nat := 118140960795 + 237239 * 2 ^ 59
def prefixEnd_237239 : Nat := 4983230072969 + 3 ^ 40 * 237239 * 2
def baseEnd_237239 : Nat := 54141171996490015565095

theorem tailTrace_237239 : CollatzResearch.WordTrace tailWord_237239 prefixEnd_237239 54141171996490015565095 := by
  unfold tailWord_237239
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652817187531095040570771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5768544791687396693713847 8652817187531095040570771)
  ·
    refine ⟨12979225781296642560856157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8652817187531095040570771 12979225781296642560856157)
    ·
      refine ⟨4867209667986240960321059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12979225781296642560856157 4867209667986240960321059)
      ·
        refine ⟨7300814501979361440481589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867209667986240960321059 7300814501979361440481589)
        ·
          refine ⟨684451359560565135045149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7300814501979361440481589 684451359560565135045149)
          ·
            refine ⟨256669259835211925641931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 684451359560565135045149 256669259835211925641931)
            ·
              refine ⟨385003889752817888462897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256669259835211925641931 385003889752817888462897)
              ·
                refine ⟨288752917314613416347173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385003889752817888462897 288752917314613416347173)
                ·
                  refine ⟨54141171996490015565095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288752917314613416347173 54141171996490015565095)
                  ·
                    rfl

theorem cell21_237239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 4].length) (baseStart_237239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237239 prefixEnd_237239 := by exact prefixLift 237239
  have htrace : WordTrace (prefixWord ++ tailWord_237239) baseStart_237239 baseEnd_237239 := by
    simpa [prefixWord, tailWord_237239, baseEnd_237239] using wordTrace_append hprefix tailTrace_237239
  have hstable : (prefixWord ++ tailWord_237239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237239).length < 2 ^ (prefixWord ++ tailWord_237239).sum := by decide
  have hdescent : baseEnd_237239 < baseStart_237239 := by decide
  rcases family_descends (prefixWord ++ tailWord_237239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237298 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_237298 : Nat := 118140960795 + 237298 * 2 ^ 59
def prefixEnd_237298 : Nat := 4983230072969 + 3 ^ 40 * 237298 * 2
def baseEnd_237298 : Nat := 54154636600319024081641

theorem tailTrace_237298 : CollatzResearch.WordTrace tailWord_237298 prefixEnd_237298 54154636600319024081641 := by
  unfold tailWord_237298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163742273579337029242137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5769979396211565411312365 2163742273579337029242137)
  ·
    refine ⟨1622806705184502771931603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2163742273579337029242137 1622806705184502771931603)
    ·
      refine ⟨2434210057776754157897405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1622806705184502771931603 2434210057776754157897405)
      ·
        refine ⟨912828771666282809211527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2434210057776754157897405 912828771666282809211527)
        ·
          refine ⟨1369243157499424213817291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912828771666282809211527 1369243157499424213817291)
          ·
            refine ⟨2053864736249136320725937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369243157499424213817291 2053864736249136320725937)
            ·
              refine ⟨1540398552186852240544453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053864736249136320725937 1540398552186852240544453)
              ·
                refine ⟨288824728535034795102085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1540398552186852240544453 288824728535034795102085)
                ·
                  refine ⟨54154636600319024081641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 288824728535034795102085 54154636600319024081641)
                  ·
                    rfl

theorem cell21_237298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_237298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237298 prefixEnd_237298 := by exact prefixLift 237298
  have htrace : WordTrace (prefixWord ++ tailWord_237298) baseStart_237298 baseEnd_237298 := by
    simpa [prefixWord, tailWord_237298, baseEnd_237298] using wordTrace_append hprefix tailTrace_237298
  have hstable : (prefixWord ++ tailWord_237298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237298).length < 2 ^ (prefixWord ++ tailWord_237298).sum := by decide
  have hdescent : baseEnd_237298 < baseStart_237298 := by decide
  rcases family_descends (prefixWord ++ tailWord_237298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237402 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_237402 : Nat := 118140960795 + 237402 * 2 ^ 59
def prefixEnd_237402 : Nat := 4983230072969 + 3 ^ 40 * 237402 * 2
def baseEnd_237402 : Nat := 54178370817237954348095

theorem tailTrace_237402 : CollatzResearch.WordTrace tailWord_237402 prefixEnd_237402 54178370817237954348095 := by
  unfold tailWord_237402
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164690571485143469688615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5772508190627049252502973 2164690571485143469688615)
  ·
    refine ⟨3247035857227715204532923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2164690571485143469688615 3247035857227715204532923)
    ·
      refine ⟨4870553785841572806799385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3247035857227715204532923 4870553785841572806799385)
      ·
        refine ⟨3652915339381179605099539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4870553785841572806799385 3652915339381179605099539)
        ·
          refine ⟨5479373009071769407649309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652915339381179605099539 5479373009071769407649309)
          ·
            refine ⟨2054764878401913527868491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5479373009071769407649309 2054764878401913527868491)
            ·
              refine ⟨3082147317602870291802737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054764878401913527868491 3082147317602870291802737)
              ·
                refine ⟨2311610488202152718852053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3082147317602870291802737 2311610488202152718852053)
                ·
                  refine ⟨54178370817237954348095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2311610488202152718852053 54178370817237954348095)
                  ·
                    rfl

theorem cell21_237402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_237402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237402 prefixEnd_237402 := by exact prefixLift 237402
  have htrace : WordTrace (prefixWord ++ tailWord_237402) baseStart_237402 baseEnd_237402 := by
    simpa [prefixWord, tailWord_237402, baseEnd_237402] using wordTrace_append hprefix tailTrace_237402
  have hstable : (prefixWord ++ tailWord_237402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237402).length < 2 ^ (prefixWord ++ tailWord_237402).sum := by decide
  have hdescent : baseEnd_237402 < baseStart_237402 := by decide
  rcases family_descends (prefixWord ++ tailWord_237402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237470 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_237470 : Nat := 118140960795 + 237470 * 2 ^ 59
def prefixEnd_237470 : Nat := 4983230072969 + 3 ^ 40 * 237470 * 2
def baseEnd_237470 : Nat := 54193889343684947214623

theorem tailTrace_237470 : CollatzResearch.WordTrace tailWord_237470 prefixEnd_237470 54193889343684947214623 := by
  unfold tailWord_237470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082655306211777686528733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5774161633129480994819909 1082655306211777686528733)
  ·
    refine ⟨405995739829416632448275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1082655306211777686528733 405995739829416632448275)
    ·
      refine ⟨608993609744124948672413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405995739829416632448275 608993609744124948672413)
      ·
        refine ⟨228372603654046855752155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 608993609744124948672413 228372603654046855752155)
        ·
          refine ⟨342558905481070283628233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228372603654046855752155 342558905481070283628233)
          ·
            refine ⟨256919179110802712721175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342558905481070283628233 256919179110802712721175)
            ·
              refine ⟨385378768666204069081763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256919179110802712721175 385378768666204069081763)
              ·
                refine ⟨578068152999306103622645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385378768666204069081763 578068152999306103622645)
                ·
                  refine ⟨54193889343684947214623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 578068152999306103622645 54193889343684947214623)
                  ·
                    rfl

theorem cell21_237470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_237470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237470 prefixEnd_237470 := by exact prefixLift 237470
  have htrace : WordTrace (prefixWord ++ tailWord_237470) baseStart_237470 baseEnd_237470 := by
    simpa [prefixWord, tailWord_237470, baseEnd_237470] using wordTrace_append hprefix tailTrace_237470
  have hstable : (prefixWord ++ tailWord_237470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237470).length < 2 ^ (prefixWord ++ tailWord_237470).sum := by decide
  have hdescent : baseEnd_237470 < baseStart_237470 := by decide
  rcases family_descends (prefixWord ++ tailWord_237470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237532 : List Nat := [2, 2, 6, 1, 2, 1, 1, 6]
def baseStart_237532 : Nat := 118140960795 + 237532 * 2 ^ 59
def prefixEnd_237532 : Nat := 4983230072969 + 3 ^ 40 * 237532 * 2
def baseEnd_237532 : Nat := 18069346196128872393721

theorem tailTrace_237532 : CollatzResearch.WordTrace tailWord_237532 prefixEnd_237532 18069346196128872393721 := by
  unfold tailWord_237532
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331751887734803040493425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5775669183646404053991233 4331751887734803040493425)
  ·
    refine ⟨3248813915801102280370069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4331751887734803040493425 3248813915801102280370069)
    ·
      refine ⟨152288152303176669392347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3248813915801102280370069 152288152303176669392347)
      ·
        refine ⟨228432228454765004088521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152288152303176669392347 228432228454765004088521)
        ·
          refine ⟨171324171341073753066391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228432228454765004088521 171324171341073753066391)
          ·
            refine ⟨256986257011610629599587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171324171341073753066391 256986257011610629599587)
            ·
              refine ⟨385479385517415944399381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256986257011610629599587 385479385517415944399381)
              ·
                refine ⟨18069346196128872393721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385479385517415944399381 18069346196128872393721)
                ·
                  rfl

theorem cell21_237532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 6].length) (baseStart_237532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237532 prefixEnd_237532 := by exact prefixLift 237532
  have htrace : WordTrace (prefixWord ++ tailWord_237532) baseStart_237532 baseEnd_237532 := by
    simpa [prefixWord, tailWord_237532, baseEnd_237532] using wordTrace_append hprefix tailTrace_237532
  have hstable : (prefixWord ++ tailWord_237532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237532).length < 2 ^ (prefixWord ++ tailWord_237532).sum := by decide
  have hdescent : baseEnd_237532 < baseStart_237532 := by decide
  rcases family_descends (prefixWord ++ tailWord_237532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237599 : List Nat := [1, 1, 2, 4, 1, 2, 2, 8]
def baseStart_237599 : Nat := 118140960795 + 237599 * 2 ^ 59
def prefixEnd_237599 : Nat := 4983230072969 + 3 ^ 40 * 237599 * 2
def baseEnd_237599 : Nat := 18074442967069796521453

theorem tailTrace_237599 : CollatzResearch.WordTrace tailWord_237599 prefixEnd_237599 18074442967069796521453 := by
  unfold tailWord_237599
  simp only [CollatzResearch.WordTrace]
  refine ⟨8665947466226876523675851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5777298310817917682450567 8665947466226876523675851)
  ·
    refine ⟨12998921199340314785513777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8665947466226876523675851 12998921199340314785513777)
    ·
      refine ⟨9749190899505236089135333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12998921199340314785513777 9749190899505236089135333)
      ·
        refine ⟨1827973293657231766712875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9749190899505236089135333 1827973293657231766712875)
        ·
          refine ⟨2741959940485847650069313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827973293657231766712875 2741959940485847650069313)
          ·
            refine ⟨2056469955364385737551985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2741959940485847650069313 2056469955364385737551985)
            ·
              refine ⟨1542352466523289303163989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056469955364385737551985 1542352466523289303163989)
              ·
                refine ⟨18074442967069796521453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1542352466523289303163989 18074442967069796521453)
                ·
                  rfl

theorem cell21_237599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 8].length) (baseStart_237599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237599 prefixEnd_237599 := by exact prefixLift 237599
  have htrace : WordTrace (prefixWord ++ tailWord_237599) baseStart_237599 baseEnd_237599 := by
    simpa [prefixWord, tailWord_237599, baseEnd_237599] using wordTrace_append hprefix tailTrace_237599
  have hstable : (prefixWord ++ tailWord_237599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237599).length < 2 ^ (prefixWord ++ tailWord_237599).sum := by decide
  have hdescent : baseEnd_237599 < baseStart_237599 := by decide
  rcases family_descends (prefixWord ++ tailWord_237599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237616 : List Nat := [2, 1, 1, 1, 2, 5, 4, 5]
def baseStart_237616 : Nat := 118140960795 + 237616 * 2 ^ 59
def prefixEnd_237616 : Nat := 4983230072969 + 3 ^ 40 * 237616 * 2
def baseEnd_237616 : Nat := 18075736177607045926997

theorem tailTrace_237616 : CollatzResearch.WordTrace tailWord_237616 prefixEnd_237616 18075736177607045926997 := by
  unfold tailWord_237616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333283753582644213522351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5777711671443525618029801 4333283753582644213522351)
  ·
    refine ⟨6499925630373966320283527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4333283753582644213522351 6499925630373966320283527)
    ·
      refine ⟨9749888445560949480425291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6499925630373966320283527 9749888445560949480425291)
      ·
        refine ⟨14624832668341424220637937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9749888445560949480425291 14624832668341424220637937)
        ·
          refine ⟨10968624501256068165478453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14624832668341424220637937 10968624501256068165478453)
          ·
            refine ⟨1028308546992756390513605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10968624501256068165478453 1028308546992756390513605)
            ·
              refine ⟨192807852561141823221301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1028308546992756390513605 192807852561141823221301)
              ·
                refine ⟨18075736177607045926997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192807852561141823221301 18075736177607045926997)
                ·
                  rfl

theorem cell21_237616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_237616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237616 prefixEnd_237616 := by exact prefixLift 237616
  have htrace : WordTrace (prefixWord ++ tailWord_237616) baseStart_237616 baseEnd_237616 := by
    simpa [prefixWord, tailWord_237616, baseEnd_237616] using wordTrace_append hprefix tailTrace_237616
  have hstable : (prefixWord ++ tailWord_237616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237616).length < 2 ^ (prefixWord ++ tailWord_237616).sum := by decide
  have hdescent : baseEnd_237616 < baseStart_237616 := by decide
  rcases family_descends (prefixWord ++ tailWord_237616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237726 : List Nat := [4, 3, 1, 1, 3, 1, 3, 5]
def baseStart_237726 : Nat := 118140960795 + 237726 * 2 ^ 59
def prefixEnd_237726 : Nat := 4983230072969 + 3 ^ 40 * 237726 * 2
def baseEnd_237726 : Nat := 18084104010495130315811

theorem tailTrace_237726 : CollatzResearch.WordTrace tailWord_237726 prefixEnd_237726 18084104010495130315811 := by
  unfold tailWord_237726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1083822442095847151693629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5780386357844518142366021 1083822442095847151693629)
  ·
    refine ⟨406433415785942681885111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1083822442095847151693629 406433415785942681885111)
    ·
      refine ⟨609650123678914022827667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406433415785942681885111 609650123678914022827667)
      ·
        refine ⟨914475185518371034241501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609650123678914022827667 914475185518371034241501)
        ·
          refine ⟨342928194569389137840563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 914475185518371034241501 342928194569389137840563)
          ·
            refine ⟨514392291854083706760845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342928194569389137840563 514392291854083706760845)
            ·
              refine ⟨192897109445281390035317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 514392291854083706760845 192897109445281390035317)
              ·
                refine ⟨18084104010495130315811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192897109445281390035317 18084104010495130315811)
                ·
                  rfl

theorem cell21_237726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_237726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237726 prefixEnd_237726 := by exact prefixLift 237726
  have htrace : WordTrace (prefixWord ++ tailWord_237726) baseStart_237726 baseEnd_237726 := by
    simpa [prefixWord, tailWord_237726, baseEnd_237726] using wordTrace_append hprefix tailTrace_237726
  have hstable : (prefixWord ++ tailWord_237726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237726).length < 2 ^ (prefixWord ++ tailWord_237726).sum := by decide
  have hdescent : baseEnd_237726 < baseStart_237726 := by decide
  rcases family_descends (prefixWord ++ tailWord_237726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237751 : List Nat := [1, 1, 3, 1, 4, 3, 8]
def baseStart_237751 : Nat := 118140960795 + 237751 * 2 ^ 59
def prefixEnd_237751 : Nat := 4983230072969 + 3 ^ 40 * 237751 * 2
def baseEnd_237751 : Nat := 6028668596898989225635

theorem tailTrace_237751 : CollatzResearch.WordTrace tailWord_237751 prefixEnd_237751 6028668596898989225635 := by
  unfold tailWord_237751
  simp only [CollatzResearch.WordTrace]
  refine ⟨8671491361676206483209107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5780994241117470988806071 8671491361676206483209107)
  ·
    refine ⟨13007237042514309724813661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8671491361676206483209107 13007237042514309724813661)
    ·
      refine ⟨4877713890942866146805123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13007237042514309724813661 4877713890942866146805123)
      ·
        refine ⟨7316570836414299220207685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4877713890942866146805123 7316570836414299220207685)
        ·
          refine ⟨1371857031827681103788941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7316570836414299220207685 1371857031827681103788941)
          ·
            refine ⟨514446386935380413920853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1371857031827681103788941 514446386935380413920853)
            ·
              refine ⟨6028668596898989225635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 514446386935380413920853 6028668596898989225635)
              ·
                rfl

theorem cell21_237751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 8].length) (baseStart_237751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237751 prefixEnd_237751 := by exact prefixLift 237751
  have htrace : WordTrace (prefixWord ++ tailWord_237751) baseStart_237751 baseEnd_237751 := by
    simpa [prefixWord, tailWord_237751, baseEnd_237751] using wordTrace_append hprefix tailTrace_237751
  have hstable : (prefixWord ++ tailWord_237751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237751).length < 2 ^ (prefixWord ++ tailWord_237751).sum := by decide
  have hdescent : baseEnd_237751 < baseStart_237751 := by decide
  rcases family_descends (prefixWord ++ tailWord_237751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237827 : List Nat := [1, 1, 1, 3, 2, 3, 4, 6]
def baseStart_237827 : Nat := 118140960795 + 237827 * 2 ^ 59
def prefixEnd_237827 : Nat := 4983230072969 + 3 ^ 40 * 237827 * 2
def baseEnd_237827 : Nat := 18091787202510553254631

theorem tailTrace_237827 : CollatzResearch.WordTrace tailWord_237827 prefixEnd_237827 18091787202510553254631 := by
  unfold tailWord_237827
  simp only [CollatzResearch.WordTrace]
  refine ⟨8674263309400871462975735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5782842206267247641983823 8674263309400871462975735)
  ·
    refine ⟨13011394964101307194463603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8674263309400871462975735 13011394964101307194463603)
    ·
      refine ⟨19517092446151960791695405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13011394964101307194463603 19517092446151960791695405)
      ·
        refine ⟨7318909667306985296885777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19517092446151960791695405 7318909667306985296885777)
        ·
          refine ⟨5489182250480238972664333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7318909667306985296885777 5489182250480238972664333)
          ·
            refine ⟨2058443343930089614749125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5489182250480238972664333 2058443343930089614749125)
            ·
              refine ⟨385958126986891802765461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2058443343930089614749125 385958126986891802765461)
              ·
                refine ⟨18091787202510553254631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385958126986891802765461 18091787202510553254631)
                ·
                  rfl

theorem cell21_237827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 6].length) (baseStart_237827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237827 prefixEnd_237827 := by exact prefixLift 237827
  have htrace : WordTrace (prefixWord ++ tailWord_237827) baseStart_237827 baseEnd_237827 := by
    simpa [prefixWord, tailWord_237827, baseEnd_237827] using wordTrace_append hprefix tailTrace_237827
  have hstable : (prefixWord ++ tailWord_237827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237827).length < 2 ^ (prefixWord ++ tailWord_237827).sum := by decide
  have hdescent : baseEnd_237827 < baseStart_237827 := by decide
  rcases family_descends (prefixWord ++ tailWord_237827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237875 : List Nat := [1, 1, 1, 2, 5, 1, 3, 4, 3]
def baseStart_237875 : Nat := 118140960795 + 237875 * 2 ^ 59
def prefixEnd_237875 : Nat := 4983230072969 + 3 ^ 40 * 237875 * 2
def baseEnd_237875 : Nat := 54286315861494242963795

theorem tailTrace_237875 : CollatzResearch.WordTrace tailWord_237875 prefixEnd_237875 54286315861494242963795 := by
  unfold tailWord_237875
  simp only [CollatzResearch.WordTrace]
  refine ⟨8676014013226975660723079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5784009342151317107148719 8676014013226975660723079)
  ·
    refine ⟨13014021019840463491084619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8676014013226975660723079 13014021019840463491084619)
    ·
      refine ⟨19521031529760695236626929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13014021019840463491084619 19521031529760695236626929)
      ·
        refine ⟨14640773647320521427470197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19521031529760695236626929 14640773647320521427470197)
        ·
          refine ⟨1372572529436298883825331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14640773647320521427470197 1372572529436298883825331)
          ·
            refine ⟨2058858794154448325737997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372572529436298883825331 2058858794154448325737997)
            ·
              refine ⟨772072047807918122151749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2058858794154448325737997 772072047807918122151749)
              ·
                refine ⟨144763508963984647903453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772072047807918122151749 144763508963984647903453)
                ·
                  refine ⟨54286315861494242963795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144763508963984647903453 54286315861494242963795)
                  ·
                    rfl

theorem cell21_237875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 3].length) (baseStart_237875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237875 prefixEnd_237875 := by exact prefixLift 237875
  have htrace : WordTrace (prefixWord ++ tailWord_237875) baseStart_237875 baseEnd_237875 := by
    simpa [prefixWord, tailWord_237875, baseEnd_237875] using wordTrace_append hprefix tailTrace_237875
  have hstable : (prefixWord ++ tailWord_237875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237875).length < 2 ^ (prefixWord ++ tailWord_237875).sum := by decide
  have hdescent : baseEnd_237875 < baseStart_237875 := by decide
  rcases family_descends (prefixWord ++ tailWord_237875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237892 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 5]
def baseStart_237892 : Nat := 118140960795 + 237892 * 2 ^ 59
def prefixEnd_237892 : Nat := 4983230072969 + 3 ^ 40 * 237892 * 2
def baseEnd_237892 : Nat := 54290195493105991180427

theorem tailTrace_237892 : CollatzResearch.WordTrace tailWord_237892 prefixEnd_237892 54290195493105991180427 := by
  unfold tailWord_237892
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338317027082693782045965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5784422702776925042727953 4338317027082693782045965)
  ·
    refine ⟨1626868885156010168267237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4338317027082693782045965 1626868885156010168267237)
    ·
      refine ⟨305037915966751906550107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1626868885156010168267237 305037915966751906550107)
      ·
        refine ⟨457556873950127859825161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305037915966751906550107 457556873950127859825161)
        ·
          refine ⟨343167655462595894868871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457556873950127859825161 343167655462595894868871)
          ·
            refine ⟨514751483193893842303307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343167655462595894868871 514751483193893842303307)
            ·
              refine ⟨772127224790840763454961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514751483193893842303307 772127224790840763454961)
              ·
                refine ⟨579095418593130572591221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772127224790840763454961 579095418593130572591221)
                ·
                  refine ⟨54290195493105991180427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 579095418593130572591221 54290195493105991180427)
                  ·
                    rfl

theorem cell21_237892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_237892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237892 prefixEnd_237892 := by exact prefixLift 237892
  have htrace : WordTrace (prefixWord ++ tailWord_237892) baseStart_237892 baseEnd_237892 := by
    simpa [prefixWord, tailWord_237892, baseEnd_237892] using wordTrace_append hprefix tailTrace_237892
  have hstable : (prefixWord ++ tailWord_237892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237892).length < 2 ^ (prefixWord ++ tailWord_237892).sum := by decide
  have hdescent : baseEnd_237892 < baseStart_237892 := by decide
  rcases family_descends (prefixWord ++ tailWord_237892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237982 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_237982 : Nat := 118140960795 + 237982 * 2 ^ 59
def prefixEnd_237982 : Nat := 4983230072969 + 3 ^ 40 * 237982 * 2
def baseEnd_237982 : Nat := 54310734719285834680243

theorem tailTrace_237982 : CollatzResearch.WordTrace tailWord_237982 prefixEnd_237982 54310734719285834680243 := by
  unfold tailWord_237982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084989577979916616858525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5786611082559555289912133 1084989577979916616858525)
  ·
    refine ⟨406871091742468731321947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1084989577979916616858525 406871091742468731321947)
    ·
      refine ⟨610306637613703096982921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406871091742468731321947 610306637613703096982921)
      ·
        refine ⟨457729978210277322737191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610306637613703096982921 457729978210277322737191)
        ·
          refine ⟨686594967315415984105787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457729978210277322737191 686594967315415984105787)
          ·
            refine ⟨1029892450973123976158681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686594967315415984105787 1029892450973123976158681)
            ·
              refine ⟨772419338229842982119011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1029892450973123976158681 772419338229842982119011)
              ·
                refine ⟨1158629007344764473178517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772419338229842982119011 1158629007344764473178517)
                ·
                  refine ⟨54310734719285834680243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1158629007344764473178517 54310734719285834680243)
                  ·
                    rfl

theorem cell21_237982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_237982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237982 prefixEnd_237982 := by exact prefixLift 237982
  have htrace : WordTrace (prefixWord ++ tailWord_237982) baseStart_237982 baseEnd_237982 := by
    simpa [prefixWord, tailWord_237982, baseEnd_237982] using wordTrace_append hprefix tailTrace_237982
  have hstable : (prefixWord ++ tailWord_237982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237982).length < 2 ^ (prefixWord ++ tailWord_237982).sum := by decide
  have hdescent : baseEnd_237982 < baseStart_237982 := by decide
  rcases family_descends (prefixWord ++ tailWord_237982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237985 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 5]
def baseStart_237985 : Nat := 118140960795 + 237985 * 2 ^ 59
def prefixEnd_237985 : Nat := 4983230072969 + 3 ^ 40 * 237985 * 2
def baseEnd_237985 : Nat := 54311419360158496130237

theorem tailTrace_237985 : CollatzResearch.WordTrace tailWord_237985 prefixEnd_237985 54311419360158496130237 := by
  unfold tailWord_237985
  simp only [CollatzResearch.WordTrace]
  refine ⟨8680026042828464447227409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5786684028552309631484939 8680026042828464447227409)
  ·
    refine ⟨6510019532121348335420557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8680026042828464447227409 6510019532121348335420557)
    ·
      refine ⟨2441257324545505625782709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6510019532121348335420557 2441257324545505625782709)
      ·
        refine ⟨228867874176141152417129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2441257324545505625782709 228867874176141152417129)
        ·
          refine ⟨171650905632105864312847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228867874176141152417129 171650905632105864312847)
          ·
            refine ⟨257476358448158796469271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171650905632105864312847 257476358448158796469271)
            ·
              refine ⟨386214537672238194703907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257476358448158796469271 386214537672238194703907)
              ·
                refine ⟨579321806508357292055861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386214537672238194703907 579321806508357292055861)
                ·
                  refine ⟨54311419360158496130237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 579321806508357292055861 54311419360158496130237)
                  ·
                    rfl

theorem cell21_237985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 5].length) (baseStart_237985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_237985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_237985 prefixEnd_237985 := by exact prefixLift 237985
  have htrace : WordTrace (prefixWord ++ tailWord_237985) baseStart_237985 baseEnd_237985 := by
    simpa [prefixWord, tailWord_237985, baseEnd_237985] using wordTrace_append hprefix tailTrace_237985
  have hstable : (prefixWord ++ tailWord_237985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237985).length < 2 ^ (prefixWord ++ tailWord_237985).sum := by decide
  have hdescent : baseEnd_237985 < baseStart_237985 := by decide
  rcases family_descends (prefixWord ++ tailWord_237985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238041 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 4]
def baseStart_238041 : Nat := 118140960795 + 238041 * 2 ^ 59
def prefixEnd_238041 : Nat := 4983230072969 + 3 ^ 40 * 238041 * 2
def baseEnd_238041 : Nat := 54324199323114843196789

theorem tailTrace_238041 : CollatzResearch.WordTrace tailWord_238041 prefixEnd_238041 54324199323114843196789 := by
  unfold tailWord_238041
  simp only [CollatzResearch.WordTrace]
  refine ⟨8682068530625586011265977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5788045687083724007510651 8682068530625586011265977)
  ·
    refine ⟨6511551397969189508449483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8682068530625586011265977 6511551397969189508449483)
    ·
      refine ⟨9767327096953784262674225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6511551397969189508449483 9767327096953784262674225)
      ·
        refine ⟨7325495322715338197005669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9767327096953784262674225 7325495322715338197005669)
        ·
          refine ⟨1373530373009125911938563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7325495322715338197005669 1373530373009125911938563)
          ·
            refine ⟨2060295559513688867907845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373530373009125911938563 2060295559513688867907845)
            ·
              refine ⟨386305417408816662732721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2060295559513688867907845 386305417408816662732721)
              ·
                refine ⟨289729063056612497049541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386305417408816662732721 289729063056612497049541)
                ·
                  refine ⟨54324199323114843196789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289729063056612497049541 54324199323114843196789)
                  ·
                    rfl

theorem cell21_238041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_238041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238041 prefixEnd_238041 := by exact prefixLift 238041
  have htrace : WordTrace (prefixWord ++ tailWord_238041) baseStart_238041 baseEnd_238041 := by
    simpa [prefixWord, tailWord_238041, baseEnd_238041] using wordTrace_append hprefix tailTrace_238041
  have hstable : (prefixWord ++ tailWord_238041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238041).length < 2 ^ (prefixWord ++ tailWord_238041).sum := by decide
  have hdescent : baseEnd_238041 < baseStart_238041 := by decide
  rcases family_descends (prefixWord ++ tailWord_238041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238255 : List Nat := [1, 1, 2, 1, 2, 6, 2, 3, 3]
def baseStart_238255 : Nat := 118140960795 + 238255 * 2 ^ 59
def prefixEnd_238255 : Nat := 4983230072969 + 3 ^ 40 * 238255 * 2
def baseEnd_238255 : Nat := 54373037038698026629685

theorem tailTrace_238255 : CollatzResearch.WordTrace tailWord_238255 prefixEnd_238255 54373037038698026629685 := by
  unfold tailWord_238255
  simp only [CollatzResearch.WordTrace]
  refine ⟨8689873751850300559556219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5793249167900200373037479 8689873751850300559556219)
  ·
    refine ⟨13034810627775450839334329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8689873751850300559556219 13034810627775450839334329)
    ·
      refine ⟨9776107970831588129500747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13034810627775450839334329 9776107970831588129500747)
      ·
        refine ⟨14664161956247382194251121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9776107970831588129500747 14664161956247382194251121)
        ·
          refine ⟨10998121467185536645688341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14664161956247382194251121 10998121467185536645688341)
          ·
            refine ⟨515536943774322030266641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10998121467185536645688341 515536943774322030266641)
            ·
              refine ⟨386652707830741522699981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515536943774322030266641 386652707830741522699981)
              ·
                refine ⟨144994765436528071012493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 386652707830741522699981 144994765436528071012493)
                ·
                  refine ⟨54373037038698026629685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144994765436528071012493 54373037038698026629685)
                  ·
                    rfl

theorem cell21_238255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 3].length) (baseStart_238255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238255 prefixEnd_238255 := by exact prefixLift 238255
  have htrace : WordTrace (prefixWord ++ tailWord_238255) baseStart_238255 baseEnd_238255 := by
    simpa [prefixWord, tailWord_238255, baseEnd_238255] using wordTrace_append hprefix tailTrace_238255
  have hstable : (prefixWord ++ tailWord_238255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238255).length < 2 ^ (prefixWord ++ tailWord_238255).sum := by decide
  have hdescent : baseEnd_238255 < baseStart_238255 := by decide
  rcases family_descends (prefixWord ++ tailWord_238255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238266 : List Nat := [3, 1, 1, 1, 2, 3, 10]
def baseStart_238266 : Nat := 118140960795 + 238266 * 2 ^ 59
def prefixEnd_238266 : Nat := 4983230072969 + 3 ^ 40 * 238266 * 2
def baseEnd_238266 : Nat := 6041727487618272438481

theorem tailTrace_238266 : CollatzResearch.WordTrace tailWord_238266 prefixEnd_238266 6041727487618272438481 := by
  unfold tailWord_238266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172568738702612359551663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5793516636540299625471101 2172568738702612359551663)
  ·
    refine ⟨3258853108053918539327495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2172568738702612359551663 3258853108053918539327495)
    ·
      refine ⟨4888279662080877808991243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3258853108053918539327495 4888279662080877808991243)
      ·
        refine ⟨7332419493121316713486865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4888279662080877808991243 7332419493121316713486865)
        ·
          refine ⟨5499314619840987535115149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7332419493121316713486865 5499314619840987535115149)
          ·
            refine ⟨2062242982440370325668181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5499314619840987535115149 2062242982440370325668181)
            ·
              refine ⟨6041727487618272438481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2062242982440370325668181 6041727487618272438481)
              ·
                rfl

theorem cell21_238266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 10].length) (baseStart_238266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238266 prefixEnd_238266 := by exact prefixLift 238266
  have htrace : WordTrace (prefixWord ++ tailWord_238266) baseStart_238266 baseEnd_238266 := by
    simpa [prefixWord, tailWord_238266, baseEnd_238266] using wordTrace_append hprefix tailTrace_238266
  have hstable : (prefixWord ++ tailWord_238266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238266).length < 2 ^ (prefixWord ++ tailWord_238266).sum := by decide
  have hdescent : baseEnd_238266 < baseStart_238266 := by decide
  rcases family_descends (prefixWord ++ tailWord_238266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238269 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 4]
def baseStart_238269 : Nat := 118140960795 + 238269 * 2 ^ 59
def prefixEnd_238269 : Nat := 4983230072969 + 3 ^ 40 * 238269 * 2
def baseEnd_238269 : Nat := 54376232029437113396323

theorem tailTrace_238269 : CollatzResearch.WordTrace tailWord_238269 prefixEnd_238269 54376232029437113396323 := by
  unfold tailWord_238269
  simp only [CollatzResearch.WordTrace]
  refine ⟨8690384373799580950565861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5793589582533053967043907 8690384373799580950565861)
  ·
    refine ⟨1629447070087421428231099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8690384373799580950565861 1629447070087421428231099)
    ·
      refine ⟨2444170605131132142346649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629447070087421428231099 2444170605131132142346649)
      ·
        refine ⟨1833127953848349106759987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2444170605131132142346649 1833127953848349106759987)
        ·
          refine ⟨2749691930772523660139981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1833127953848349106759987 2749691930772523660139981)
          ·
            refine ⟨1031134474039696372552493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2749691930772523660139981 1031134474039696372552493)
            ·
              refine ⟨386675427764886139707185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1031134474039696372552493 386675427764886139707185)
              ·
                refine ⟨290006570823664604780389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386675427764886139707185 290006570823664604780389)
                ·
                  refine ⟨54376232029437113396323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290006570823664604780389 54376232029437113396323)
                  ·
                    rfl

theorem cell21_238269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_238269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238269 prefixEnd_238269 := by exact prefixLift 238269
  have htrace : WordTrace (prefixWord ++ tailWord_238269) baseStart_238269 baseEnd_238269 := by
    simpa [prefixWord, tailWord_238269, baseEnd_238269] using wordTrace_append hprefix tailTrace_238269
  have hstable : (prefixWord ++ tailWord_238269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238269).length < 2 ^ (prefixWord ++ tailWord_238269).sum := by decide
  have hdescent : baseEnd_238269 < baseStart_238269 := by decide
  rcases family_descends (prefixWord ++ tailWord_238269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238286 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_238286 : Nat := 118140960795 + 238286 * 2 ^ 59
def prefixEnd_238286 : Nat := 4983230072969 + 3 ^ 40 * 238286 * 2
def baseEnd_238286 : Nat := 54380111661048861612955

theorem tailTrace_238286 : CollatzResearch.WordTrace tailWord_238286 prefixEnd_238286 54380111661048861612955 := by
  unfold tailWord_238286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1086375551842249106741839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5794002943158661902623141 1086375551842249106741839)
  ·
    refine ⟨1629563327763373660112759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1086375551842249106741839 1629563327763373660112759)
    ·
      refine ⟨2444344991645060490169139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629563327763373660112759 2444344991645060490169139)
      ·
        refine ⟨3666517487467590735253709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444344991645060490169139 3666517487467590735253709)
        ·
          refine ⟨1374944057800346525720141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3666517487467590735253709 1374944057800346525720141)
          ·
            refine ⟨515604021675129947145053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1374944057800346525720141 515604021675129947145053)
            ·
              refine ⟨193351508128173730179395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 515604021675129947145053 193351508128173730179395)
              ·
                refine ⟨290027262192260595269093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193351508128173730179395 290027262192260595269093)
                ·
                  refine ⟨54380111661048861612955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290027262192260595269093 54380111661048861612955)
                  ·
                    rfl

theorem cell21_238286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_238286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238286 prefixEnd_238286 := by exact prefixLift 238286
  have htrace : WordTrace (prefixWord ++ tailWord_238286) baseStart_238286 baseEnd_238286 := by
    simpa [prefixWord, tailWord_238286, baseEnd_238286] using wordTrace_append hprefix tailTrace_238286
  have hstable : (prefixWord ++ tailWord_238286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238286).length < 2 ^ (prefixWord ++ tailWord_238286).sum := by decide
  have hdescent : baseEnd_238286 < baseStart_238286 := by decide
  rcases family_descends (prefixWord ++ tailWord_238286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238297 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 5]
def baseStart_238297 : Nat := 118140960795 + 238297 * 2 ^ 59
def prefixEnd_238297 : Nat := 4983230072969 + 3 ^ 40 * 238297 * 2
def baseEnd_238297 : Nat := 54382622010915286929599

theorem tailTrace_238297 : CollatzResearch.WordTrace tailWord_238297 prefixEnd_238297 54382622010915286929599 := by
  unfold tailWord_238297
  simp only [CollatzResearch.WordTrace]
  refine ⟨8691405617698141732585145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5794270411798761155056763 8691405617698141732585145)
  ·
    refine ⟨6518554213273606299438859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8691405617698141732585145 6518554213273606299438859)
    ·
      refine ⟨9777831319910409449158289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6518554213273606299438859 9777831319910409449158289)
      ·
        refine ⟨7333373489932807086868717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9777831319910409449158289 7333373489932807086868717)
        ·
          refine ⟨2750015058724802657575769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7333373489932807086868717 2750015058724802657575769)
          ·
            refine ⟨2062511294043601993181827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2750015058724802657575769 2062511294043601993181827)
            ·
              refine ⟨3093766941065402989772741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062511294043601993181827 3093766941065402989772741)
              ·
                refine ⟨580081301449763060582389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3093766941065402989772741 580081301449763060582389)
                ·
                  refine ⟨54382622010915286929599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 580081301449763060582389 54382622010915286929599)
                  ·
                    rfl

theorem cell21_238297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_238297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238297 prefixEnd_238297 := by exact prefixLift 238297
  have htrace : WordTrace (prefixWord ++ tailWord_238297) baseStart_238297 baseEnd_238297 := by
    simpa [prefixWord, tailWord_238297, baseEnd_238297] using wordTrace_append hprefix tailTrace_238297
  have hstable : (prefixWord ++ tailWord_238297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238297).length < 2 ^ (prefixWord ++ tailWord_238297).sum := by decide
  have hdescent : baseEnd_238297 < baseStart_238297 := by decide
  rcases family_descends (prefixWord ++ tailWord_238297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238300 : List Nat := [2, 2, 5, 1, 1, 2, 1, 7]
def baseStart_238300 : Nat := 118140960795 + 238300 * 2 ^ 59
def prefixEnd_238300 : Nat := 4983230072969 + 3 ^ 40 * 238300 * 2
def baseEnd_238300 : Nat := 18127768883929316126531

theorem tailTrace_238300 : CollatzResearch.WordTrace tailWord_238300 prefixEnd_238300 18127768883929316126531 := by
  unfold tailWord_238300
  simp only [CollatzResearch.WordTrace]
  refine ⟨4345757518343636622472177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5794343357791515496629569 4345757518343636622472177)
  ·
    refine ⟨3259318138757727466854133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4345757518343636622472177 3259318138757727466854133)
    ·
      refine ⟨305561075508536950017575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3259318138757727466854133 305561075508536950017575)
      ·
        refine ⟨458341613262805425026363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305561075508536950017575 458341613262805425026363)
        ·
          refine ⟨687512419894208137539545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458341613262805425026363 687512419894208137539545)
          ·
            refine ⟨515634314920656103154659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687512419894208137539545 515634314920656103154659)
            ·
              refine ⟨773451472380984154731989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515634314920656103154659 773451472380984154731989)
              ·
                refine ⟨18127768883929316126531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 773451472380984154731989 18127768883929316126531)
                ·
                  rfl

theorem cell21_238300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_238300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238300 prefixEnd_238300 := by exact prefixLift 238300
  have htrace : WordTrace (prefixWord ++ tailWord_238300) baseStart_238300 baseEnd_238300 := by
    simpa [prefixWord, tailWord_238300, baseEnd_238300] using wordTrace_append hprefix tailTrace_238300
  have hstable : (prefixWord ++ tailWord_238300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238300).length < 2 ^ (prefixWord ++ tailWord_238300).sum := by decide
  have hdescent : baseEnd_238300 < baseStart_238300 := by decide
  rcases family_descends (prefixWord ++ tailWord_238300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238328 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 4]
def baseStart_238328 : Nat := 118140960795 + 238328 * 2 ^ 59
def prefixEnd_238328 : Nat := 4983230072969 + 3 ^ 40 * 238328 * 2
def baseEnd_238328 : Nat := 54389696633266121912869

theorem tailTrace_238328 : CollatzResearch.WordTrace tailWord_238328 prefixEnd_238328 54389696633266121912869 := by
  unfold tailWord_238328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4346268140292917013481819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5795024187057222684642425 4346268140292917013481819)
  ·
    refine ⟨6519402210439375520222729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4346268140292917013481819 6519402210439375520222729)
    ·
      refine ⟨4889551657829531640167047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6519402210439375520222729 4889551657829531640167047)
      ·
        refine ⟨7334327486744297460250571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889551657829531640167047 7334327486744297460250571)
        ·
          refine ⟨11001491230116446190375857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7334327486744297460250571 11001491230116446190375857)
          ·
            refine ⟨8251118422587334642781893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11001491230116446190375857 8251118422587334642781893)
            ·
              refine ⟨1547084704235125245521605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8251118422587334642781893 1547084704235125245521605)
              ·
                refine ⟨290078382044085983535301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1547084704235125245521605 290078382044085983535301)
                ·
                  refine ⟨54389696633266121912869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290078382044085983535301 54389696633266121912869)
                  ·
                    rfl

theorem cell21_238328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_238328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238328 prefixEnd_238328 := by exact prefixLift 238328
  have htrace : WordTrace (prefixWord ++ tailWord_238328) baseStart_238328 baseEnd_238328 := by
    simpa [prefixWord, tailWord_238328, baseEnd_238328] using wordTrace_append hprefix tailTrace_238328
  have hstable : (prefixWord ++ tailWord_238328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238328).length < 2 ^ (prefixWord ++ tailWord_238328).sum := by decide
  have hdescent : baseEnd_238328 < baseStart_238328 := by decide
  rcases family_descends (prefixWord ++ tailWord_238328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238345 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 4]
def baseStart_238345 : Nat := 118140960795 + 238345 * 2 ^ 59
def prefixEnd_238345 : Nat := 4983230072969 + 3 ^ 40 * 238345 * 2
def baseEnd_238345 : Nat := 54393576264877870129501

theorem tailTrace_238345 : CollatzResearch.WordTrace tailWord_238345 prefixEnd_238345 54393576264877870129501 := by
  unfold tailWord_238345
  simp only [CollatzResearch.WordTrace]
  refine ⟨8693156321524245930332489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5795437547682830620221659 8693156321524245930332489)
  ·
    refine ⟨6519867241143184447749367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8693156321524245930332489 6519867241143184447749367)
    ·
      refine ⟨9779800861714776671624051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6519867241143184447749367 9779800861714776671624051)
      ·
        refine ⟨14669701292572165007436077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9779800861714776671624051 14669701292572165007436077)
        ·
          refine ⟨5501137984714561877788529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14669701292572165007436077 5501137984714561877788529)
          ·
            refine ⟨4125853488535921408341397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5501137984714561877788529 4125853488535921408341397)
            ·
              refine ⟨193399382275121316016003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4125853488535921408341397 193399382275121316016003)
              ·
                refine ⟨290099073412681974024005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193399382275121316016003 290099073412681974024005)
                ·
                  refine ⟨54393576264877870129501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290099073412681974024005 54393576264877870129501)
                  ·
                    rfl

theorem cell21_238345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_238345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238345 prefixEnd_238345 := by exact prefixLift 238345
  have htrace : WordTrace (prefixWord ++ tailWord_238345) baseStart_238345 baseEnd_238345 := by
    simpa [prefixWord, tailWord_238345, baseEnd_238345] using wordTrace_append hprefix tailTrace_238345
  have hstable : (prefixWord ++ tailWord_238345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238345).length < 2 ^ (prefixWord ++ tailWord_238345).sum := by decide
  have hdescent : baseEnd_238345 < baseStart_238345 := by decide
  rcases family_descends (prefixWord ++ tailWord_238345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238449 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 5]
def baseStart_238449 : Nat := 118140960795 + 238449 * 2 ^ 59
def prefixEnd_238449 : Nat := 4983230072969 + 3 ^ 40 * 238449 * 2
def baseEnd_238449 : Nat := 54417310481796800395955

theorem tailTrace_238449 : CollatzResearch.WordTrace tailWord_238449 prefixEnd_238449 54417310481796800395955 := by
  unfold tailWord_238449
  simp only [CollatzResearch.WordTrace]
  refine ⟨8696949513147471692118401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5797966342098314461412267 8696949513147471692118401)
  ·
    refine ⟨6522712134860603769088801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8696949513147471692118401 6522712134860603769088801)
    ·
      refine ⟨4892034101145452826816601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6522712134860603769088801 4892034101145452826816601)
      ·
        refine ⟨3669025575859089620112451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4892034101145452826816601 3669025575859089620112451)
        ·
          refine ⟨5503538363788634430168677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3669025575859089620112451 5503538363788634430168677)
          ·
            refine ⟨1031913443210368955656627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5503538363788634430168677 1031913443210368955656627)
            ·
              refine ⟨1547870164815553433484941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031913443210368955656627 1547870164815553433484941)
              ·
                refine ⟨580451311805832537556853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1547870164815553433484941 580451311805832537556853)
                ·
                  refine ⟨54417310481796800395955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 580451311805832537556853 54417310481796800395955)
                  ·
                    rfl

theorem cell21_238449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_238449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238449 prefixEnd_238449 := by exact prefixLift 238449
  have htrace : WordTrace (prefixWord ++ tailWord_238449) baseStart_238449 baseEnd_238449 := by
    simpa [prefixWord, tailWord_238449, baseEnd_238449] using wordTrace_append hprefix tailTrace_238449
  have hstable : (prefixWord ++ tailWord_238449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238449).length < 2 ^ (prefixWord ++ tailWord_238449).sum := by decide
  have hdescent : baseEnd_238449 < baseStart_238449 := by decide
  rcases family_descends (prefixWord ++ tailWord_238449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238559 : List Nat := [1, 1, 2, 3, 5, 1, 1, 4, 3]
def baseStart_238559 : Nat := 118140960795 + 238559 * 2 ^ 59
def prefixEnd_238559 : Nat := 4983230072969 + 3 ^ 40 * 238559 * 2
def baseEnd_238559 : Nat := 54442413980461053562397

theorem tailTrace_238559 : CollatzResearch.WordTrace tailWord_238559 prefixEnd_238559 54442413980461053562397 := by
  unfold tailWord_238559
  simp only [CollatzResearch.WordTrace]
  refine ⟨8700961542748960478622731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5800641028499306985748487 8700961542748960478622731)
  ·
    refine ⟨13051442314123440717934097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8700961542748960478622731 13051442314123440717934097)
    ·
      refine ⟨9788581735592580538450573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13051442314123440717934097 9788581735592580538450573)
      ·
        refine ⟨3670718150847217701918965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9788581735592580538450573 3670718150847217701918965)
        ·
          refine ⟨344129826641926659554903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3670718150847217701918965 344129826641926659554903)
          ·
            refine ⟨516194739962889989332355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344129826641926659554903 516194739962889989332355)
            ·
              refine ⟨774292109944334983998533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516194739962889989332355 774292109944334983998533)
              ·
                refine ⟨145179770614562809499725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 774292109944334983998533 145179770614562809499725)
                ·
                  refine ⟨54442413980461053562397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145179770614562809499725 54442413980461053562397)
                  ·
                    rfl

theorem cell21_238559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 3].length) (baseStart_238559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238559 prefixEnd_238559 := by exact prefixLift 238559
  have htrace : WordTrace (prefixWord ++ tailWord_238559) baseStart_238559 baseEnd_238559 := by
    simpa [prefixWord, tailWord_238559, baseEnd_238559] using wordTrace_append hprefix tailTrace_238559
  have hstable : (prefixWord ++ tailWord_238559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238559).length < 2 ^ (prefixWord ++ tailWord_238559).sum := by decide
  have hdescent : baseEnd_238559 < baseStart_238559 := by decide
  rcases family_descends (prefixWord ++ tailWord_238559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238618 : List Nat := [3, 1, 1, 3, 1, 2, 1, 6, 3]
def baseStart_238618 : Nat := 118140960795 + 238618 * 2 ^ 59
def prefixEnd_238618 : Nat := 4983230072969 + 3 ^ 40 * 238618 * 2
def baseEnd_238618 : Nat := 54455878584290062078943

theorem tailTrace_238618 : CollatzResearch.WordTrace tailWord_238618 prefixEnd_238618 54455878584290062078943 := by
  unfold tailWord_238618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2175778362383803388755127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5802075633023475703347005 2175778362383803388755127)
  ·
    refine ⟨3263667543575705083132691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2175778362383803388755127 3263667543575705083132691)
    ·
      refine ⟨4895501315363557624699037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3263667543575705083132691 4895501315363557624699037)
      ·
        refine ⟨1835812993261334109262139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4895501315363557624699037 1835812993261334109262139)
        ·
          refine ⟨2753719489892001163893209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835812993261334109262139 2753719489892001163893209)
          ·
            refine ⟨2065289617419000872919907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2753719489892001163893209 2065289617419000872919907)
            ·
              refine ⟨3097934426128501309379861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065289617419000872919907 3097934426128501309379861)
              ·
                refine ⟨145215676224773498877181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3097934426128501309379861 145215676224773498877181)
                ·
                  refine ⟨54455878584290062078943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145215676224773498877181 54455878584290062078943)
                  ·
                    rfl

theorem cell21_238618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_238618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238618 prefixEnd_238618 := by exact prefixLift 238618
  have htrace : WordTrace (prefixWord ++ tailWord_238618) baseStart_238618 baseEnd_238618 := by
    simpa [prefixWord, tailWord_238618, baseEnd_238618] using wordTrace_append hprefix tailTrace_238618
  have hstable : (prefixWord ++ tailWord_238618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238618).length < 2 ^ (prefixWord ++ tailWord_238618).sum := by decide
  have hdescent : baseEnd_238618 < baseStart_238618 := by decide
  rcases family_descends (prefixWord ++ tailWord_238618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238725 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 4]
def baseStart_238725 : Nat := 118140960795 + 238725 * 2 ^ 59
def prefixEnd_238725 : Nat := 4983230072969 + 3 ^ 40 * 238725 * 2
def baseEnd_238725 : Nat := 54480297442081653795391

theorem tailTrace_238725 : CollatzResearch.WordTrace tailWord_238725 prefixEnd_238725 54480297442081653795391 := by
  unfold tailWord_238725
  simp only [CollatzResearch.WordTrace]
  refine ⟨8707016060147570829165629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5804677373431713886110419 8707016060147570829165629)
  ·
    refine ⟨3265131022555339060937111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8707016060147570829165629 3265131022555339060937111)
    ·
      refine ⟨4897696533833008591405667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265131022555339060937111 4897696533833008591405667)
      ·
        refine ⟨7346544800749512887108501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4897696533833008591405667 7346544800749512887108501)
        ·
          refine ⟨344369287535133416583211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7346544800749512887108501 344369287535133416583211)
          ·
            refine ⟨516553931302700124874817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344369287535133416583211 516553931302700124874817)
            ·
              refine ⟨387415448477025093656113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516553931302700124874817 387415448477025093656113)
              ·
                refine ⟨290561586357768820242085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387415448477025093656113 290561586357768820242085)
                ·
                  refine ⟨54480297442081653795391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290561586357768820242085 54480297442081653795391)
                  ·
                    rfl

theorem cell21_238725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_238725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238725 prefixEnd_238725 := by exact prefixLift 238725
  have htrace : WordTrace (prefixWord ++ tailWord_238725) baseStart_238725 baseEnd_238725 := by
    simpa [prefixWord, tailWord_238725, baseEnd_238725] using wordTrace_append hprefix tailTrace_238725
  have hstable : (prefixWord ++ tailWord_238725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238725).length < 2 ^ (prefixWord ++ tailWord_238725).sum := by decide
  have hdescent : baseEnd_238725 < baseStart_238725 := by decide
  rcases family_descends (prefixWord ++ tailWord_238725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238753 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 5]
def baseStart_238753 : Nat := 118140960795 + 238753 * 2 ^ 59
def prefixEnd_238753 : Nat := 4983230072969 + 3 ^ 40 * 238753 * 2
def baseEnd_238753 : Nat := 54486687423559827328667

theorem tailTrace_238753 : CollatzResearch.WordTrace tailWord_238753 prefixEnd_238753 54486687423559827328667 := by
  unfold tailWord_238753
  simp only [CollatzResearch.WordTrace]
  refine ⟨8708037304046131611184913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5805358202697421074123275 8708037304046131611184913)
  ·
    refine ⟨6531027978034598708388685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8708037304046131611184913 6531027978034598708388685)
    ·
      refine ⟨2449135491762974515645757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6531027978034598708388685 2449135491762974515645757)
      ·
        refine ⟨918425809411115443367159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2449135491762974515645757 918425809411115443367159)
        ·
          refine ⟨1377638714116673165050739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918425809411115443367159 1377638714116673165050739)
          ·
            refine ⟨2066458071175009747576109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377638714116673165050739 2066458071175009747576109)
            ·
              refine ⟨774921776690628655341041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2066458071175009747576109 774921776690628655341041)
              ·
                refine ⟨581191332517971491505781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774921776690628655341041 581191332517971491505781)
                ·
                  refine ⟨54486687423559827328667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 581191332517971491505781 54486687423559827328667)
                  ·
                    rfl

theorem cell21_238753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_238753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238753 prefixEnd_238753 := by exact prefixLift 238753
  have htrace : WordTrace (prefixWord ++ tailWord_238753) baseStart_238753 baseEnd_238753 := by
    simpa [prefixWord, tailWord_238753, baseEnd_238753] using wordTrace_append hprefix tailTrace_238753
  have hstable : (prefixWord ++ tailWord_238753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238753).length < 2 ^ (prefixWord ++ tailWord_238753).sum := by decide
  have hdescent : baseEnd_238753 < baseStart_238753 := by decide
  rcases family_descends (prefixWord ++ tailWord_238753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238770 : List Nat := [3, 2, 1, 1, 1, 4, 1, 5, 3]
def baseStart_238770 : Nat := 118140960795 + 238770 * 2 ^ 59
def prefixEnd_238770 : Nat := 4983230072969 + 3 ^ 40 * 238770 * 2
def baseEnd_238770 : Nat := 54490567055171575545299

theorem tailTrace_238770 : CollatzResearch.WordTrace tailWord_238770 prefixEnd_238770 54490567055171575545299 := by
  unfold tailWord_238770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177164336246135878638441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5805771563323029009702509 2177164336246135878638441)
  ·
    refine ⟨1632873252184601908978831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2177164336246135878638441 1632873252184601908978831)
    ·
      refine ⟨2449309878276902863468247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1632873252184601908978831 2449309878276902863468247)
      ·
        refine ⟨3673964817415354295202371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449309878276902863468247 3673964817415354295202371)
        ·
          refine ⟨5510947226123031442803557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673964817415354295202371 5510947226123031442803557)
          ·
            refine ⟨1033302604898068395525667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5510947226123031442803557 1033302604898068395525667)
            ·
              refine ⟨1549953907347102593288501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033302604898068395525667 1549953907347102593288501)
              ·
                refine ⟨145308178813790868120797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1549953907347102593288501 145308178813790868120797)
                ·
                  refine ⟨54490567055171575545299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145308178813790868120797 54490567055171575545299)
                  ·
                    rfl

theorem cell21_238770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_238770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238770 prefixEnd_238770 := by exact prefixLift 238770
  have htrace : WordTrace (prefixWord ++ tailWord_238770) baseStart_238770 baseEnd_238770 := by
    simpa [prefixWord, tailWord_238770, baseEnd_238770] using wordTrace_append hprefix tailTrace_238770
  have hstable : (prefixWord ++ tailWord_238770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238770).length < 2 ^ (prefixWord ++ tailWord_238770).sum := by decide
  have hdescent : baseEnd_238770 < baseStart_238770 := by decide
  rcases family_descends (prefixWord ++ tailWord_238770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238784 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 6]
def baseStart_238784 : Nat := 118140960795 + 238784 * 2 ^ 59
def prefixEnd_238784 : Nat := 4983230072969 + 3 ^ 40 * 238784 * 2
def baseEnd_238784 : Nat := 54493762045910662311937

theorem tailTrace_238784 : CollatzResearch.WordTrace tailWord_238784 prefixEnd_238784 54493762045910662311937 := by
  unfold tailWord_238784
  simp only [CollatzResearch.WordTrace]
  refine ⟨4354583983466911952781703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5806111977955882603708937 4354583983466911952781703)
  ·
    refine ⟨6531875975200367929172555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4354583983466911952781703 6531875975200367929172555)
    ·
      refine ⟨9797813962800551893758833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6531875975200367929172555 9797813962800551893758833)
      ·
        refine ⟨7348360472100413920319125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9797813962800551893758833 7348360472100413920319125)
        ·
          refine ⟨344454397129706902514959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7348360472100413920319125 344454397129706902514959)
          ·
            refine ⟨516681595694560353772439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344454397129706902514959 516681595694560353772439)
            ·
              refine ⟨775022393541840530658659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516681595694560353772439 775022393541840530658659)
              ·
                refine ⟨1162533590312760795987989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775022393541840530658659 1162533590312760795987989)
                ·
                  refine ⟨54493762045910662311937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1162533590312760795987989 54493762045910662311937)
                  ·
                    rfl

theorem cell21_238784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_238784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238784 prefixEnd_238784 := by exact prefixLift 238784
  have htrace : WordTrace (prefixWord ++ tailWord_238784) baseStart_238784 baseEnd_238784 := by
    simpa [prefixWord, tailWord_238784, baseEnd_238784] using wordTrace_append hprefix tailTrace_238784
  have hstable : (prefixWord ++ tailWord_238784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238784).length < 2 ^ (prefixWord ++ tailWord_238784).sum := by decide
  have hdescent : baseEnd_238784 < baseStart_238784 := by decide
  rcases family_descends (prefixWord ++ tailWord_238784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238846 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_238846 : Nat := 118140960795 + 238846 * 2 ^ 59
def prefixEnd_238846 : Nat := 4983230072969 + 3 ^ 40 * 238846 * 2
def baseEnd_238846 : Nat := 54507911290612332278477

theorem tailTrace_238846 : CollatzResearch.WordTrace tailWord_238846 prefixEnd_238846 54507911290612332278477 := by
  unfold tailWord_238846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088928661588651061790049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5807619528472805662880261 1088928661588651061790049)
  ·
    refine ⟨816696496191488296342537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1088928661588651061790049 816696496191488296342537)
    ·
      refine ⟨612522372143616222256903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 816696496191488296342537 612522372143616222256903)
      ·
        refine ⟨918783558215424333385355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612522372143616222256903 918783558215424333385355)
        ·
          refine ⟨1378175337323136500078033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918783558215424333385355 1378175337323136500078033)
          ·
            refine ⟨1033631502992352375058525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378175337323136500078033 1033631502992352375058525)
            ·
              refine ⟨387611813622132140646947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033631502992352375058525 387611813622132140646947)
              ·
                refine ⟨581417720433198210970421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387611813622132140646947 581417720433198210970421)
                ·
                  refine ⟨54507911290612332278477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 581417720433198210970421 54507911290612332278477)
                  ·
                    rfl

theorem cell21_238846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_238846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238846 prefixEnd_238846 := by exact prefixLift 238846
  have htrace : WordTrace (prefixWord ++ tailWord_238846) baseStart_238846 baseEnd_238846 := by
    simpa [prefixWord, tailWord_238846, baseEnd_238846] using wordTrace_append hprefix tailTrace_238846
  have hstable : (prefixWord ++ tailWord_238846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238846).length < 2 ^ (prefixWord ++ tailWord_238846).sum := by decide
  have hdescent : baseEnd_238846 < baseStart_238846 := by decide
  rcases family_descends (prefixWord ++ tailWord_238846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238860 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 4]
def baseStart_238860 : Nat := 118140960795 + 238860 * 2 ^ 59
def prefixEnd_238860 : Nat := 4983230072969 + 3 ^ 40 * 238860 * 2
def baseEnd_238860 : Nat := 54511106281351419045115

theorem tailTrace_238860 : CollatzResearch.WordTrace tailWord_238860 prefixEnd_238860 54511106281351419045115 := by
  unfold tailWord_238860
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355969957329244442665017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5807959943105659256886689 4355969957329244442665017)
  ·
    refine ⟨3266977467996933331998763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4355969957329244442665017 3266977467996933331998763)
    ·
      refine ⟨4900466201995399997998145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3266977467996933331998763 4900466201995399997998145)
      ·
        refine ⟨3675349651496549998498609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4900466201995399997998145 3675349651496549998498609)
        ·
          refine ⟨2756512238622412498873957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3675349651496549998498609 2756512238622412498873957)
          ·
            refine ⟨516846044741702343538867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2756512238622412498873957 516846044741702343538867)
            ·
              refine ⟨775269067112553515308301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516846044741702343538867 775269067112553515308301)
              ·
                refine ⟨290725900167207568240613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 775269067112553515308301 290725900167207568240613)
                ·
                  refine ⟨54511106281351419045115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290725900167207568240613 54511106281351419045115)
                  ·
                    rfl

theorem cell21_238860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_238860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238860 prefixEnd_238860 := by exact prefixLift 238860
  have htrace : WordTrace (prefixWord ++ tailWord_238860) baseStart_238860 baseEnd_238860 := by
    simpa [prefixWord, tailWord_238860, baseEnd_238860] using wordTrace_append hprefix tailTrace_238860
  have hstable : (prefixWord ++ tailWord_238860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238860).length < 2 ^ (prefixWord ++ tailWord_238860).sum := by decide
  have hdescent : baseEnd_238860 < baseStart_238860 := by decide
  rcases family_descends (prefixWord ++ tailWord_238860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238874 : List Nat := [3, 1, 1, 3, 3, 1, 2, 7]
def baseStart_238874 : Nat := 118140960795 + 238874 * 2 ^ 59
def prefixEnd_238874 : Nat := 4983230072969 + 3 ^ 40 * 238874 * 2
def baseEnd_238874 : Nat := 18171433757363501937251

theorem tailTrace_238874 : CollatzResearch.WordTrace tailWord_238874 prefixEnd_238874 18171433757363501937251 := by
  unfold tailWord_238874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2178112634151942319084919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5808300357738512850893117 2178112634151942319084919)
  ·
    refine ⟨3267168951227913478627379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2178112634151942319084919 3267168951227913478627379)
    ·
      refine ⟨4900753426841870217941069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3267168951227913478627379 4900753426841870217941069)
      ·
        refine ⟨1837782535065701331727901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4900753426841870217941069 1837782535065701331727901)
        ·
          refine ⟨689168450649637999397963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1837782535065701331727901 689168450649637999397963)
          ·
            refine ⟨1033752675974456999096945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689168450649637999397963 1033752675974456999096945)
            ·
              refine ⟨775314506980842749322709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033752675974456999096945 775314506980842749322709)
              ·
                refine ⟨18171433757363501937251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 775314506980842749322709 18171433757363501937251)
                ·
                  rfl

theorem cell21_238874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_238874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238874 prefixEnd_238874 := by exact prefixLift 238874
  have htrace : WordTrace (prefixWord ++ tailWord_238874) baseStart_238874 baseEnd_238874 := by
    simpa [prefixWord, tailWord_238874, baseEnd_238874] using wordTrace_append hprefix tailTrace_238874
  have hstable : (prefixWord ++ tailWord_238874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238874).length < 2 ^ (prefixWord ++ tailWord_238874).sum := by decide
  have hdescent : baseEnd_238874 < baseStart_238874 := by decide
  rcases family_descends (prefixWord ++ tailWord_238874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238925 : List Nat := [1, 6, 1, 3, 1, 1, 3, 5]
def baseStart_238925 : Nat := 118140960795 + 238925 * 2 ^ 59
def prefixEnd_238925 : Nat := 4983230072969 + 3 ^ 40 * 238925 * 2
def baseEnd_238925 : Nat := 18175313388975250153883

theorem tailTrace_238925 : CollatzResearch.WordTrace tailWord_238925 prefixEnd_238925 18175313388975250153883 := by
  unfold tailWord_238925
  simp only [CollatzResearch.WordTrace]
  refine ⟨8714310659423004986446229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5809540439615336657630819 8714310659423004986446229)
  ·
    refine ⟨408483312160453358739667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8714310659423004986446229 408483312160453358739667)
    ·
      refine ⟨612724968240680038109501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408483312160453358739667 612724968240680038109501)
      ·
        refine ⟨229771863090255014291063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 612724968240680038109501 229771863090255014291063)
        ·
          refine ⟨344657794635382521436595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229771863090255014291063 344657794635382521436595)
          ·
            refine ⟨516986691953073782154893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344657794635382521436595 516986691953073782154893)
            ·
              refine ⟨193870009482402668308085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 516986691953073782154893 193870009482402668308085)
              ·
                refine ⟨18175313388975250153883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 193870009482402668308085 18175313388975250153883)
                ·
                  rfl

theorem cell21_238925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 5].length) (baseStart_238925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_238925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_238925 prefixEnd_238925 := by exact prefixLift 238925
  have htrace : WordTrace (prefixWord ++ tailWord_238925) baseStart_238925 baseEnd_238925 := by
    simpa [prefixWord, tailWord_238925, baseEnd_238925] using wordTrace_append hprefix tailTrace_238925
  have hstable : (prefixWord ++ tailWord_238925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238925).length < 2 ^ (prefixWord ++ tailWord_238925).sum := by decide
  have hdescent : baseEnd_238925 < baseStart_238925 := by decide
  rcases family_descends (prefixWord ++ tailWord_238925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239015 : List Nat := [1, 1, 6, 1, 1, 1, 5, 2, 3]
def baseStart_239015 : Nat := 118140960795 + 239015 * 2 ^ 59
def prefixEnd_239015 : Nat := 4983230072969 + 3 ^ 40 * 239015 * 2
def baseEnd_239015 : Nat := 54546479393105593961465

theorem tailTrace_239015 : CollatzResearch.WordTrace tailWord_239015 prefixEnd_239015 54546479393105593961465 := by
  unfold tailWord_239015
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717593229096950357222499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5811728819397966904814999 8717593229096950357222499)
  ·
    refine ⟨13076389843645425535833749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8717593229096950357222499 13076389843645425535833749)
    ·
      refine ⟨612955773920879321992207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13076389843645425535833749 612955773920879321992207)
      ·
        refine ⟨919433660881318982988311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612955773920879321992207 919433660881318982988311)
        ·
          refine ⟨1379150491321978474482467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919433660881318982988311 1379150491321978474482467)
          ·
            refine ⟨2068725736982967711723701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379150491321978474482467 2068725736982967711723701)
            ·
              refine ⟨193943037842153222974097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2068725736982967711723701 193943037842153222974097)
              ·
                refine ⟨145457278381614917230573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193943037842153222974097 145457278381614917230573)
                ·
                  refine ⟨54546479393105593961465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145457278381614917230573 54546479393105593961465)
                  ·
                    rfl

theorem cell21_239015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 3].length) (baseStart_239015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239015 prefixEnd_239015 := by exact prefixLift 239015
  have htrace : WordTrace (prefixWord ++ tailWord_239015) baseStart_239015 baseEnd_239015 := by
    simpa [prefixWord, tailWord_239015, baseEnd_239015] using wordTrace_append hprefix tailTrace_239015
  have hstable : (prefixWord ++ tailWord_239015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239015).length < 2 ^ (prefixWord ++ tailWord_239015).sum := by decide
  have hdescent : baseEnd_239015 < baseStart_239015 := by decide
  rcases family_descends (prefixWord ++ tailWord_239015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239029 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 4]
def baseStart_239029 : Nat := 118140960795 + 239029 * 2 ^ 59
def prefixEnd_239029 : Nat := 4983230072969 + 3 ^ 40 * 239029 * 2
def baseEnd_239029 : Nat := 54549674383844680728103

theorem tailTrace_239029 : CollatzResearch.WordTrace tailWord_239029 prefixEnd_239029 54549674383844680728103 := by
  unfold tailWord_239029
  simp only [CollatzResearch.WordTrace]
  refine ⟨8718103851046230748232141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5812069234030820498821427 8718103851046230748232141)
  ·
    refine ⟨3269288944142336530587053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8718103851046230748232141 3269288944142336530587053)
    ·
      refine ⟨1225983354053376198970145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3269288944142336530587053 1225983354053376198970145)
      ·
        refine ⟨919487515540032149227609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1225983354053376198970145 919487515540032149227609)
        ·
          refine ⟨689615636655024111920707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 919487515540032149227609 689615636655024111920707)
          ·
            refine ⟨1034423454982536167881061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689615636655024111920707 1034423454982536167881061)
            ·
              refine ⟨193954397809225531477699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1034423454982536167881061 193954397809225531477699)
              ·
                refine ⟨290931596713838297216549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193954397809225531477699 290931596713838297216549)
                ·
                  refine ⟨54549674383844680728103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 290931596713838297216549 54549674383844680728103)
                  ·
                    rfl

theorem cell21_239029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_239029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239029 prefixEnd_239029 := by exact prefixLift 239029
  have htrace : WordTrace (prefixWord ++ tailWord_239029) baseStart_239029 baseEnd_239029 := by
    simpa [prefixWord, tailWord_239029, baseEnd_239029] using wordTrace_append hprefix tailTrace_239029
  have hstable : (prefixWord ++ tailWord_239029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239029).length < 2 ^ (prefixWord ++ tailWord_239029).sum := by decide
  have hdescent : baseEnd_239029 < baseStart_239029 := by decide
  rcases family_descends (prefixWord ++ tailWord_239029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239040 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_239040 : Nat := 118140960795 + 239040 * 2 ^ 59
def prefixEnd_239040 : Nat := 4983230072969 + 3 ^ 40 * 239040 * 2
def baseEnd_239040 : Nat := 54552184733711106044747

theorem tailTrace_239040 : CollatzResearch.WordTrace tailWord_239040 prefixEnd_239040 54552184733711106044747 := by
  unfold tailWord_239040
  simp only [CollatzResearch.WordTrace]
  refine ⟨4359252527003189813441287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5812336702670919751255049 4359252527003189813441287)
  ·
    refine ⟨6538878790504784720161931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4359252527003189813441287 6538878790504784720161931)
    ·
      refine ⟨9808318185757177080242897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6538878790504784720161931 9808318185757177080242897)
      ·
        refine ⟨7356238639317882810182173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9808318185757177080242897 7356238639317882810182173)
        ·
          refine ⟨2758589489744206053818315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7356238639317882810182173 2758589489744206053818315)
          ·
            refine ⟨4137884234616309080727473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758589489744206053818315 4137884234616309080727473)
            ·
              refine ⟨3103413175962231810545605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4137884234616309080727473 3103413175962231810545605)
              ·
                refine ⟨581889970492918464477301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3103413175962231810545605 581889970492918464477301)
                ·
                  refine ⟨54552184733711106044747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 581889970492918464477301 54552184733711106044747)
                  ·
                    rfl

theorem cell21_239040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_239040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239040 prefixEnd_239040 := by exact prefixLift 239040
  have htrace : WordTrace (prefixWord ++ tailWord_239040) baseStart_239040 baseEnd_239040 := by
    simpa [prefixWord, tailWord_239040, baseEnd_239040] using wordTrace_append hprefix tailTrace_239040
  have hstable : (prefixWord ++ tailWord_239040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239040).length < 2 ^ (prefixWord ++ tailWord_239040).sum := by decide
  have hdescent : baseEnd_239040 < baseStart_239040 := by decide
  rcases family_descends (prefixWord ++ tailWord_239040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239133 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 5]
def baseStart_239133 : Nat := 118140960795 + 239133 * 2 ^ 59
def prefixEnd_239133 : Nat := 4983230072969 + 3 ^ 40 * 239133 * 2
def baseEnd_239133 : Nat := 54573408600763610994557

theorem tailTrace_239133 : CollatzResearch.WordTrace tailWord_239133 prefixEnd_239133 54573408600763610994557 := by
  unfold tailWord_239133
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721897042669456510018053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5814598028446304340012035 8721897042669456510018053)
  ·
    refine ⟨1635355695500523095628385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8721897042669456510018053 1635355695500523095628385)
    ·
      refine ⟨1226516771625392321721289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1635355695500523095628385 1226516771625392321721289)
      ·
        refine ⟨919887578719044241290967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1226516771625392321721289 919887578719044241290967)
        ·
          refine ⟨1379831368078566361936451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919887578719044241290967 1379831368078566361936451)
          ·
            refine ⟨2069747052117849542904677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379831368078566361936451 2069747052117849542904677)
            ·
              refine ⟨388077572272096789294627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2069747052117849542904677 388077572272096789294627)
              ·
                refine ⟨582116358408145183941941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388077572272096789294627 582116358408145183941941)
                ·
                  refine ⟨54573408600763610994557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 582116358408145183941941 54573408600763610994557)
                  ·
                    rfl

theorem cell21_239133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_239133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239133 prefixEnd_239133 := by exact prefixLift 239133
  have htrace : WordTrace (prefixWord ++ tailWord_239133) baseStart_239133 baseEnd_239133 := by
    simpa [prefixWord, tailWord_239133, baseEnd_239133] using wordTrace_append hprefix tailTrace_239133
  have hstable : (prefixWord ++ tailWord_239133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239133).length < 2 ^ (prefixWord ++ tailWord_239133).sum := by decide
  have hdescent : baseEnd_239133 < baseStart_239133 := by decide
  rcases family_descends (prefixWord ++ tailWord_239133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239268 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_239268 : Nat := 118140960795 + 239268 * 2 ^ 59
def prefixEnd_239268 : Nat := 4983230072969 + 3 ^ 40 * 239268 * 2
def baseEnd_239268 : Nat := 54604217440033376244281

theorem tailTrace_239268 : CollatzResearch.WordTrace tailWord_239268 prefixEnd_239268 54604217440033376244281 := by
  unfold tailWord_239268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4363410448590187283091229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5817880598120249710788305 4363410448590187283091229)
  ·
    refine ⟨1636278918221320231159211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4363410448590187283091229 1636278918221320231159211)
    ·
      refine ⟨2454418377331980346738817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636278918221320231159211 2454418377331980346738817)
      ·
        refine ⟨1840813782998985260054113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2454418377331980346738817 1840813782998985260054113)
        ·
          refine ⟨1380610337249238945040585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1840813782998985260054113 1380610337249238945040585)
          ·
            refine ⟨1035457752936929208780439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1380610337249238945040585 1035457752936929208780439)
            ·
              refine ⟨1553186629405393813170659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035457752936929208780439 1553186629405393813170659)
              ·
                refine ⟨2329779944108090719755989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553186629405393813170659 2329779944108090719755989)
                ·
                  refine ⟨54604217440033376244281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2329779944108090719755989 54604217440033376244281)
                  ·
                    rfl

theorem cell21_239268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_239268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239268 prefixEnd_239268 := by exact prefixLift 239268
  have htrace : WordTrace (prefixWord ++ tailWord_239268) baseStart_239268 baseEnd_239268 := by
    simpa [prefixWord, tailWord_239268, baseEnd_239268] using wordTrace_append hprefix tailTrace_239268
  have hstable : (prefixWord ++ tailWord_239268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239268).length < 2 ^ (prefixWord ++ tailWord_239268).sum := by decide
  have hdescent : baseEnd_239268 < baseStart_239268 := by decide
  rcases family_descends (prefixWord ++ tailWord_239268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239361 : List Nat := [1, 2, 4, 1, 1, 1, 2, 6, 3]
def baseStart_239361 : Nat := 118140960795 + 239361 * 2 ^ 59
def prefixEnd_239361 : Nat := 4983230072969 + 3 ^ 40 * 239361 * 2
def baseEnd_239361 : Nat := 54625441307085881194091

theorem tailTrace_239361 : CollatzResearch.WordTrace tailWord_239361 prefixEnd_239361 54625441307085881194091 := by
  unfold tailWord_239361
  simp only [CollatzResearch.WordTrace]
  refine ⟨8730212885843451449317937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5820141923895634299545291 8730212885843451449317937)
  ·
    refine ⟨6547659664382588586988453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8730212885843451449317937 6547659664382588586988453)
    ·
      refine ⟨1227686187071735360060335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6547659664382588586988453 1227686187071735360060335)
      ·
        refine ⟨1841529280607603040090503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227686187071735360060335 1841529280607603040090503)
        ·
          refine ⟨2762293920911404560135755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841529280607603040090503 2762293920911404560135755)
          ·
            refine ⟨4143440881367106840203633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762293920911404560135755 4143440881367106840203633)
            ·
              refine ⟨3107580661025330130152725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4143440881367106840203633 3107580661025330130152725)
              ·
                refine ⟨145667843485562349850909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3107580661025330130152725 145667843485562349850909)
                ·
                  refine ⟨54625441307085881194091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145667843485562349850909 54625441307085881194091)
                  ·
                    rfl

theorem cell21_239361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 3].length) (baseStart_239361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239361 prefixEnd_239361 := by exact prefixLift 239361
  have htrace : WordTrace (prefixWord ++ tailWord_239361) baseStart_239361 baseEnd_239361 := by
    simpa [prefixWord, tailWord_239361, baseEnd_239361] using wordTrace_append hprefix tailTrace_239361
  have hstable : (prefixWord ++ tailWord_239361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239361).length < 2 ^ (prefixWord ++ tailWord_239361).sum := by decide
  have hdescent : baseEnd_239361 < baseStart_239361 := by decide
  rcases family_descends (prefixWord ++ tailWord_239361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239406 : List Nat := [4, 1, 3, 2, 2, 9]
def baseStart_239406 : Nat := 118140960795 + 239406 * 2 ^ 59
def prefixEnd_239406 : Nat := 4983230072969 + 3 ^ 40 * 239406 * 2
def baseEnd_239406 : Nat := 2023544848895400109037

theorem tailTrace_239406 : CollatzResearch.WordTrace tailWord_239406 prefixEnd_239406 2023544848895400109037 := by
  unfold tailWord_239406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091481771335053016838259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5821236113786949423137381 1091481771335053016838259)
  ·
    refine ⟨1637222657002579525257389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1091481771335053016838259 1637222657002579525257389)
    ·
      refine ⟨613958496375967321971521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1637222657002579525257389 613958496375967321971521)
      ·
        refine ⟨460468872281975491478641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 613958496375967321971521 460468872281975491478641)
        ·
          refine ⟨345351654211481618608981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460468872281975491478641 345351654211481618608981)
          ·
            refine ⟨2023544848895400109037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 345351654211481618608981 2023544848895400109037)
            ·
              rfl

theorem cell21_239406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 9].length) (baseStart_239406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239406 prefixEnd_239406 := by exact prefixLift 239406
  have htrace : WordTrace (prefixWord ++ tailWord_239406) baseStart_239406 baseEnd_239406 := by
    simpa [prefixWord, tailWord_239406, baseEnd_239406] using wordTrace_append hprefix tailTrace_239406
  have hstable : (prefixWord ++ tailWord_239406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239406).length < 2 ^ (prefixWord ++ tailWord_239406).sum := by decide
  have hdescent : baseEnd_239406 < baseStart_239406 := by decide
  rcases family_descends (prefixWord ++ tailWord_239406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239412 : List Nat := [2, 5, 1, 1, 2, 3, 2, 2, 3]
def baseStart_239412 : Nat := 118140960795 + 239412 * 2 ^ 59
def prefixEnd_239412 : Nat := 4983230072969 + 3 ^ 40 * 239412 * 2
def baseEnd_239412 : Nat := 54637080201921125843987

theorem tailTrace_239412 : CollatzResearch.WordTrace tailWord_239412 prefixEnd_239412 54637080201921125843987 := by
  unfold tailWord_239412
  simp only [CollatzResearch.WordTrace]
  refine ⟨4366036504329343579712245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5821382005772458106282993 4366036504329343579712245)
  ·
    refine ⟨409315922280875960598023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4366036504329343579712245 409315922280875960598023)
    ·
      refine ⟨613973883421313940897035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409315922280875960598023 613973883421313940897035)
      ·
        refine ⟨920960825131970911345553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613973883421313940897035 920960825131970911345553)
        ·
          refine ⟨690720618848978183509165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920960825131970911345553 690720618848978183509165)
          ·
            refine ⟨259020232068366818815937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 690720618848978183509165 259020232068366818815937)
            ·
              refine ⟨194265174051275114111953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259020232068366818815937 194265174051275114111953)
              ·
                refine ⟨145698880538456335583965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194265174051275114111953 145698880538456335583965)
                ·
                  refine ⟨54637080201921125843987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145698880538456335583965 54637080201921125843987)
                  ·
                    rfl

theorem cell21_239412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_239412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239412 prefixEnd_239412 := by exact prefixLift 239412
  have htrace : WordTrace (prefixWord ++ tailWord_239412) baseStart_239412 baseEnd_239412 := by
    simpa [prefixWord, tailWord_239412, baseEnd_239412] using wordTrace_append hprefix tailTrace_239412
  have hstable : (prefixWord ++ tailWord_239412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239412).length < 2 ^ (prefixWord ++ tailWord_239412).sum := by decide
  have hdescent : baseEnd_239412 < baseStart_239412 := by decide
  rcases family_descends (prefixWord ++ tailWord_239412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239423 : List Nat := [1, 1, 2, 2, 7, 1, 1, 6]
def baseStart_239423 : Nat := 118140960795 + 239423 * 2 ^ 59
def prefixEnd_239423 : Nat := 4983230072969 + 3 ^ 40 * 239423 * 2
def baseEnd_239423 : Nat := 18213196850595850386877

theorem tailTrace_239423 : CollatzResearch.WordTrace tailWord_239423 prefixEnd_239423 18213196850595850386877 := by
  unfold tailWord_239423
  simp only [CollatzResearch.WordTrace]
  refine ⟨8732474211618836038074923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5821649474412557358716615 8732474211618836038074923)
  ·
    refine ⟨13098711317428254057112385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8732474211618836038074923 13098711317428254057112385)
    ·
      refine ⟨9824033488071190542834289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13098711317428254057112385 9824033488071190542834289)
      ·
        refine ⟨7368025116053392907125717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9824033488071190542834289 7368025116053392907125717)
        ·
          refine ⟨172688088657501396260759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7368025116053392907125717 172688088657501396260759)
          ·
            refine ⟨259032132986252094391139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172688088657501396260759 259032132986252094391139)
            ·
              refine ⟨388548199479378141586709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259032132986252094391139 388548199479378141586709)
              ·
                refine ⟨18213196850595850386877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 388548199479378141586709 18213196850595850386877)
                ·
                  rfl

theorem cell21_239423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 6].length) (baseStart_239423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239423 prefixEnd_239423 := by exact prefixLift 239423
  have htrace : WordTrace (prefixWord ++ tailWord_239423) baseStart_239423 baseEnd_239423 := by
    simpa [prefixWord, tailWord_239423, baseEnd_239423] using wordTrace_append hprefix tailTrace_239423
  have hstable : (prefixWord ++ tailWord_239423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239423).length < 2 ^ (prefixWord ++ tailWord_239423).sum := by decide
  have hdescent : baseEnd_239423 < baseStart_239423 := by decide
  rcases family_descends (prefixWord ++ tailWord_239423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239437 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 7]
def baseStart_239437 : Nat := 118140960795 + 239437 * 2 ^ 59
def prefixEnd_239437 : Nat := 4983230072969 + 3 ^ 40 * 239437 * 2
def baseEnd_239437 : Nat := 54642785542526637927269

theorem tailTrace_239437 : CollatzResearch.WordTrace tailWord_239437 prefixEnd_239437 54642785542526637927269 := by
  unfold tailWord_239437
  simp only [CollatzResearch.WordTrace]
  refine ⟨8732984833568116429084565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5821989889045410952723043 8732984833568116429084565)
  ·
    refine ⟨409358664073505457613339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8732984833568116429084565 409358664073505457613339)
    ·
      refine ⟨614037996110258186420009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409358664073505457613339 614037996110258186420009)
      ·
        refine ⟨460528497082693639815007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614037996110258186420009 460528497082693639815007)
        ·
          refine ⟨690792745624040459722511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460528497082693639815007 690792745624040459722511)
          ·
            refine ⟨1036189118436060689583767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690792745624040459722511 1036189118436060689583767)
            ·
              refine ⟨1554283677654091034375651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036189118436060689583767 1554283677654091034375651)
              ·
                refine ⟨2331425516481136551563477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554283677654091034375651 2331425516481136551563477)
                ·
                  refine ⟨54642785542526637927269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2331425516481136551563477 54642785542526637927269)
                  ·
                    rfl

theorem cell21_239437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_239437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239437 prefixEnd_239437 := by exact prefixLift 239437
  have htrace : WordTrace (prefixWord ++ tailWord_239437) baseStart_239437 baseEnd_239437 := by
    simpa [prefixWord, tailWord_239437, baseEnd_239437] using wordTrace_append hprefix tailTrace_239437
  have hstable : (prefixWord ++ tailWord_239437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239437).length < 2 ^ (prefixWord ++ tailWord_239437).sum := by decide
  have hdescent : baseEnd_239437 < baseStart_239437 := by decide
  rcases family_descends (prefixWord ++ tailWord_239437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239468 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 4]
def baseStart_239468 : Nat := 118140960795 + 239468 * 2 ^ 59
def prefixEnd_239468 : Nat := 4983230072969 + 3 ^ 40 * 239468 * 2
def baseEnd_239468 : Nat := 54649860164877472910539

theorem tailTrace_239468 : CollatzResearch.WordTrace tailWord_239468 prefixEnd_239468 54649860164877472910539 := by
  unfold tailWord_239468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4367057748227904361731529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5822743664303872482308705 4367057748227904361731529)
  ·
    refine ⟨3275293311170928271298647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4367057748227904361731529 3275293311170928271298647)
    ·
      refine ⟨4912939966756392406947971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3275293311170928271298647 4912939966756392406947971)
      ·
        refine ⟨7369409950134588610421957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912939966756392406947971 7369409950134588610421957)
        ·
          refine ⟨1381764365650235364454117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7369409950134588610421957 1381764365650235364454117)
          ·
            refine ⟨259080818559419130835147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1381764365650235364454117 259080818559419130835147)
            ·
              refine ⟨388621227839128696252721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259080818559419130835147 388621227839128696252721)
              ·
                refine ⟨291465920879346522189541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388621227839128696252721 291465920879346522189541)
                ·
                  refine ⟨54649860164877472910539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291465920879346522189541 54649860164877472910539)
                  ·
                    rfl

theorem cell21_239468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_239468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239468 prefixEnd_239468 := by exact prefixLift 239468
  have htrace : WordTrace (prefixWord ++ tailWord_239468) baseStart_239468 baseEnd_239468 := by
    simpa [prefixWord, tailWord_239468, baseEnd_239468] using wordTrace_append hprefix tailTrace_239468
  have hstable : (prefixWord ++ tailWord_239468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239468).length < 2 ^ (prefixWord ++ tailWord_239468).sum := by decide
  have hdescent : baseEnd_239468 < baseStart_239468 := by decide
  rcases family_descends (prefixWord ++ tailWord_239468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239513 : List Nat := [1, 2, 1, 2, 1, 3, 5, 3, 3]
def baseStart_239513 : Nat := 118140960795 + 239513 * 2 ^ 59
def prefixEnd_239513 : Nat := 4983230072969 + 3 ^ 40 * 239513 * 2
def baseEnd_239513 : Nat := 54660129777967394660447

theorem tailTrace_239513 : CollatzResearch.WordTrace tailWord_239513 prefixEnd_239513 54660129777967394660447 := by
  unfold tailWord_239513
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735756781292781408851193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5823837854195187605900795 8735756781292781408851193)
  ·
    refine ⟨6551817585969586056638395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8735756781292781408851193 6551817585969586056638395)
    ·
      refine ⟨9827726378954379084957593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6551817585969586056638395 9827726378954379084957593)
      ·
        refine ⟨7370794784215784313718195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9827726378954379084957593 7370794784215784313718195)
        ·
          refine ⟨11056192176323676470577293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7370794784215784313718195 11056192176323676470577293)
          ·
            refine ⟨4146072066121378676466485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11056192176323676470577293 4146072066121378676466485)
            ·
              refine ⟨388694256198879250918733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4146072066121378676466485 388694256198879250918733)
              ·
                refine ⟨145760346074579719094525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388694256198879250918733 145760346074579719094525)
                ·
                  refine ⟨54660129777967394660447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145760346074579719094525 54660129777967394660447)
                  ·
                    rfl

theorem cell21_239513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 3].length) (baseStart_239513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239513 prefixEnd_239513 := by exact prefixLift 239513
  have htrace : WordTrace (prefixWord ++ tailWord_239513) baseStart_239513 baseEnd_239513 := by
    simpa [prefixWord, tailWord_239513, baseEnd_239513] using wordTrace_append hprefix tailTrace_239513
  have hstable : (prefixWord ++ tailWord_239513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239513).length < 2 ^ (prefixWord ++ tailWord_239513).sum := by decide
  have hdescent : baseEnd_239513 < baseStart_239513 := by decide
  rcases family_descends (prefixWord ++ tailWord_239513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239527 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 6]
def baseStart_239527 : Nat := 118140960795 + 239527 * 2 ^ 59
def prefixEnd_239527 : Nat := 4983230072969 + 3 ^ 40 * 239527 * 2
def baseEnd_239527 : Nat := 54663324768706481427085

theorem tailTrace_239527 : CollatzResearch.WordTrace tailWord_239527 prefixEnd_239527 54663324768706481427085 := by
  unfold tailWord_239527
  simp only [CollatzResearch.WordTrace]
  refine ⟨8736267403242061799860835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5824178268828041199907223 8736267403242061799860835)
  ·
    refine ⟨13104401104863092699791253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8736267403242061799860835 13104401104863092699791253)
    ·
      refine ⟨614268801790457470302715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13104401104863092699791253 614268801790457470302715)
      ·
        refine ⟨921403202685686205454073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614268801790457470302715 921403202685686205454073)
        ·
          refine ⟨691052402014264654090555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921403202685686205454073 691052402014264654090555)
          ·
            refine ⟨1036578603021396981135833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691052402014264654090555 1036578603021396981135833)
            ·
              refine ⟨777433952266047735851875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1036578603021396981135833 777433952266047735851875)
              ·
                refine ⟨1166150928399071603777813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777433952266047735851875 1166150928399071603777813)
                ·
                  refine ⟨54663324768706481427085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1166150928399071603777813 54663324768706481427085)
                  ·
                    rfl

theorem cell21_239527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_239527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239527 prefixEnd_239527 := by exact prefixLift 239527
  have htrace : WordTrace (prefixWord ++ tailWord_239527) baseStart_239527 baseEnd_239527 := by
    simpa [prefixWord, tailWord_239527, baseEnd_239527] using wordTrace_append hprefix tailTrace_239527
  have hstable : (prefixWord ++ tailWord_239527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239527).length < 2 ^ (prefixWord ++ tailWord_239527).sum := by decide
  have hdescent : baseEnd_239527 < baseStart_239527 := by decide
  rcases family_descends (prefixWord ++ tailWord_239527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239541 : List Nat := [1, 3, 3, 2, 1, 2, 1, 8]
def baseStart_239541 : Nat := 118140960795 + 239541 * 2 ^ 59
def prefixEnd_239541 : Nat := 4983230072969 + 3 ^ 40 * 239541 * 2
def baseEnd_239541 : Nat := 18222173253148522731241

theorem tailTrace_239541 : CollatzResearch.WordTrace tailWord_239541 prefixEnd_239541 18222173253148522731241 := by
  unfold tailWord_239541
  simp only [CollatzResearch.WordTrace]
  refine ⟨8736778025191342190870477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5824518683460894793913651 8736778025191342190870477)
  ·
    refine ⟨3276291759446753321576429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8736778025191342190870477 3276291759446753321576429)
    ·
      refine ⟨1228609409792532495591161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3276291759446753321576429 1228609409792532495591161)
      ·
        refine ⟨921457057344399371693371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1228609409792532495591161 921457057344399371693371)
        ·
          refine ⟨1382185586016599057540057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921457057344399371693371 1382185586016599057540057)
          ·
            refine ⟨1036639189512449293155043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1382185586016599057540057 1036639189512449293155043)
            ·
              refine ⟨1554958784268673939732565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036639189512449293155043 1554958784268673939732565)
              ·
                refine ⟨18222173253148522731241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1554958784268673939732565 18222173253148522731241)
                ·
                  rfl

theorem cell21_239541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 8].length) (baseStart_239541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239541 prefixEnd_239541 := by exact prefixLift 239541
  have htrace : WordTrace (prefixWord ++ tailWord_239541) baseStart_239541 baseEnd_239541 := by
    simpa [prefixWord, tailWord_239541, baseEnd_239541] using wordTrace_append hprefix tailTrace_239541
  have hstable : (prefixWord ++ tailWord_239541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239541).length < 2 ^ (prefixWord ++ tailWord_239541).sum := by decide
  have hdescent : baseEnd_239541 < baseStart_239541 := by decide
  rcases family_descends (prefixWord ++ tailWord_239541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239637 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 4]
def baseStart_239637 : Nat := 118140960795 + 239637 * 2 ^ 59
def prefixEnd_239637 : Nat := 4983230072969 + 3 ^ 40 * 239637 * 2
def baseEnd_239637 : Nat := 54688428267370734593527

theorem tailTrace_239637 : CollatzResearch.WordTrace tailWord_239637 prefixEnd_239637 54688428267370734593527 := by
  unfold tailWord_239637
  simp only [CollatzResearch.WordTrace]
  refine ⟨8740279432843550586365165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5826852955229033724243443 8740279432843550586365165)
  ·
    refine ⟨3277604787316331469886937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8740279432843550586365165 3277604787316331469886937)
    ·
      refine ⟨2458203590487248602415203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3277604787316331469886937 2458203590487248602415203)
      ·
        refine ⟨3687305385730872903622805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2458203590487248602415203 3687305385730872903622805)
        ·
          refine ⟨172842439956134667357319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3687305385730872903622805 172842439956134667357319)
          ·
            refine ⟨259263659934202001035979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172842439956134667357319 259263659934202001035979)
            ·
              refine ⟨388895489901303001553969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259263659934202001035979 388895489901303001553969)
              ·
                refine ⟨291671617425977251165477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388895489901303001553969 291671617425977251165477)
                ·
                  refine ⟨54688428267370734593527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 291671617425977251165477 54688428267370734593527)
                  ·
                    rfl

theorem cell21_239637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_239637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239637 prefixEnd_239637 := by exact prefixLift 239637
  have htrace : WordTrace (prefixWord ++ tailWord_239637) baseStart_239637 baseEnd_239637 := by
    simpa [prefixWord, tailWord_239637, baseEnd_239637] using wordTrace_append hprefix tailTrace_239637
  have hstable : (prefixWord ++ tailWord_239637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239637).length < 2 ^ (prefixWord ++ tailWord_239637).sum := by decide
  have hdescent : baseEnd_239637 < baseStart_239637 := by decide
  rcases family_descends (prefixWord ++ tailWord_239637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239668 : List Nat := [2, 5, 1, 2, 2, 2, 2, 5]
def baseStart_239668 : Nat := 118140960795 + 239668 * 2 ^ 59
def prefixEnd_239668 : Nat := 4983230072969 + 3 ^ 40 * 239668 * 2
def baseEnd_239668 : Nat := 18231834296573856525599

theorem tailTrace_239668 : CollatzResearch.WordTrace tailWord_239668 prefixEnd_239668 18231834296573856525599 := by
  unfold tailWord_239668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4370705047865621440371829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5827606730487495253829105 4370705047865621440371829)
  ·
    refine ⟨409753598237402010034859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4370705047865621440371829 409753598237402010034859)
    ·
      refine ⟨614630397356103015052289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409753598237402010034859 614630397356103015052289)
      ·
        refine ⟨460972798017077261289217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614630397356103015052289 460972798017077261289217)
        ·
          refine ⟨345729598512807945966913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460972798017077261289217 345729598512807945966913)
          ·
            refine ⟨259297198884605959475185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345729598512807945966913 259297198884605959475185)
            ·
              refine ⟨194472899163454469606389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259297198884605959475185 194472899163454469606389)
              ·
                refine ⟨18231834296573856525599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194472899163454469606389 18231834296573856525599)
                ·
                  rfl

theorem cell21_239668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_239668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239668 prefixEnd_239668 := by exact prefixLift 239668
  have htrace : WordTrace (prefixWord ++ tailWord_239668) baseStart_239668 baseEnd_239668 := by
    simpa [prefixWord, tailWord_239668, baseEnd_239668] using wordTrace_append hprefix tailTrace_239668
  have hstable : (prefixWord ++ tailWord_239668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239668).length < 2 ^ (prefixWord ++ tailWord_239668).sum := by decide
  have hdescent : baseEnd_239668 < baseStart_239668 := by decide
  rcases family_descends (prefixWord ++ tailWord_239668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239758 : List Nat := [4, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_239758 : Nat := 118140960795 + 239758 * 2 ^ 59
def prefixEnd_239758 : Nat := 4983230072969 + 3 ^ 40 * 239758 * 2
def baseEnd_239758 : Nat := 54716042115901413076613

theorem tailTrace_239758 : CollatzResearch.WordTrace tailWord_239758 prefixEnd_239758 54716042115901413076613 := by
  unfold tailWord_239758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1093086583175648531439991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5829795110270125501013285 1093086583175648531439991)
  ·
    refine ⟨1639629874763472797159987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1093086583175648531439991 1639629874763472797159987)
    ·
      refine ⟨2459444812145209195739981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1639629874763472797159987 2459444812145209195739981)
      ·
        refine ⟨922291804554453448402493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2459444812145209195739981 922291804554453448402493)
        ·
          refine ⟨345859426707920043150935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 922291804554453448402493 345859426707920043150935)
          ·
            refine ⟨518789140061880064726403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345859426707920043150935 518789140061880064726403)
            ·
              refine ⟨778183710092820097089605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518789140061880064726403 778183710092820097089605)
              ·
                refine ⟨145909445642403768204301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778183710092820097089605 145909445642403768204301)
                ·
                  refine ⟨54716042115901413076613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145909445642403768204301 54716042115901413076613)
                  ·
                    rfl

theorem cell21_239758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_239758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239758 prefixEnd_239758 := by exact prefixLift 239758
  have htrace : WordTrace (prefixWord ++ tailWord_239758) baseStart_239758 baseEnd_239758 := by
    simpa [prefixWord, tailWord_239758, baseEnd_239758] using wordTrace_append hprefix tailTrace_239758
  have hstable : (prefixWord ++ tailWord_239758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239758).length < 2 ^ (prefixWord ++ tailWord_239758).sum := by decide
  have hdescent : baseEnd_239758 < baseStart_239758 := by decide
  rcases family_descends (prefixWord ++ tailWord_239758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239845 : List Nat := [1, 3, 1, 4, 2, 2, 1, 7]
def baseStart_239845 : Nat := 118140960795 + 239845 * 2 ^ 59
def prefixEnd_239845 : Nat := 4983230072969 + 3 ^ 40 * 239845 * 2
def baseEnd_239845 : Nat := 18245298900402865042145

theorem tailTrace_239845 : CollatzResearch.WordTrace tailWord_239845 prefixEnd_239845 18245298900402865042145 := by
  unfold tailWord_239845
  simp only [CollatzResearch.WordTrace]
  refine ⟨8747865816090002109936989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5831910544060001406624659 8747865816090002109936989)
  ·
    refine ⟨3280449681033750791226371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8747865816090002109936989 3280449681033750791226371)
    ·
      refine ⟨4920674521550626186839557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3280449681033750791226371 4920674521550626186839557)
      ·
        refine ⟨922626472790742410032417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4920674521550626186839557 922626472790742410032417)
        ·
          refine ⟨691969854593056807524313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 922626472790742410032417 691969854593056807524313)
          ·
            refine ⟨518977390944792605643235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691969854593056807524313 518977390944792605643235)
            ·
              refine ⟨778466086417188908464853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518977390944792605643235 778466086417188908464853)
              ·
                refine ⟨18245298900402865042145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 778466086417188908464853 18245298900402865042145)
                ·
                  rfl

theorem cell21_239845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 7].length) (baseStart_239845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239845 prefixEnd_239845 := by exact prefixLift 239845
  have htrace : WordTrace (prefixWord ++ tailWord_239845) baseStart_239845 baseEnd_239845 := by
    simpa [prefixWord, tailWord_239845, baseEnd_239845] using wordTrace_append hprefix tailTrace_239845
  have hstable : (prefixWord ++ tailWord_239845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239845).length < 2 ^ (prefixWord ++ tailWord_239845).sum := by decide
  have hdescent : baseEnd_239845 < baseStart_239845 := by decide
  rcases family_descends (prefixWord ++ tailWord_239845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239921 : List Nat := [1, 2, 2, 3, 5, 8]
def baseStart_239921 : Nat := 118140960795 + 239921 * 2 ^ 59
def prefixEnd_239921 : Nat := 4983230072969 + 3 ^ 40 * 239921 * 2
def baseEnd_239921 : Nat := 2027897812468494513319

theorem tailTrace_239921 : CollatzResearch.WordTrace tailWord_239921 prefixEnd_239921 2027897812468494513319 := by
  unfold tailWord_239921
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750637763814667089703617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5833758509209778059802411 8750637763814667089703617)
  ·
    refine ⟨6562978322861000317277713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8750637763814667089703617 6562978322861000317277713)
    ·
      refine ⟨4922233742145750237958285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6562978322861000317277713 4922233742145750237958285)
      ·
        refine ⟨1845837653304656339234357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4922233742145750237958285 1845837653304656339234357)
        ·
          refine ⟨173047279997311531803221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1845837653304656339234357 173047279997311531803221)
          ·
            refine ⟨2027897812468494513319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 173047279997311531803221 2027897812468494513319)
            ·
              rfl

theorem cell21_239921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 8].length) (baseStart_239921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239921 prefixEnd_239921 := by exact prefixLift 239921
  have htrace : WordTrace (prefixWord ++ tailWord_239921) baseStart_239921 baseEnd_239921 := by
    simpa [prefixWord, tailWord_239921, baseEnd_239921] using wordTrace_append hprefix tailTrace_239921
  have hstable : (prefixWord ++ tailWord_239921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239921).length < 2 ^ (prefixWord ++ tailWord_239921).sum := by decide
  have hdescent : baseEnd_239921 < baseStart_239921 := by decide
  rcases family_descends (prefixWord ++ tailWord_239921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239924 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 4]
def baseStart_239924 : Nat := 118140960795 + 239924 * 2 ^ 59
def prefixEnd_239924 : Nat := 4983230072969 + 3 ^ 40 * 239924 * 2
def baseEnd_239924 : Nat := 54753925577522013309607

theorem tailTrace_239924 : CollatzResearch.WordTrace tailWord_239924 prefixEnd_239924 54753925577522013309607 := by
  unfold tailWord_239924
  simp only [CollatzResearch.WordTrace]
  refine ⟨4375373591401899301031413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5833831455202532401375217 4375373591401899301031413)
  ·
    refine ⟨410191274193928059471695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4375373591401899301031413 410191274193928059471695)
    ·
      refine ⟨615286911290892089207543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 410191274193928059471695 615286911290892089207543)
      ·
        refine ⟨922930366936338133811315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 615286911290892089207543 922930366936338133811315)
        ·
          refine ⟨1384395550404507200716973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922930366936338133811315 1384395550404507200716973)
          ·
            refine ⟨519148331401690200268865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1384395550404507200716973 519148331401690200268865)
            ·
              refine ⟨389361248551267650201649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519148331401690200268865 389361248551267650201649)
              ·
                refine ⟨292020936413450737651237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389361248551267650201649 292020936413450737651237)
                ·
                  refine ⟨54753925577522013309607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292020936413450737651237 54753925577522013309607)
                  ·
                    rfl

theorem cell21_239924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_239924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239924 prefixEnd_239924 := by exact prefixLift 239924
  have htrace : WordTrace (prefixWord ++ tailWord_239924) baseStart_239924 baseEnd_239924 := by
    simpa [prefixWord, tailWord_239924, baseEnd_239924] using wordTrace_append hprefix tailTrace_239924
  have hstable : (prefixWord ++ tailWord_239924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239924).length < 2 ^ (prefixWord ++ tailWord_239924).sum := by decide
  have hdescent : baseEnd_239924 < baseStart_239924 := by decide
  rcases family_descends (prefixWord ++ tailWord_239924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239935 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 5]
def baseStart_239935 : Nat := 118140960795 + 239935 * 2 ^ 59
def prefixEnd_239935 : Nat := 4983230072969 + 3 ^ 40 * 239935 * 2
def baseEnd_239935 : Nat := 54756435927388438626251

theorem tailTrace_239935 : CollatzResearch.WordTrace tailWord_239935 prefixEnd_239935 54756435927388438626251 := by
  unfold tailWord_239935
  simp only [CollatzResearch.WordTrace]
  refine ⟨8751148385763947480713259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5834098923842631653808839 8751148385763947480713259)
  ·
    refine ⟨13126722578645921221069889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8751148385763947480713259 13126722578645921221069889)
    ·
      refine ⟨9845041933984440915802417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13126722578645921221069889 9845041933984440915802417)
      ·
        refine ⟨7383781450488330686851813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9845041933984440915802417 7383781450488330686851813)
        ·
          refine ⟨1384459021966562003784715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7383781450488330686851813 1384459021966562003784715)
          ·
            refine ⟨2076688532949843005677073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384459021966562003784715 2076688532949843005677073)
            ·
              refine ⟨1557516399712382254257805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076688532949843005677073 1557516399712382254257805)
              ·
                refine ⟨584068649892143345346677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1557516399712382254257805 584068649892143345346677)
                ·
                  refine ⟨54756435927388438626251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 584068649892143345346677 54756435927388438626251)
                  ·
                    rfl

theorem cell21_239935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_239935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_239935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_239935 prefixEnd_239935 := by exact prefixLift 239935
  have htrace : WordTrace (prefixWord ++ tailWord_239935) baseStart_239935 baseEnd_239935 := by
    simpa [prefixWord, tailWord_239935, baseEnd_239935] using wordTrace_append hprefix tailTrace_239935
  have hstable : (prefixWord ++ tailWord_239935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239935).length < 2 ^ (prefixWord ++ tailWord_239935).sum := by decide
  have hdescent : baseEnd_239935 < baseStart_239935 := by decide
  rcases family_descends (prefixWord ++ tailWord_239935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240011 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 5]
def baseStart_240011 : Nat := 118140960795 + 240011 * 2 ^ 59
def prefixEnd_240011 : Nat := 4983230072969 + 3 ^ 40 * 240011 * 2
def baseEnd_240011 : Nat := 54773780162829195359429

theorem tailTrace_240011 : CollatzResearch.WordTrace tailWord_240011 prefixEnd_240011 54773780162829195359429 := by
  unfold tailWord_240011
  simp only [CollatzResearch.WordTrace]
  refine ⟨8753920333488612460479887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5835946888992408306986591 8753920333488612460479887)
  ·
    refine ⟨13130880500232918690719831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8753920333488612460479887 13130880500232918690719831)
    ·
      refine ⟨19696320750349378036079747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13130880500232918690719831 19696320750349378036079747)
      ·
        refine ⟨29544481125524067054119621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19696320750349378036079747 29544481125524067054119621)
        ·
          refine ⟨5539590211035762572647429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29544481125524067054119621 5539590211035762572647429)
          ·
            refine ⟨1038673164569205482371393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5539590211035762572647429 1038673164569205482371393)
            ·
              refine ⟨779004873426904111778545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038673164569205482371393 779004873426904111778545)
              ·
                refine ⟨584253655070178083833909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779004873426904111778545 584253655070178083833909)
                ·
                  refine ⟨54773780162829195359429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 584253655070178083833909 54773780162829195359429)
                  ·
                    rfl

theorem cell21_240011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_240011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240011 prefixEnd_240011 := by exact prefixLift 240011
  have htrace : WordTrace (prefixWord ++ tailWord_240011) baseStart_240011 baseEnd_240011 := by
    simpa [prefixWord, tailWord_240011, baseEnd_240011] using wordTrace_append hprefix tailTrace_240011
  have hstable : (prefixWord ++ tailWord_240011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240011).length < 2 ^ (prefixWord ++ tailWord_240011).sum := by decide
  have hdescent : baseEnd_240011 < baseStart_240011 := by decide
  rcases family_descends (prefixWord ++ tailWord_240011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240014 : List Nat := [4, 1, 1, 4, 1, 1, 4, 5]
def baseStart_240014 : Nat := 118140960795 + 240014 * 2 ^ 59
def prefixEnd_240014 : Nat := 4983230072969 + 3 ^ 40 * 240014 * 2
def baseEnd_240014 : Nat := 18258154934567285603141

theorem tailTrace_240014 : CollatzResearch.WordTrace tailWord_240014 prefixEnd_240014 18258154934567285603141 := by
  unfold tailWord_240014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1094253719059717996604887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5836019834985162648559397 1094253719059717996604887)
  ·
    refine ⟨1641380578589576994907331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1094253719059717996604887 1641380578589576994907331)
    ·
      refine ⟨2462070867884365492360997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1641380578589576994907331 2462070867884365492360997)
      ·
        refine ⟨461638287728318529817687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2462070867884365492360997 461638287728318529817687)
        ·
          refine ⟨692457431592477794726531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461638287728318529817687 692457431592477794726531)
          ·
            refine ⟨1038686147388716692089797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692457431592477794726531 1038686147388716692089797)
            ·
              refine ⟨194753652635384379766837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1038686147388716692089797 194753652635384379766837)
              ·
                refine ⟨18258154934567285603141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194753652635384379766837 18258154934567285603141)
                ·
                  rfl

theorem cell21_240014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_240014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240014 prefixEnd_240014 := by exact prefixLift 240014
  have htrace : WordTrace (prefixWord ++ tailWord_240014) baseStart_240014 baseEnd_240014 := by
    simpa [prefixWord, tailWord_240014, baseEnd_240014] using wordTrace_append hprefix tailTrace_240014
  have hstable : (prefixWord ++ tailWord_240014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240014).length < 2 ^ (prefixWord ++ tailWord_240014).sum := by decide
  have hdescent : baseEnd_240014 < baseStart_240014 := by decide
  rcases family_descends (prefixWord ++ tailWord_240014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240025 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 8]
def baseStart_240025 : Nat := 118140960795 + 240025 * 2 ^ 59
def prefixEnd_240025 : Nat := 4983230072969 + 3 ^ 40 * 240025 * 2
def baseEnd_240025 : Nat := 54776975153568282126067

theorem tailTrace_240025 : CollatzResearch.WordTrace tailWord_240025 prefixEnd_240025 54776975153568282126067 := by
  unfold tailWord_240025
  simp only [CollatzResearch.WordTrace]
  refine ⟨8754430955437892851489529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5836287303625261900993019 8754430955437892851489529)
  ·
    refine ⟨6565823216578419638617147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8754430955437892851489529 6565823216578419638617147)
    ·
      refine ⟨9848734824867629457925721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6565823216578419638617147 9848734824867629457925721)
      ·
        refine ⟨7386551118650722093444291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9848734824867629457925721 7386551118650722093444291)
        ·
          refine ⟨11079826677976083140166437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7386551118650722093444291 11079826677976083140166437)
          ·
            refine ⟨2077467502120515588781207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11079826677976083140166437 2077467502120515588781207)
            ·
              refine ⟨3116201253180773383171811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077467502120515588781207 3116201253180773383171811)
              ·
                refine ⟨4674301879771160074757717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116201253180773383171811 4674301879771160074757717)
                ·
                  refine ⟨54776975153568282126067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4674301879771160074757717 54776975153568282126067)
                  ·
                    rfl

theorem cell21_240025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_240025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240025 prefixEnd_240025 := by exact prefixLift 240025
  have htrace : WordTrace (prefixWord ++ tailWord_240025) baseStart_240025 baseEnd_240025 := by
    simpa [prefixWord, tailWord_240025, baseEnd_240025] using wordTrace_append hprefix tailTrace_240025
  have hstable : (prefixWord ++ tailWord_240025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240025).length < 2 ^ (prefixWord ++ tailWord_240025).sum := by decide
  have hdescent : baseEnd_240025 < baseStart_240025 := by decide
  rcases family_descends (prefixWord ++ tailWord_240025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240163 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 5]
def baseStart_240163 : Nat := 118140960795 + 240163 * 2 ^ 59
def prefixEnd_240163 : Nat := 4983230072969 + 3 ^ 40 * 240163 * 2
def baseEnd_240163 : Nat := 54808468633710708825785

theorem tailTrace_240163 : CollatzResearch.WordTrace tailWord_240163 prefixEnd_240163 54808468633710708825785 := by
  unfold tailWord_240163
  simp only [CollatzResearch.WordTrace]
  refine ⟨8759464228937942420013143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5839642819291961613342095 8759464228937942420013143)
  ·
    refine ⟨13139196343406913630019715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8759464228937942420013143 13139196343406913630019715)
    ·
      refine ⟨19708794515110370445029573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13139196343406913630019715 19708794515110370445029573)
      ·
        refine ⟨3695398971583194458443045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19708794515110370445029573 3695398971583194458443045)
        ·
          refine ⟨692887307171848960958071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3695398971583194458443045 692887307171848960958071)
          ·
            refine ⟨1039330960757773441437107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692887307171848960958071 1039330960757773441437107)
            ·
              refine ⟨1558996441136660162155661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039330960757773441437107 1558996441136660162155661)
              ·
                refine ⟨584623665426247560808373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1558996441136660162155661 584623665426247560808373)
                ·
                  refine ⟨54808468633710708825785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 584623665426247560808373 54808468633710708825785)
                  ·
                    rfl

theorem cell21_240163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_240163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240163 prefixEnd_240163 := by exact prefixLift 240163
  have htrace : WordTrace (prefixWord ++ tailWord_240163) baseStart_240163 baseEnd_240163 := by
    simpa [prefixWord, tailWord_240163, baseEnd_240163] using wordTrace_append hprefix tailTrace_240163
  have hstable : (prefixWord ++ tailWord_240163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240163).length < 2 ^ (prefixWord ++ tailWord_240163).sum := by decide
  have hdescent : baseEnd_240163 < baseStart_240163 := by decide
  rcases family_descends (prefixWord ++ tailWord_240163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240197 : List Nat := [1, 3, 1, 1, 1, 7, 1, 3, 3]
def baseStart_240197 : Nat := 118140960795 + 240197 * 2 ^ 59
def prefixEnd_240197 : Nat := 4983230072969 + 3 ^ 40 * 240197 * 2
def baseEnd_240197 : Nat := 54816227896934205259049

theorem tailTrace_240197 : CollatzResearch.WordTrace tailWord_240197 prefixEnd_240197 54816227896934205259049 := by
  unfold tailWord_240197
  simp only [CollatzResearch.WordTrace]
  refine ⟨8760704310814766226750845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5840469540543177484500563 8760704310814766226750845)
  ·
    refine ⟨3285264116555537335031567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8760704310814766226750845 3285264116555537335031567)
    ·
      refine ⟨4927896174833306002547351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3285264116555537335031567 4927896174833306002547351)
      ·
        refine ⟨7391844262249959003821027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927896174833306002547351 7391844262249959003821027)
        ·
          refine ⟨11087766393374938505731541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7391844262249959003821027 11087766393374938505731541)
          ·
            refine ⟨259869524844725121228083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11087766393374938505731541 259869524844725121228083)
            ·
              refine ⟨389804287267087681842125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259869524844725121228083 389804287267087681842125)
              ·
                refine ⟨146176607725157880690797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389804287267087681842125 146176607725157880690797)
                ·
                  refine ⟨54816227896934205259049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146176607725157880690797 54816227896934205259049)
                  ·
                    rfl

theorem cell21_240197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_240197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240197 prefixEnd_240197 := by exact prefixLift 240197
  have htrace : WordTrace (prefixWord ++ tailWord_240197) baseStart_240197 baseEnd_240197 := by
    simpa [prefixWord, tailWord_240197, baseEnd_240197] using wordTrace_append hprefix tailTrace_240197
  have hstable : (prefixWord ++ tailWord_240197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240197).length < 2 ^ (prefixWord ++ tailWord_240197).sum := by decide
  have hdescent : baseEnd_240197 < baseStart_240197 := by decide
  rcases family_descends (prefixWord ++ tailWord_240197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240321 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 4]
def baseStart_240321 : Nat := 118140960795 + 240321 * 2 ^ 59
def prefixEnd_240321 : Nat := 4983230072969 + 3 ^ 40 * 240321 * 2
def baseEnd_240321 : Nat := 54844526386337545192129

theorem tailTrace_240321 : CollatzResearch.WordTrace tailWord_240321 prefixEnd_240321 54844526386337545192129 := by
  unfold tailWord_240321
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765226962365535404264817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5843484641577023602843211 8765226962365535404264817)
  ·
    refine ⟨6573920221774151553198613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8765226962365535404264817 6573920221774151553198613)
    ·
      refine ⟨308152510395663354056185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6573920221774151553198613 308152510395663354056185)
      ·
        refine ⟨231114382796747515542139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308152510395663354056185 231114382796747515542139)
        ·
          refine ⟨346671574195121273313209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231114382796747515542139 346671574195121273313209)
          ·
            refine ⟨260003680646340954984907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346671574195121273313209 260003680646340954984907)
            ·
              refine ⟨390005520969511432477361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260003680646340954984907 390005520969511432477361)
              ·
                refine ⟨292504140727133574358021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390005520969511432477361 292504140727133574358021)
                ·
                  refine ⟨54844526386337545192129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292504140727133574358021 54844526386337545192129)
                  ·
                    rfl

theorem cell21_240321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_240321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240321 prefixEnd_240321 := by exact prefixLift 240321
  have htrace : WordTrace (prefixWord ++ tailWord_240321) baseStart_240321 baseEnd_240321 := by
    simpa [prefixWord, tailWord_240321, baseEnd_240321] using wordTrace_append hprefix tailTrace_240321
  have hstable : (prefixWord ++ tailWord_240321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240321).length < 2 ^ (prefixWord ++ tailWord_240321).sum := by decide
  have hdescent : baseEnd_240321 < baseStart_240321 := by decide
  rcases family_descends (prefixWord ++ tailWord_240321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240332 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 5]
def baseStart_240332 : Nat := 118140960795 + 240332 * 2 ^ 59
def prefixEnd_240332 : Nat := 4983230072969 + 3 ^ 40 * 240332 * 2
def baseEnd_240332 : Nat := 54847036736203970508773

theorem tailTrace_240332 : CollatzResearch.WordTrace tailWord_240332 prefixEnd_240332 54847036736203970508773 := by
  unfold tailWord_240332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4382814082662842141457625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5843752110217122855276833 4382814082662842141457625)
  ·
    refine ⟨3287110561997131606093219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4382814082662842141457625 3287110561997131606093219)
    ·
      refine ⟨4930665842995697409139829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287110561997131606093219 4930665842995697409139829)
      ·
        refine ⟨462249922780846632106859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4930665842995697409139829 462249922780846632106859)
        ·
          refine ⟨693374884171269948160289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462249922780846632106859 693374884171269948160289)
          ·
            refine ⟨520031163128452461120217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693374884171269948160289 520031163128452461120217)
            ·
              refine ⟨390023372346339345840163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520031163128452461120217 390023372346339345840163)
              ·
                refine ⟨585035058519509018760245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390023372346339345840163 585035058519509018760245)
                ·
                  refine ⟨54847036736203970508773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 585035058519509018760245 54847036736203970508773)
                  ·
                    rfl

theorem cell21_240332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_240332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240332 prefixEnd_240332 := by exact prefixLift 240332
  have htrace : WordTrace (prefixWord ++ tailWord_240332) baseStart_240332 baseEnd_240332 := by
    simpa [prefixWord, tailWord_240332, baseEnd_240332] using wordTrace_append hprefix tailTrace_240332
  have hstable : (prefixWord ++ tailWord_240332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240332).length < 2 ^ (prefixWord ++ tailWord_240332).sum := by decide
  have hdescent : baseEnd_240332 < baseStart_240332 := by decide
  rcases family_descends (prefixWord ++ tailWord_240332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240436 : List Nat := [2, 5, 1, 1, 12]
def baseStart_240436 : Nat := 118140960795 + 240436 * 2 ^ 59
def prefixEnd_240436 : Nat := 4983230072969 + 3 ^ 40 * 240436 * 2
def baseEnd_240436 : Nat := 677416925347196305867

theorem tailTrace_240436 : CollatzResearch.WordTrace tailWord_240436 prefixEnd_240436 677416925347196305867 := by
  unfold tailWord_240436
  simp only [CollatzResearch.WordTrace]
  refine ⟨4384710678474455022350581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5846280904632606696467441 4384710678474455022350581)
  ·
    refine ⟨411066626106980158345367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4384710678474455022350581 411066626106980158345367)
    ·
      refine ⟨616599939160470237518051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411066626106980158345367 616599939160470237518051)
      ·
        refine ⟨924899908740705356277077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616599939160470237518051 924899908740705356277077)
        ·
          refine ⟨677416925347196305867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 924899908740705356277077 677416925347196305867)
          ·
            rfl

theorem cell21_240436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 12].length) (baseStart_240436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240436 prefixEnd_240436 := by exact prefixLift 240436
  have htrace : WordTrace (prefixWord ++ tailWord_240436) baseStart_240436 baseEnd_240436 := by
    simpa [prefixWord, tailWord_240436, baseEnd_240436] using wordTrace_append hprefix tailTrace_240436
  have hstable : (prefixWord ++ tailWord_240436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240436).length < 2 ^ (prefixWord ++ tailWord_240436).sum := by decide
  have hdescent : baseEnd_240436 < baseStart_240436 := by decide
  rcases family_descends (prefixWord ++ tailWord_240436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240442 : List Nat := [3, 1, 1, 1, 6, 2, 2, 2, 3]
def baseStart_240442 : Nat := 118140960795 + 240442 * 2 ^ 59
def prefixEnd_240442 : Nat := 4983230072969 + 3 ^ 40 * 240442 * 2
def baseEnd_240442 : Nat := 54872140234868223675215

theorem tailTrace_240442 : CollatzResearch.WordTrace tailWord_240442 prefixEnd_240442 54872140234868223675215 := by
  unfold tailWord_240442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192410048731793267354895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5846426796618115379613053 2192410048731793267354895)
  ·
    refine ⟨3288615073097689901032343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2192410048731793267354895 3288615073097689901032343)
    ·
      refine ⟨4932922609646534851548515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3288615073097689901032343 4932922609646534851548515)
      ·
        refine ⟨7399383914469802277322773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932922609646534851548515 7399383914469802277322773)
        ·
          refine ⟨346846120990771981749505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7399383914469802277322773 346846120990771981749505)
          ·
            refine ⟨260134590743078986312129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346846120990771981749505 260134590743078986312129)
            ·
              refine ⟨195100943057309239734097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260134590743078986312129 195100943057309239734097)
              ·
                refine ⟨146325707292981929800573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195100943057309239734097 146325707292981929800573)
                ·
                  refine ⟨54872140234868223675215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146325707292981929800573 54872140234868223675215)
                  ·
                    rfl

theorem cell21_240442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_240442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240442 prefixEnd_240442 := by exact prefixLift 240442
  have htrace : WordTrace (prefixWord ++ tailWord_240442) baseStart_240442 baseEnd_240442 := by
    simpa [prefixWord, tailWord_240442, baseEnd_240442] using wordTrace_append hprefix tailTrace_240442
  have hstable : (prefixWord ++ tailWord_240442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240442).length < 2 ^ (prefixWord ++ tailWord_240442).sum := by decide
  have hdescent : baseEnd_240442 < baseStart_240442 := by decide
  rcases family_descends (prefixWord ++ tailWord_240442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240484 : List Nat := [2, 3, 1, 1, 4, 1, 1, 5, 3]
def baseStart_240484 : Nat := 118140960795 + 240484 * 2 ^ 59
def prefixEnd_240484 : Nat := 4983230072969 + 3 ^ 40 * 240484 * 2
def baseEnd_240484 : Nat := 54881725207085483975129

theorem tailTrace_240484 : CollatzResearch.WordTrace tailWord_240484 prefixEnd_240484 54881725207085483975129 := by
  unfold tailWord_240484
  simp only [CollatzResearch.WordTrace]
  refine ⟨4385586030387507121224253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5847448040516676161632337 4385586030387507121224253)
  ·
    refine ⟨1644594761395315170459095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4385586030387507121224253 1644594761395315170459095)
    ·
      refine ⟨2466892142092972755688643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644594761395315170459095 2466892142092972755688643)
      ·
        refine ⟨3700338213139459133532965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2466892142092972755688643 3700338213139459133532965)
        ·
          refine ⟨693813414963648587537431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3700338213139459133532965 693813414963648587537431)
          ·
            refine ⟨1040720122445472881306147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693813414963648587537431 1040720122445472881306147)
            ·
              refine ⟨1561080183668209321959221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040720122445472881306147 1561080183668209321959221)
              ·
                refine ⟨146351267218894623933677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1561080183668209321959221 146351267218894623933677)
                ·
                  refine ⟨54881725207085483975129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146351267218894623933677 54881725207085483975129)
                  ·
                    rfl

theorem cell21_240484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_240484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240484 prefixEnd_240484 := by exact prefixLift 240484
  have htrace : WordTrace (prefixWord ++ tailWord_240484) baseStart_240484 baseEnd_240484 := by
    simpa [prefixWord, tailWord_240484, baseEnd_240484] using wordTrace_append hprefix tailTrace_240484
  have hstable : (prefixWord ++ tailWord_240484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240484).length < 2 ^ (prefixWord ++ tailWord_240484).sum := by decide
  have hdescent : baseEnd_240484 < baseStart_240484 := by decide
  rcases family_descends (prefixWord ++ tailWord_240484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240498 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_240498 : Nat := 118140960795 + 240498 * 2 ^ 59
def prefixEnd_240498 : Nat := 4983230072969 + 3 ^ 40 * 240498 * 2
def baseEnd_240498 : Nat := 54884920197824570741767

theorem tailTrace_240498 : CollatzResearch.WordTrace tailWord_240498 prefixEnd_240498 54884920197824570741767 := by
  unfold tailWord_240498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192920670681073658364537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5847788455149529755638765 2192920670681073658364537)
  ·
    refine ⟨1644690503010805243773403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2192920670681073658364537 1644690503010805243773403)
    ·
      refine ⟨2467035754516207865660105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1644690503010805243773403 2467035754516207865660105)
      ·
        refine ⟨1850276815887155899245079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2467035754516207865660105 1850276815887155899245079)
        ·
          refine ⟨2775415223830733848867619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850276815887155899245079 2775415223830733848867619)
          ·
            refine ⟨4163122835746100773301429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775415223830733848867619 4163122835746100773301429)
            ·
              refine ⟨390292765851196947497009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4163122835746100773301429 390292765851196947497009)
              ·
                refine ⟨292719574388397710622757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390292765851196947497009 292719574388397710622757)
                ·
                  refine ⟨54884920197824570741767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292719574388397710622757 54884920197824570741767)
                  ·
                    rfl

theorem cell21_240498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_240498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240498 prefixEnd_240498 := by exact prefixLift 240498
  have htrace : WordTrace (prefixWord ++ tailWord_240498) baseStart_240498 baseEnd_240498 := by
    simpa [prefixWord, tailWord_240498, baseEnd_240498] using wordTrace_append hprefix tailTrace_240498
  have hstable : (prefixWord ++ tailWord_240498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240498).length < 2 ^ (prefixWord ++ tailWord_240498).sum := by decide
  have hdescent : baseEnd_240498 < baseStart_240498 := by decide
  rcases family_descends (prefixWord ++ tailWord_240498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240574 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_240574 : Nat := 118140960795 + 240574 * 2 ^ 59
def prefixEnd_240574 : Nat := 4983230072969 + 3 ^ 40 * 240574 * 2
def baseEnd_240574 : Nat := 54902264433265327474945

theorem tailTrace_240574 : CollatzResearch.WordTrace tailWord_240574 prefixEnd_240574 54902264433265327474945 := by
  unfold tailWord_240574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096806828806119951653097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5849636420299306408816517 1096806828806119951653097)
  ·
    refine ⟨822605121604589963739823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1096806828806119951653097 822605121604589963739823)
    ·
      refine ⟨1233907682406884945609735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822605121604589963739823 1233907682406884945609735)
      ·
        refine ⟨1850861523610327418414603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233907682406884945609735 1850861523610327418414603)
        ·
          refine ⟨2776292285415491127621905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850861523610327418414603 2776292285415491127621905)
          ·
            refine ⟨2082219214061618345716429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2776292285415491127621905 2082219214061618345716429)
            ·
              refine ⟨780832205273106879643661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2082219214061618345716429 780832205273106879643661)
              ·
                refine ⟨292812076977415079866373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 780832205273106879643661 292812076977415079866373)
                ·
                  refine ⟨54902264433265327474945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292812076977415079866373 54902264433265327474945)
                  ·
                    rfl

theorem cell21_240574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_240574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240574 prefixEnd_240574 := by exact prefixLift 240574
  have htrace : WordTrace (prefixWord ++ tailWord_240574) baseStart_240574 baseEnd_240574 := by
    simpa [prefixWord, tailWord_240574, baseEnd_240574] using wordTrace_append hprefix tailTrace_240574
  have hstable : (prefixWord ++ tailWord_240574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240574).length < 2 ^ (prefixWord ++ tailWord_240574).sum := by decide
  have hdescent : baseEnd_240574 < baseStart_240574 := by decide
  rcases family_descends (prefixWord ++ tailWord_240574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240622 : List Nat := [4, 1, 2, 1, 5, 1, 1, 6]
def baseStart_240622 : Nat := 118140960795 + 240622 * 2 ^ 59
def prefixEnd_240622 : Nat := 4983230072969 + 3 ^ 40 * 240622 * 2
def baseEnd_240622 : Nat := 18304406229075970224949

theorem tailTrace_240622 : CollatzResearch.WordTrace tailWord_240622 prefixEnd_240622 18304406229075970224949 := by
  unfold tailWord_240622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1097025666784382976371515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5850803556183375873981413 1097025666784382976371515)
  ·
    refine ⟨1645538500176574464557273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1097025666784382976371515 1645538500176574464557273)
    ·
      refine ⟨1234153875132430848417955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1645538500176574464557273 1234153875132430848417955)
      ·
        refine ⟨1851230812698646272626933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234153875132430848417955 1851230812698646272626933)
        ·
          refine ⟨173552888690498088058775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1851230812698646272626933 173552888690498088058775)
          ·
            refine ⟨260329333035747132088163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173552888690498088058775 260329333035747132088163)
            ·
              refine ⟨390493999553620698132245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260329333035747132088163 390493999553620698132245)
              ·
                refine ⟨18304406229075970224949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 390493999553620698132245 18304406229075970224949)
                ·
                  rfl

theorem cell21_240622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_240622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240622 prefixEnd_240622 := by exact prefixLift 240622
  have htrace : WordTrace (prefixWord ++ tailWord_240622) baseStart_240622 baseEnd_240622 := by
    simpa [prefixWord, tailWord_240622, baseEnd_240622] using wordTrace_append hprefix tailTrace_240622
  have hstable : (prefixWord ++ tailWord_240622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240622).length < 2 ^ (prefixWord ++ tailWord_240622).sum := by decide
  have hdescent : baseEnd_240622 < baseStart_240622 := by decide
  rcases family_descends (prefixWord ++ tailWord_240622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240633 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 4]
def baseStart_240633 : Nat := 118140960795 + 240633 * 2 ^ 59
def prefixEnd_240633 : Nat := 4983230072969 + 3 ^ 40 * 240633 * 2
def baseEnd_240633 : Nat := 54915729037094335991491

theorem tailTrace_240633 : CollatzResearch.WordTrace tailWord_240633 prefixEnd_240633 54915729037094335991491 := by
  unfold tailWord_240633
  simp only [CollatzResearch.WordTrace]
  refine ⟨8776606537235212689622553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5851071024823475126415035 8776606537235212689622553)
  ·
    refine ⟨6582454902926409517216915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8776606537235212689622553 6582454902926409517216915)
    ·
      refine ⟨9873682354389614275825373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6582454902926409517216915 9873682354389614275825373)
      ·
        refine ⟨3702630882896105353434515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9873682354389614275825373 3702630882896105353434515)
        ·
          refine ⟨5553946324344158030151773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3702630882896105353434515 5553946324344158030151773)
          ·
            refine ⟨2082729871629059261306915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5553946324344158030151773 2082729871629059261306915)
            ·
              refine ⟨3124094807443588891960373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082729871629059261306915 3124094807443588891960373)
              ·
                refine ⟨292883888197836458621285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3124094807443588891960373 292883888197836458621285)
                ·
                  refine ⟨54915729037094335991491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 292883888197836458621285 54915729037094335991491)
                  ·
                    rfl

theorem cell21_240633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_240633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240633 prefixEnd_240633 := by exact prefixLift 240633
  have htrace : WordTrace (prefixWord ++ tailWord_240633) baseStart_240633 baseEnd_240633 := by
    simpa [prefixWord, tailWord_240633, baseEnd_240633] using wordTrace_append hprefix tailTrace_240633
  have hstable : (prefixWord ++ tailWord_240633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240633).length < 2 ^ (prefixWord ++ tailWord_240633).sum := by decide
  have hdescent : baseEnd_240633 < baseStart_240633 := by decide
  rcases family_descends (prefixWord ++ tailWord_240633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240743 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 4]
def baseStart_240743 : Nat := 118140960795 + 240743 * 2 ^ 59
def prefixEnd_240743 : Nat := 4983230072969 + 3 ^ 40 * 240743 * 2
def baseEnd_240743 : Nat := 54940832535758589157933

theorem tailTrace_240743 : CollatzResearch.WordTrace tailWord_240743 prefixEnd_240743 54940832535758589157933 := by
  unfold tailWord_240743
  simp only [CollatzResearch.WordTrace]
  refine ⟨8780618566836701476126883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5853745711224467650751255 8780618566836701476126883)
  ·
    refine ⟨13170927850255052214190325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8780618566836701476126883 13170927850255052214190325)
    ·
      refine ⟨1234774485961411145080343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13170927850255052214190325 1234774485961411145080343)
      ·
        refine ⟨1852161728942116717620515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234774485961411145080343 1852161728942116717620515)
        ·
          refine ⟨2778242593413175076430773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852161728942116717620515 2778242593413175076430773)
          ·
            refine ⟨260460243132485163415385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2778242593413175076430773 260460243132485163415385)
            ·
              refine ⟨195345182349363872561539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260460243132485163415385 195345182349363872561539)
              ·
                refine ⟨293017773524045808842309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195345182349363872561539 293017773524045808842309)
                ·
                  refine ⟨54940832535758589157933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293017773524045808842309 54940832535758589157933)
                  ·
                    rfl

theorem cell21_240743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 4].length) (baseStart_240743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240743 prefixEnd_240743 := by exact prefixLift 240743
  have htrace : WordTrace (prefixWord ++ tailWord_240743) baseStart_240743 baseEnd_240743 := by
    simpa [prefixWord, tailWord_240743, baseEnd_240743] using wordTrace_append hprefix tailTrace_240743
  have hstable : (prefixWord ++ tailWord_240743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240743).length < 2 ^ (prefixWord ++ tailWord_240743).sum := by decide
  have hdescent : baseEnd_240743 < baseStart_240743 := by decide
  rcases family_descends (prefixWord ++ tailWord_240743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240754 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_240754 : Nat := 118140960795 + 240754 * 2 ^ 59
def prefixEnd_240754 : Nat := 4983230072969 + 3 ^ 40 * 240754 * 2
def baseEnd_240754 : Nat := 54943342885625014474577

theorem tailTrace_240754 : CollatzResearch.WordTrace tailWord_240754 prefixEnd_240754 54943342885625014474577 := by
  unfold tailWord_240754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195254942449212588694329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5854013179864566903184877 2195254942449212588694329)
  ·
    refine ⟨1646441206836909441520747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2195254942449212588694329 1646441206836909441520747)
    ·
      refine ⟨2469661810255364162281121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1646441206836909441520747 2469661810255364162281121)
      ·
        refine ⟨1852246357691523121710841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2469661810255364162281121 1852246357691523121710841)
        ·
          refine ⟨1389184768268642341283131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852246357691523121710841 1389184768268642341283131)
          ·
            refine ⟨2083777152402963511924697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389184768268642341283131 2083777152402963511924697)
            ·
              refine ⟨1562832864302222633943523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083777152402963511924697 1562832864302222633943523)
              ·
                refine ⟨2344249296453333950915285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562832864302222633943523 2344249296453333950915285)
                ·
                  refine ⟨54943342885625014474577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2344249296453333950915285 54943342885625014474577)
                  ·
                    rfl

theorem cell21_240754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_240754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240754 prefixEnd_240754 := by exact prefixLift 240754
  have htrace : WordTrace (prefixWord ++ tailWord_240754) baseStart_240754 baseEnd_240754 := by
    simpa [prefixWord, tailWord_240754, baseEnd_240754] using wordTrace_append hprefix tailTrace_240754
  have hstable : (prefixWord ++ tailWord_240754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240754).length < 2 ^ (prefixWord ++ tailWord_240754).sum := by decide
  have hdescent : baseEnd_240754 < baseStart_240754 := by decide
  rcases family_descends (prefixWord ++ tailWord_240754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240768 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_240768 : Nat := 118140960795 + 240768 * 2 ^ 59
def prefixEnd_240768 : Nat := 4983230072969 + 3 ^ 40 * 240768 * 2
def baseEnd_240768 : Nat := 54946537876364101241215

theorem tailTrace_240768 : CollatzResearch.WordTrace tailWord_240768 prefixEnd_240768 54946537876364101241215 := by
  unfold tailWord_240768
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390765195873065372893479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5854353594497420497191305 4390765195873065372893479)
  ·
    refine ⟨6586147793809598059340219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4390765195873065372893479 6586147793809598059340219)
    ·
      refine ⟨9879221690714397089010329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6586147793809598059340219 9879221690714397089010329)
      ·
        refine ⟨7409416268035797816757747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9879221690714397089010329 7409416268035797816757747)
        ·
          refine ⟨11114124402053696725136621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7409416268035797816757747 11114124402053696725136621)
          ·
            refine ⟨4167796650770136271926233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11114124402053696725136621 4167796650770136271926233)
            ·
              refine ⟨3125847488077602203944675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4167796650770136271926233 3125847488077602203944675)
              ·
                refine ⟨4688771232116403305917013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3125847488077602203944675 4688771232116403305917013)
                ·
                  refine ⟨54946537876364101241215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4688771232116403305917013 54946537876364101241215)
                  ·
                    rfl

theorem cell21_240768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_240768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240768 prefixEnd_240768 := by exact prefixLift 240768
  have htrace : WordTrace (prefixWord ++ tailWord_240768) baseStart_240768 baseEnd_240768 := by
    simpa [prefixWord, tailWord_240768, baseEnd_240768] using wordTrace_append hprefix tailTrace_240768
  have hstable : (prefixWord ++ tailWord_240768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240768).length < 2 ^ (prefixWord ++ tailWord_240768).sum := by decide
  have hdescent : baseEnd_240768 < baseStart_240768 := by decide
  rcases family_descends (prefixWord ++ tailWord_240768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240771 : List Nat := [1, 1, 1, 3, 3, 2, 2, 5, 3]
def baseStart_240771 : Nat := 118140960795 + 240771 * 2 ^ 59
def prefixEnd_240771 : Nat := 4983230072969 + 3 ^ 40 * 240771 * 2
def baseEnd_240771 : Nat := 54947222517236762691209

theorem tailTrace_240771 : CollatzResearch.WordTrace tailWord_240771 prefixEnd_240771 54947222517236762691209 := by
  unfold tailWord_240771
  simp only [CollatzResearch.WordTrace]
  refine ⟨8781639810735262258146167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5854426540490174838764111 8781639810735262258146167)
  ·
    refine ⟨13172459716102893387219251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8781639810735262258146167 13172459716102893387219251)
    ·
      refine ⟨19758689574154340080828877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13172459716102893387219251 19758689574154340080828877)
      ·
        refine ⟨7409508590307877530310829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19758689574154340080828877 7409508590307877530310829)
        ·
          refine ⟨2778565721365454073866561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7409508590307877530310829 2778565721365454073866561)
          ·
            refine ⟨2083924291024090555399921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2778565721365454073866561 2083924291024090555399921)
            ·
              refine ⟨1562943218268067916549941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083924291024090555399921 1562943218268067916549941)
              ·
                refine ⟨146525926712631367176557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1562943218268067916549941 146525926712631367176557)
                ·
                  refine ⟨54947222517236762691209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146525926712631367176557 54947222517236762691209)
                  ·
                    rfl

theorem cell21_240771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 3].length) (baseStart_240771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240771 prefixEnd_240771 := by exact prefixLift 240771
  have htrace : WordTrace (prefixWord ++ tailWord_240771) baseStart_240771 baseEnd_240771 := by
    simpa [prefixWord, tailWord_240771, baseEnd_240771] using wordTrace_append hprefix tailTrace_240771
  have hstable : (prefixWord ++ tailWord_240771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240771).length < 2 ^ (prefixWord ++ tailWord_240771).sum := by decide
  have hdescent : baseEnd_240771 < baseStart_240771 := by decide
  rcases family_descends (prefixWord ++ tailWord_240771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240836 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 4]
def baseStart_240836 : Nat := 118140960795 + 240836 * 2 ^ 59
def prefixEnd_240836 : Nat := 4983230072969 + 3 ^ 40 * 240836 * 2
def baseEnd_240836 : Nat := 54962056402811094107743

theorem tailTrace_240836 : CollatzResearch.WordTrace tailWord_240836 prefixEnd_240836 54962056402811094107743 := by
  unfold tailWord_240836
  simp only [CollatzResearch.WordTrace]
  refine ⟨4392005277749889179631181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5856007036999852239508241 4392005277749889179631181)
  ·
    refine ⟨1647001979156208442361693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4392005277749889179631181 1647001979156208442361693)
    ·
      refine ⟨617625742183578165885635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1647001979156208442361693 617625742183578165885635)
      ·
        refine ⟨926438613275367248828453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617625742183578165885635 926438613275367248828453)
        ·
          refine ⟨173707239989131359155335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 926438613275367248828453 173707239989131359155335)
          ·
            refine ⟨260560859983697038733003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173707239989131359155335 260560859983697038733003)
            ·
              refine ⟨390841289975545558099505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260560859983697038733003 390841289975545558099505)
              ·
                refine ⟨293130967481659168574629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390841289975545558099505 293130967481659168574629)
                ·
                  refine ⟨54962056402811094107743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293130967481659168574629 54962056402811094107743)
                  ·
                    rfl

theorem cell21_240836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_240836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240836 prefixEnd_240836 := by exact prefixLift 240836
  have htrace : WordTrace (prefixWord ++ tailWord_240836) baseStart_240836 baseEnd_240836 := by
    simpa [prefixWord, tailWord_240836, baseEnd_240836] using wordTrace_append hprefix tailTrace_240836
  have hstable : (prefixWord ++ tailWord_240836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240836).length < 2 ^ (prefixWord ++ tailWord_240836).sum := by decide
  have hdescent : baseEnd_240836 < baseStart_240836 := by decide
  rcases family_descends (prefixWord ++ tailWord_240836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240875 : List Nat := [1, 1, 1, 1, 2, 7, 1, 7]
def baseStart_240875 : Nat := 118140960795 + 240875 * 2 ^ 59
def prefixEnd_240875 : Nat := 4983230072969 + 3 ^ 40 * 240875 * 2
def baseEnd_240875 : Nat := 18323652244718564319221

theorem tailTrace_240875 : CollatzResearch.WordTrace tailWord_240875 prefixEnd_240875 18323652244718564319221 := by
  unfold tailWord_240875
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785433002358488019932079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5856955334905658679954719 8785433002358488019932079)
  ·
    refine ⟨13178149503537732029898119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8785433002358488019932079 13178149503537732029898119)
    ·
      refine ⟨19767224255306598044847179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13178149503537732029898119 19767224255306598044847179)
      ·
        refine ⟨29650836382959897067270769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19767224255306598044847179 29650836382959897067270769)
        ·
          refine ⟨22238127287219922800453077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29650836382959897067270769 22238127287219922800453077)
          ·
            refine ⟨521206108294216940635619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 22238127287219922800453077 521206108294216940635619)
            ·
              refine ⟨781809162441325410953429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521206108294216940635619 781809162441325410953429)
              ·
                refine ⟨18323652244718564319221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 781809162441325410953429 18323652244718564319221)
                ·
                  rfl

theorem cell21_240875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 7].length) (baseStart_240875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240875 prefixEnd_240875 := by exact prefixLift 240875
  have htrace : WordTrace (prefixWord ++ tailWord_240875) baseStart_240875 baseEnd_240875 := by
    simpa [prefixWord, tailWord_240875, baseEnd_240875] using wordTrace_append hprefix tailTrace_240875
  have hstable : (prefixWord ++ tailWord_240875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240875).length < 2 ^ (prefixWord ++ tailWord_240875).sum := by decide
  have hdescent : baseEnd_240875 < baseStart_240875 := by decide
  rcases family_descends (prefixWord ++ tailWord_240875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240892 : List Nat := [2, 2, 2, 1, 5, 2, 7]
def baseStart_240892 : Nat := 118140960795 + 240892 * 2 ^ 59
def prefixEnd_240892 : Nat := 4983230072969 + 3 ^ 40 * 240892 * 2
def baseEnd_240892 : Nat := 6108315151751937908255

theorem tailTrace_240892 : CollatzResearch.WordTrace tailWord_240892 prefixEnd_240892 6108315151751937908255 := by
  unfold tailWord_240892
  simp only [CollatzResearch.WordTrace]
  refine ⟨4393026521648449961650465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5857368695531266615533953 4393026521648449961650465)
  ·
    refine ⟨3294769891236337471237849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4393026521648449961650465 3294769891236337471237849)
    ·
      refine ⟨2471077418427253103428387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3294769891236337471237849 2471077418427253103428387)
      ·
        refine ⟨3706616127640879655142581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471077418427253103428387 3706616127640879655142581)
        ·
          refine ⟨347495261966332467669617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3706616127640879655142581 347495261966332467669617)
          ·
            refine ⟨260621446474749350752213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347495261966332467669617 260621446474749350752213)
            ·
              refine ⟨6108315151751937908255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 260621446474749350752213 6108315151751937908255)
              ·
                rfl

theorem cell21_240892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 7].length) (baseStart_240892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240892 prefixEnd_240892 := by exact prefixLift 240892
  have htrace : WordTrace (prefixWord ++ tailWord_240892) baseStart_240892 baseEnd_240892 := by
    simpa [prefixWord, tailWord_240892, baseEnd_240892] using wordTrace_append hprefix tailTrace_240892
  have hstable : (prefixWord ++ tailWord_240892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240892).length < 2 ^ (prefixWord ++ tailWord_240892).sum := by decide
  have hdescent : baseEnd_240892 < baseStart_240892 := by decide
  rcases family_descends (prefixWord ++ tailWord_240892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240898 : List Nat := [3, 4, 1, 1, 3, 1, 3, 2, 3]
def baseStart_240898 : Nat := 118140960795 + 240898 * 2 ^ 59
def prefixEnd_240898 : Nat := 4983230072969 + 3 ^ 40 * 240898 * 2
def baseEnd_240898 : Nat := 54976205647512764074283

theorem tailTrace_240898 : CollatzResearch.WordTrace tailWord_240898 prefixEnd_240898 54976205647512764074283 := by
  unfold tailWord_240898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2196567970318790737004837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5857514587516775298679565 2196567970318790737004837)
  ·
    refine ⟨411856494434773263188407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2196567970318790737004837 411856494434773263188407)
    ·
      refine ⟨617784741652159894782611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411856494434773263188407 617784741652159894782611)
      ·
        refine ⟨926677112478239842173917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617784741652159894782611 926677112478239842173917)
        ·
          refine ⟨347503917179339940815219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 926677112478239842173917 347503917179339940815219)
          ·
            refine ⟨521255875769009911222829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347503917179339940815219 521255875769009911222829)
            ·
              refine ⟨195470953413378716708561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521255875769009911222829 195470953413378716708561)
              ·
                refine ⟨146603215060034037531421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195470953413378716708561 146603215060034037531421)
                ·
                  refine ⟨54976205647512764074283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146603215060034037531421 54976205647512764074283)
                  ·
                    rfl

theorem cell21_240898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_240898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240898 prefixEnd_240898 := by exact prefixLift 240898
  have htrace : WordTrace (prefixWord ++ tailWord_240898) baseStart_240898 baseEnd_240898 := by
    simpa [prefixWord, tailWord_240898, baseEnd_240898] using wordTrace_append hprefix tailTrace_240898
  have hstable : (prefixWord ++ tailWord_240898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240898).length < 2 ^ (prefixWord ++ tailWord_240898).sum := by decide
  have hdescent : baseEnd_240898 < baseStart_240898 := by decide
  rcases family_descends (prefixWord ++ tailWord_240898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240957 : List Nat := [1, 4, 1, 5, 1, 1, 1, 4, 3]
def baseStart_240957 : Nat := 118140960795 + 240957 * 2 ^ 59
def prefixEnd_240957 : Nat := 4983230072969 + 3 ^ 40 * 240957 * 2
def baseEnd_240957 : Nat := 54989670251341772590829

theorem tailTrace_240957 : CollatzResearch.WordTrace tailWord_240957 prefixEnd_240957 54989670251341772590829 := by
  unfold tailWord_240957
  simp only [CollatzResearch.WordTrace]
  refine ⟨8788423788061416024417125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5858949192040944016278083 8788423788061416024417125)
  ·
    refine ⟨1647829460261515504578211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8788423788061416024417125 1647829460261515504578211)
    ·
      refine ⟨2471744190392273256867317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647829460261515504578211 2471744190392273256867317)
      ·
        refine ⟨231726017849275617831311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2471744190392273256867317 231726017849275617831311)
        ·
          refine ⟨347589026773913426746967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231726017849275617831311 347589026773913426746967)
          ·
            refine ⟨521383540160870140120451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347589026773913426746967 521383540160870140120451)
            ·
              refine ⟨782075310241305210180677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521383540160870140120451 782075310241305210180677)
              ·
                refine ⟨146639120670244726908877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 782075310241305210180677 146639120670244726908877)
                ·
                  refine ⟨54989670251341772590829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146639120670244726908877 54989670251341772590829)
                  ·
                    rfl

theorem cell21_240957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_240957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240957 prefixEnd_240957 := by exact prefixLift 240957
  have htrace : WordTrace (prefixWord ++ tailWord_240957) baseStart_240957 baseEnd_240957 := by
    simpa [prefixWord, tailWord_240957, baseEnd_240957] using wordTrace_append hprefix tailTrace_240957
  have hstable : (prefixWord ++ tailWord_240957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240957).length < 2 ^ (prefixWord ++ tailWord_240957).sum := by decide
  have hdescent : baseEnd_240957 < baseStart_240957 := by decide
  rcases family_descends (prefixWord ++ tailWord_240957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240965 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 9]
def baseStart_240965 : Nat := 118140960795 + 240965 * 2 ^ 59
def prefixEnd_240965 : Nat := 4983230072969 + 3 ^ 40 * 240965 * 2
def baseEnd_240965 : Nat := 54991495960335536457479

theorem tailTrace_240965 : CollatzResearch.WordTrace tailWord_240965 prefixEnd_240965 54991495960335536457479 := by
  unfold tailWord_240965
  simp only [CollatzResearch.WordTrace]
  refine ⟨8788715572032433390708349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5859143714688288927138899 8788715572032433390708349)
  ·
    refine ⟨3295768339512162521515631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8788715572032433390708349 3295768339512162521515631)
    ·
      refine ⟨4943652509268243782273447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3295768339512162521515631 4943652509268243782273447)
      ·
        refine ⟨7415478763902365673410171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4943652509268243782273447 7415478763902365673410171)
        ·
          refine ⟨11123218145853548510115257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7415478763902365673410171 11123218145853548510115257)
          ·
            refine ⟨8342413609390161382586443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11123218145853548510115257 8342413609390161382586443)
            ·
              refine ⟨12513620414085242073879665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8342413609390161382586443 12513620414085242073879665)
              ·
                refine ⟨9385215310563931555409749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12513620414085242073879665 9385215310563931555409749)
                ·
                  refine ⟨54991495960335536457479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9385215310563931555409749 54991495960335536457479)
                  ·
                    rfl

theorem cell21_240965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_240965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_240965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_240965 prefixEnd_240965 := by exact prefixLift 240965
  have htrace : WordTrace (prefixWord ++ tailWord_240965) baseStart_240965 baseEnd_240965 := by
    simpa [prefixWord, tailWord_240965, baseEnd_240965] using wordTrace_append hprefix tailTrace_240965
  have hstable : (prefixWord ++ tailWord_240965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240965).length < 2 ^ (prefixWord ++ tailWord_240965).sum := by decide
  have hdescent : baseEnd_240965 < baseStart_240965 := by decide
  rcases family_descends (prefixWord ++ tailWord_240965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241044 : List Nat := [2, 4, 2, 1, 2, 2, 1, 7]
def baseStart_241044 : Nat := 118140960795 + 241044 * 2 ^ 59
def prefixEnd_241044 : Nat := 4983230072969 + 3 ^ 40 * 241044 * 2
def baseEnd_241044 : Nat := 18336508278882984880217

theorem tailTrace_241044 : CollatzResearch.WordTrace tailWord_241044 prefixEnd_241044 18336508278882984880217 := by
  unfold tailWord_241044
  simp only [CollatzResearch.WordTrace]
  refine ⟨4395798469373114941417093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5861064625830819921889457 4395798469373114941417093)
  ·
    refine ⟨824212213007459051515705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4395798469373114941417093 824212213007459051515705)
    ·
      refine ⟨618159159755594288636779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 824212213007459051515705 618159159755594288636779)
      ·
        refine ⟨927238739633391432955169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 618159159755594288636779 927238739633391432955169)
        ·
          refine ⟨695429054725043574716377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927238739633391432955169 695429054725043574716377)
          ·
            refine ⟨521571791043782681037283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695429054725043574716377 521571791043782681037283)
            ·
              refine ⟨782357686565674021555925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521571791043782681037283 782357686565674021555925)
              ·
                refine ⟨18336508278882984880217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 782357686565674021555925 18336508278882984880217)
                ·
                  rfl

theorem cell21_241044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_241044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241044 prefixEnd_241044 := by exact prefixLift 241044
  have htrace : WordTrace (prefixWord ++ tailWord_241044) baseStart_241044 baseEnd_241044 := by
    simpa [prefixWord, tailWord_241044, baseEnd_241044] using wordTrace_append hprefix tailTrace_241044
  have hstable : (prefixWord ++ tailWord_241044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241044).length < 2 ^ (prefixWord ++ tailWord_241044).sum := by decide
  have hdescent : baseEnd_241044 < baseStart_241044 := by decide
  rcases family_descends (prefixWord ++ tailWord_241044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241134 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_241134 : Nat := 118140960795 + 241134 * 2 ^ 59
def prefixEnd_241134 : Nat := 4983230072969 + 3 ^ 40 * 241134 * 2
def baseEnd_241134 : Nat := 55030064062828798140467

theorem tailTrace_241134 : CollatzResearch.WordTrace tailWord_241134 prefixEnd_241134 55030064062828798140467 := by
  unfold tailWord_241134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1099359938552521906701307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5863253005613450169073637 1099359938552521906701307)
  ·
    refine ⟨1649039907828782860051961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1099359938552521906701307 1649039907828782860051961)
    ·
      refine ⟨1236779930871587145038971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1649039907828782860051961 1236779930871587145038971)
      ·
        refine ⟨1855169896307380717558457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1236779930871587145038971 1855169896307380717558457)
        ·
          refine ⟨1391377422230535538168843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1855169896307380717558457 1391377422230535538168843)
          ·
            refine ⟨2087066133345803307253265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1391377422230535538168843 2087066133345803307253265)
            ·
              refine ⟨1565299600009352480439949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2087066133345803307253265 1565299600009352480439949)
              ·
                refine ⟨586987350003507180164981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1565299600009352480439949 586987350003507180164981)
                ·
                  refine ⟨55030064062828798140467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 586987350003507180164981 55030064062828798140467)
                  ·
                    rfl

theorem cell21_241134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_241134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241134 prefixEnd_241134 := by exact prefixLift 241134
  have htrace : WordTrace (prefixWord ++ tailWord_241134) baseStart_241134 baseEnd_241134 := by
    simpa [prefixWord, tailWord_241134, baseEnd_241134] using wordTrace_append hprefix tailTrace_241134
  have hstable : (prefixWord ++ tailWord_241134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241134).length < 2 ^ (prefixWord ++ tailWord_241134).sum := by decide
  have hdescent : baseEnd_241134 < baseStart_241134 := by decide
  rcases family_descends (prefixWord ++ tailWord_241134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241213 : List Nat := [1, 4, 1, 3, 3, 2, 2, 5]
def baseStart_241213 : Nat := 118140960795 + 241213 * 2 ^ 59
def prefixEnd_241213 : Nat := 4983230072969 + 3 ^ 40 * 241213 * 2
def baseEnd_241213 : Nat := 18349364313047405441213

theorem tailTrace_241213 : CollatzResearch.WordTrace tailWord_241213 prefixEnd_241213 18349364313047405441213 := by
  unfold tailWord_241213
  simp only [CollatzResearch.WordTrace]
  refine ⟨8797760875133971745736293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5865173916755981163824195 8797760875133971745736293)
  ·
    refine ⟨1649580164087619702325555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8797760875133971745736293 1649580164087619702325555)
    ·
      refine ⟨2474370246131429553488333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1649580164087619702325555 2474370246131429553488333)
      ·
        refine ⟨927888842299286082558125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2474370246131429553488333 927888842299286082558125)
        ·
          refine ⟨347958315862232280959297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 927888842299286082558125 347958315862232280959297)
          ·
            refine ⟨260968736896674210719473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347958315862232280959297 260968736896674210719473)
            ·
              refine ⟨195726552672505658039605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260968736896674210719473 195726552672505658039605)
              ·
                refine ⟨18349364313047405441213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195726552672505658039605 18349364313047405441213)
                ·
                  rfl

theorem cell21_241213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 5].length) (baseStart_241213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241213 prefixEnd_241213 := by exact prefixLift 241213
  have htrace : WordTrace (prefixWord ++ tailWord_241213) baseStart_241213 baseEnd_241213 := by
    simpa [prefixWord, tailWord_241213, baseEnd_241213] using wordTrace_append hprefix tailTrace_241213
  have hstable : (prefixWord ++ tailWord_241213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241213).length < 2 ^ (prefixWord ++ tailWord_241213).sum := by decide
  have hdescent : baseEnd_241213 < baseStart_241213 := by decide
  rcases family_descends (prefixWord ++ tailWord_241213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241258 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_241258 : Nat := 118140960795 + 241258 * 2 ^ 59
def prefixEnd_241258 : Nat := 4983230072969 + 3 ^ 40 * 241258 * 2
def baseEnd_241258 : Nat := 55058362552232138073547

theorem tailTrace_241258 : CollatzResearch.WordTrace tailWord_241258 prefixEnd_241258 55058362552232138073547 := by
  unfold tailWord_241258
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199850539992736107781107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5866268106647296287416285 2199850539992736107781107)
  ·
    refine ⟨3299775809989104161671661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2199850539992736107781107 3299775809989104161671661)
    ·
      refine ⟨1237415928745914060626873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3299775809989104161671661 1237415928745914060626873)
      ·
        refine ⟨928061946559435545470155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1237415928745914060626873 928061946559435545470155)
        ·
          refine ⟨1392092919839153318205233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928061946559435545470155 1392092919839153318205233)
          ·
            refine ⟨1044069689879364988653925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392092919839153318205233 1044069689879364988653925)
            ·
              refine ⟨195763066852380935372611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1044069689879364988653925 195763066852380935372611)
              ·
                refine ⟨293644600278571403058917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195763066852380935372611 293644600278571403058917)
                ·
                  refine ⟨55058362552232138073547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293644600278571403058917 55058362552232138073547)
                  ·
                    rfl

theorem cell21_241258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_241258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241258 prefixEnd_241258 := by exact prefixLift 241258
  have htrace : WordTrace (prefixWord ++ tailWord_241258) baseStart_241258 baseEnd_241258 := by
    simpa [prefixWord, tailWord_241258, baseEnd_241258] using wordTrace_append hprefix tailTrace_241258
  have hstable : (prefixWord ++ tailWord_241258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241258).length < 2 ^ (prefixWord ++ tailWord_241258).sum := by decide
  have hdescent : baseEnd_241258 < baseStart_241258 := by decide
  rcases family_descends (prefixWord ++ tailWord_241258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241303 : List Nat := [1, 1, 3, 3, 2, 3, 1, 4, 3]
def baseStart_241303 : Nat := 118140960795 + 241303 * 2 ^ 59
def prefixEnd_241303 : Nat := 4983230072969 + 3 ^ 40 * 241303 * 2
def baseEnd_241303 : Nat := 55068632165322059823455

theorem tailTrace_241303 : CollatzResearch.WordTrace tailWord_241303 prefixEnd_241303 55068632165322059823455 := by
  unfold tailWord_241303
  simp only [CollatzResearch.WordTrace]
  refine ⟨8801043444807917116512563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5867362296538611411008375 8801043444807917116512563)
  ·
    refine ⟨13201565167211875674768845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8801043444807917116512563 13201565167211875674768845)
    ·
      refine ⟨4950586937704453378038317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13201565167211875674768845 4950586937704453378038317)
      ·
        refine ⟨1856470101639170016764369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4950586937704453378038317 1856470101639170016764369)
        ·
          refine ⟨1392352576229377512573277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1856470101639170016764369 1392352576229377512573277)
          ·
            refine ⟨522132216086016567214979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1392352576229377512573277 522132216086016567214979)
            ·
              refine ⟨783198324129024850822469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 522132216086016567214979 783198324129024850822469)
              ·
                refine ⟨146849685774192159529213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 783198324129024850822469 146849685774192159529213)
                ·
                  refine ⟨55068632165322059823455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146849685774192159529213 55068632165322059823455)
                  ·
                    rfl

theorem cell21_241303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 3].length) (baseStart_241303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241303 prefixEnd_241303 := by exact prefixLift 241303
  have htrace : WordTrace (prefixWord ++ tailWord_241303) baseStart_241303 baseEnd_241303 := by
    simpa [prefixWord, tailWord_241303, baseEnd_241303] using wordTrace_append hprefix tailTrace_241303
  have hstable : (prefixWord ++ tailWord_241303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241303).length < 2 ^ (prefixWord ++ tailWord_241303).sum := by decide
  have hdescent : baseEnd_241303 < baseStart_241303 := by decide
  rcases family_descends (prefixWord ++ tailWord_241303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241331 : List Nat := [1, 1, 1, 2, 3, 3, 5, 5]
def baseStart_241331 : Nat := 118140960795 + 241331 * 2 ^ 59
def prefixEnd_241331 : Nat := 4983230072969 + 3 ^ 40 * 241331 * 2
def baseEnd_241331 : Nat := 18358340715600077785577

theorem tailTrace_241331 : CollatzResearch.WordTrace tailWord_241331 prefixEnd_241331 18358340715600077785577 := by
  unfold tailWord_241331
  simp only [CollatzResearch.WordTrace]
  refine ⟨8802064688706477898531847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5868043125804318599021231 8802064688706477898531847)
  ·
    refine ⟨13203097033059716847797771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8802064688706477898531847 13203097033059716847797771)
    ·
      refine ⟨19804645549589575271696657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13203097033059716847797771 19804645549589575271696657)
      ·
        refine ⟨14853484162192181453772493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19804645549589575271696657 14853484162192181453772493)
        ·
          refine ⟨5570056560822068045164685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14853484162192181453772493 5570056560822068045164685)
          ·
            refine ⟨2088771210308275516936757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5570056560822068045164685 2088771210308275516936757)
            ·
              refine ⟨195822300966400829712821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2088771210308275516936757 195822300966400829712821)
              ·
                refine ⟨18358340715600077785577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195822300966400829712821 18358340715600077785577)
                ·
                  rfl

theorem cell21_241331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 5].length) (baseStart_241331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241331 prefixEnd_241331 := by exact prefixLift 241331
  have htrace : WordTrace (prefixWord ++ tailWord_241331) baseStart_241331 baseEnd_241331 := by
    simpa [prefixWord, tailWord_241331, baseEnd_241331] using wordTrace_append hprefix tailTrace_241331
  have hstable : (prefixWord ++ tailWord_241331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241331).length < 2 ^ (prefixWord ++ tailWord_241331).sum := by decide
  have hdescent : baseEnd_241331 < baseStart_241331 := by decide
  rcases family_descends (prefixWord ++ tailWord_241331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241362 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_241362 : Nat := 118140960795 + 241362 * 2 ^ 59
def prefixEnd_241362 : Nat := 4983230072969 + 3 ^ 40 * 241362 * 2
def baseEnd_241362 : Nat := 55082096769151068340001

theorem tailTrace_241362 : CollatzResearch.WordTrace tailWord_241362 prefixEnd_241362 55082096769151068340001 := by
  unfold tailWord_241362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2200798837898542548227585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5868796901062780128606893 2200798837898542548227585)
  ·
    refine ⟨1650599128423906911170689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2200798837898542548227585 1650599128423906911170689)
    ·
      refine ⟨1237949346317930183378017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1650599128423906911170689 1237949346317930183378017)
      ·
        refine ⟨928462009738447637533513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1237949346317930183378017 928462009738447637533513)
        ·
          refine ⟨696346507303835728150135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 928462009738447637533513 696346507303835728150135)
          ·
            refine ⟨1044519760955753592225203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696346507303835728150135 1044519760955753592225203)
            ·
              refine ⟨1566779641433630388337805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044519760955753592225203 1566779641433630388337805)
              ·
                refine ⟨587542365537611395626677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1566779641433630388337805 587542365537611395626677)
                ·
                  refine ⟨55082096769151068340001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 587542365537611395626677 55082096769151068340001)
                  ·
                    rfl

theorem cell21_241362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_241362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241362 prefixEnd_241362 := by exact prefixLift 241362
  have htrace : WordTrace (prefixWord ++ tailWord_241362) baseStart_241362 baseEnd_241362 := by
    simpa [prefixWord, tailWord_241362, baseEnd_241362] using wordTrace_append hprefix tailTrace_241362
  have hstable : (prefixWord ++ tailWord_241362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241362).length < 2 ^ (prefixWord ++ tailWord_241362).sum := by decide
  have hdescent : baseEnd_241362 < baseStart_241362 := by decide
  rcases family_descends (prefixWord ++ tailWord_241362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241376 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 4]
def baseStart_241376 : Nat := 118140960795 + 241376 * 2 ^ 59
def prefixEnd_241376 : Nat := 4983230072969 + 3 ^ 40 * 241376 * 2
def baseEnd_241376 : Nat := 55085291759890155106639

theorem tailTrace_241376 : CollatzResearch.WordTrace tailWord_241376 prefixEnd_241376 55085291759890155106639 := by
  unfold tailWord_241376
  simp only [CollatzResearch.WordTrace]
  refine ⟨4401852986771725291959991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5869137315695633722613321 4401852986771725291959991)
  ·
    refine ⟨6602779480157587937939987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4401852986771725291959991 6602779480157587937939987)
    ·
      refine ⟨9904169220236381906909981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6602779480157587937939987 9904169220236381906909981)
      ·
        refine ⟨3714063457588643215091243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9904169220236381906909981 3714063457588643215091243)
        ·
          refine ⟨5571095186382964822636865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714063457588643215091243 5571095186382964822636865)
          ·
            refine ⟨4178321389787223616977649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5571095186382964822636865 4178321389787223616977649)
            ·
              refine ⟨3133741042340417712733237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178321389787223616977649 3133741042340417712733237)
              ·
                refine ⟨293788222719414160568741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3133741042340417712733237 293788222719414160568741)
                ·
                  refine ⟨55085291759890155106639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293788222719414160568741 55085291759890155106639)
                  ·
                    rfl

theorem cell21_241376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_241376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241376 prefixEnd_241376 := by exact prefixLift 241376
  have htrace : WordTrace (prefixWord ++ tailWord_241376) baseStart_241376 baseEnd_241376 := by
    simpa [prefixWord, tailWord_241376, baseEnd_241376] using wordTrace_append hprefix tailTrace_241376
  have hstable : (prefixWord ++ tailWord_241376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241376).length < 2 ^ (prefixWord ++ tailWord_241376).sum := by decide
  have hdescent : baseEnd_241376 < baseStart_241376 := by decide
  rcases family_descends (prefixWord ++ tailWord_241376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241466 : List Nat := [3, 1, 1, 1, 5, 10]
def baseStart_241466 : Nat := 118140960795 + 241466 * 2 ^ 59
def prefixEnd_241466 : Nat := 4983230072969 + 3 ^ 40 * 241466 * 2
def baseEnd_241466 : Nat := 2040956703187777726165

theorem tailTrace_241466 : CollatzResearch.WordTrace tailWord_241466 prefixEnd_241466 2040956703187777726165 := by
  unfold tailWord_241466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201747135804348988674063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5871325695478263969797501 2201747135804348988674063)
  ·
    refine ⟨3302620703706523483011095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2201747135804348988674063 3302620703706523483011095)
    ·
      refine ⟨4953931055559785224516643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3302620703706523483011095 4953931055559785224516643)
      ·
        refine ⟨7430896583339677836774965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4953931055559785224516643 7430896583339677836774965)
        ·
          refine ⟨696646554688094797197653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7430896583339677836774965 696646554688094797197653)
          ·
            refine ⟨2040956703187777726165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 696646554688094797197653 2040956703187777726165)
            ·
              rfl

theorem cell21_241466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 10].length) (baseStart_241466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241466 prefixEnd_241466 := by exact prefixLift 241466
  have htrace : WordTrace (prefixWord ++ tailWord_241466) baseStart_241466 baseEnd_241466 := by
    simpa [prefixWord, tailWord_241466, baseEnd_241466] using wordTrace_append hprefix tailTrace_241466
  have hstable : (prefixWord ++ tailWord_241466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241466).length < 2 ^ (prefixWord ++ tailWord_241466).sum := by decide
  have hdescent : baseEnd_241466 < baseStart_241466 := by decide
  rcases family_descends (prefixWord ++ tailWord_241466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241469 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 4]
def baseStart_241469 : Nat := 118140960795 + 241469 * 2 ^ 59
def prefixEnd_241469 : Nat := 4983230072969 + 3 ^ 40 * 241469 * 2
def baseEnd_241469 : Nat := 55106515626942660056449

theorem tailTrace_241469 : CollatzResearch.WordTrace tailWord_241469 prefixEnd_241469 55106515626942660056449 := by
  unfold tailWord_241469
  simp only [CollatzResearch.WordTrace]
  refine ⟨8807097962206527467055461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5871398641471018311370307 8807097962206527467055461)
  ·
    refine ⟨1651330867913723900072899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8807097962206527467055461 1651330867913723900072899)
    ·
      refine ⟨2476996301870585850109349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1651330867913723900072899 2476996301870585850109349)
      ·
        refine ⟨464436806600734846895503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2476996301870585850109349 464436806600734846895503)
        ·
          refine ⟨696655209901102270343255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464436806600734846895503 696655209901102270343255)
          ·
            refine ⟨1044982814851653405514883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696655209901102270343255 1044982814851653405514883)
            ·
              refine ⟨1567474222277480108272325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044982814851653405514883 1567474222277480108272325)
              ·
                refine ⟨293901416677027520301061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1567474222277480108272325 293901416677027520301061)
                ·
                  refine ⟨55106515626942660056449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293901416677027520301061 55106515626942660056449)
                  ·
                    rfl

theorem cell21_241469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_241469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241469 prefixEnd_241469 := by exact prefixLift 241469
  have htrace : WordTrace (prefixWord ++ tailWord_241469) baseStart_241469 baseEnd_241469 := by
    simpa [prefixWord, tailWord_241469, baseEnd_241469] using wordTrace_append hprefix tailTrace_241469
  have hstable : (prefixWord ++ tailWord_241469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241469).length < 2 ^ (prefixWord ++ tailWord_241469).sum := by decide
  have hdescent : baseEnd_241469 < baseStart_241469 := by decide
  rcases family_descends (prefixWord ++ tailWord_241469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241497 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 5]
def baseStart_241497 : Nat := 118140960795 + 241497 * 2 ^ 59
def prefixEnd_241497 : Nat := 4983230072969 + 3 ^ 40 * 241497 * 2
def baseEnd_241497 : Nat := 55112905608420833589725

theorem tailTrace_241497 : CollatzResearch.WordTrace tailWord_241497 prefixEnd_241497 55112905608420833589725 := by
  unfold tailWord_241497
  simp only [CollatzResearch.WordTrace]
  refine ⟨8808119206105088249074745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5872079470736725499383163 8808119206105088249074745)
  ·
    refine ⟨6606089404578816186806059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8808119206105088249074745 6606089404578816186806059)
    ·
      refine ⟨9909134106868224280209089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6606089404578816186806059 9909134106868224280209089)
      ·
        refine ⟨7431850580151168210156817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9909134106868224280209089 7431850580151168210156817)
        ·
          refine ⟨5573887935113376157617613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7431850580151168210156817 5573887935113376157617613)
          ·
            refine ⟨2090207975667516059106605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5573887935113376157617613 2090207975667516059106605)
            ·
              refine ⟨783827990875318522164977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2090207975667516059106605 783827990875318522164977)
              ·
                refine ⟨587870993156488891623733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783827990875318522164977 587870993156488891623733)
                ·
                  refine ⟨55112905608420833589725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 587870993156488891623733 55112905608420833589725)
                  ·
                    rfl

theorem cell21_241497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_241497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241497 prefixEnd_241497 := by exact prefixLift 241497
  have htrace : WordTrace (prefixWord ++ tailWord_241497) baseStart_241497 baseEnd_241497 := by
    simpa [prefixWord, tailWord_241497, baseEnd_241497] using wordTrace_append hprefix tailTrace_241497
  have hstable : (prefixWord ++ tailWord_241497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241497).length < 2 ^ (prefixWord ++ tailWord_241497).sum := by decide
  have hdescent : baseEnd_241497 < baseStart_241497 := by decide
  rcases family_descends (prefixWord ++ tailWord_241497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241545 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 4]
def baseStart_241545 : Nat := 118140960795 + 241545 * 2 ^ 59
def prefixEnd_241545 : Nat := 4983230072969 + 3 ^ 40 * 241545 * 2
def baseEnd_241545 : Nat := 55123859862383416789627

theorem tailTrace_241545 : CollatzResearch.WordTrace tailWord_241545 prefixEnd_241545 55123859862383416789627 := by
  unfold tailWord_241545
  simp only [CollatzResearch.WordTrace]
  refine ⟨8809869909931192446822089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5873246606620794964548059 8809869909931192446822089)
  ·
    refine ⟨6607402432448394335116567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8809869909931192446822089 6607402432448394335116567)
    ·
      refine ⟨9911103648672591502674851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6607402432448394335116567 9911103648672591502674851)
      ·
        refine ⟨14866655473008887254012277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9911103648672591502674851 14866655473008887254012277)
        ·
          refine ⟨1393748950594583180063651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14866655473008887254012277 1393748950594583180063651)
          ·
            refine ⟨2090623425891874770095477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393748950594583180063651 2090623425891874770095477)
            ·
              refine ⟨195995946177363259696451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2090623425891874770095477 195995946177363259696451)
              ·
                refine ⟨293993919266044889544677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195995946177363259696451 293993919266044889544677)
                ·
                  refine ⟨55123859862383416789627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 293993919266044889544677 55123859862383416789627)
                  ·
                    rfl

theorem cell21_241545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_241545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241545 prefixEnd_241545 := by exact prefixLift 241545
  have htrace : WordTrace (prefixWord ++ tailWord_241545) baseStart_241545 baseEnd_241545 := by
    simpa [prefixWord, tailWord_241545, baseEnd_241545] using wordTrace_append hprefix tailTrace_241545
  have hstable : (prefixWord ++ tailWord_241545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241545).length < 2 ^ (prefixWord ++ tailWord_241545).sum := by decide
  have hdescent : baseEnd_241545 < baseStart_241545 := by decide
  rcases family_descends (prefixWord ++ tailWord_241545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241559 : List Nat := [1, 1, 3, 3, 1, 3, 4, 5]
def baseStart_241559 : Nat := 118140960795 + 241559 * 2 ^ 59
def prefixEnd_241559 : Nat := 4983230072969 + 3 ^ 40 * 241559 * 2
def baseEnd_241559 : Nat := 18375684951040834518755

theorem tailTrace_241559 : CollatzResearch.WordTrace tailWord_241559 prefixEnd_241559 18375684951040834518755 := by
  unfold tailWord_241559
  simp only [CollatzResearch.WordTrace]
  refine ⟨8810380531880472837831731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5873587021253648558554487 8810380531880472837831731)
  ·
    refine ⟨13215570797820709256747597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8810380531880472837831731 13215570797820709256747597)
    ·
      refine ⟨4955839049182765971280349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13215570797820709256747597 4955839049182765971280349)
      ·
        refine ⟨1858439643443537239230131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4955839049182765971280349 1858439643443537239230131)
        ·
          refine ⟨2787659465165305858845197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1858439643443537239230131 2787659465165305858845197)
          ·
            refine ⟨1045372299436989697066949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2787659465165305858845197 1045372299436989697066949)
            ·
              refine ⟨196007306144435568200053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1045372299436989697066949 196007306144435568200053)
              ·
                refine ⟨18375684951040834518755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196007306144435568200053 18375684951040834518755)
                ·
                  rfl

theorem cell21_241559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 5].length) (baseStart_241559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241559 prefixEnd_241559 := by exact prefixLift 241559
  have htrace : WordTrace (prefixWord ++ tailWord_241559) baseStart_241559 baseEnd_241559 := by
    simpa [prefixWord, tailWord_241559, baseEnd_241559] using wordTrace_append hprefix tailTrace_241559
  have hstable : (prefixWord ++ tailWord_241559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241559).length < 2 ^ (prefixWord ++ tailWord_241559).sum := by decide
  have hdescent : baseEnd_241559 < baseStart_241559 := by decide
  rcases family_descends (prefixWord ++ tailWord_241559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241582 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_241582 : Nat := 118140960795 + 241582 * 2 ^ 59
def prefixEnd_241582 : Nat := 4983230072969 + 3 ^ 40 * 241582 * 2
def baseEnd_241582 : Nat := 55132303766479574672885

theorem tailTrace_241582 : CollatzResearch.WordTrace tailWord_241582 prefixEnd_241582 55132303766479574672885 := by
  unfold tailWord_241582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1101402426349643470739875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5874146273864765177279333 1101402426349643470739875)
  ·
    refine ⟨1652103639524465206109813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1101402426349643470739875 1652103639524465206109813)
    ·
      refine ⟨154884716205418613072795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1652103639524465206109813 154884716205418613072795)
      ·
        refine ⟨232327074308127919609193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154884716205418613072795 232327074308127919609193)
        ·
          refine ⟨174245305731095939706895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232327074308127919609193 174245305731095939706895)
          ·
            refine ⟨261367958596643909560343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174245305731095939706895 261367958596643909560343)
            ·
              refine ⟨392051937894965864340515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261367958596643909560343 392051937894965864340515)
              ·
                refine ⟨588077906842448796510773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392051937894965864340515 588077906842448796510773)
                ·
                  refine ⟨55132303766479574672885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 588077906842448796510773 55132303766479574672885)
                  ·
                    rfl

theorem cell21_241582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_241582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241582 prefixEnd_241582 := by exact prefixLift 241582
  have htrace : WordTrace (prefixWord ++ tailWord_241582) baseStart_241582 baseEnd_241582 := by
    simpa [prefixWord, tailWord_241582, baseEnd_241582] using wordTrace_append hprefix tailTrace_241582
  have hstable : (prefixWord ++ tailWord_241582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241582).length < 2 ^ (prefixWord ++ tailWord_241582).sum := by decide
  have hdescent : baseEnd_241582 < baseStart_241582 := by decide
  rcases family_descends (prefixWord ++ tailWord_241582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241587 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 6]
def baseStart_241587 : Nat := 118140960795 + 241587 * 2 ^ 59
def prefixEnd_241587 : Nat := 4983230072969 + 3 ^ 40 * 241587 * 2
def baseEnd_241587 : Nat := 55133444834600677089541

theorem tailTrace_241587 : CollatzResearch.WordTrace tailWord_241587 prefixEnd_241587 55133444834600677089541 := by
  unfold tailWord_241587
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811401775779033619851015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5874267850519355746567343 8811401775779033619851015)
  ·
    refine ⟨13217102663668550429776523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8811401775779033619851015 13217102663668550429776523)
    ·
      refine ⟨19825653995502825644664785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13217102663668550429776523 19825653995502825644664785)
      ·
        refine ⟨14869240496627119233498589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19825653995502825644664785 14869240496627119233498589)
        ·
          refine ⟨5575965186235169712561971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14869240496627119233498589 5575965186235169712561971)
          ·
            refine ⟨8363947779352754568842957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5575965186235169712561971 8363947779352754568842957)
            ·
              refine ⟨3136480417257282963316109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8363947779352754568842957 3136480417257282963316109)
              ·
                refine ⟨1176180156471481111243541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3136480417257282963316109 1176180156471481111243541)
                ·
                  refine ⟨55133444834600677089541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1176180156471481111243541 55133444834600677089541)
                  ·
                    rfl

theorem cell21_241587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_241587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241587 prefixEnd_241587 := by exact prefixLift 241587
  have htrace : WordTrace (prefixWord ++ tailWord_241587) baseStart_241587 baseEnd_241587 := by
    simpa [prefixWord, tailWord_241587, baseEnd_241587] using wordTrace_append hprefix tailTrace_241587
  have hstable : (prefixWord ++ tailWord_241587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241587).length < 2 ^ (prefixWord ++ tailWord_241587).sum := by decide
  have hdescent : baseEnd_241587 < baseStart_241587 := by decide
  rcases family_descends (prefixWord ++ tailWord_241587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241596 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 4]
def baseStart_241596 : Nat := 118140960795 + 241596 * 2 ^ 59
def prefixEnd_241596 : Nat := 4983230072969 + 3 ^ 40 * 241596 * 2
def baseEnd_241596 : Nat := 55135498757218661439523

theorem tailTrace_241596 : CollatzResearch.WordTrace tailWord_241596 prefixEnd_241596 55135498757218661439523 := by
  unfold tailWord_241596
  simp only [CollatzResearch.WordTrace]
  refine ⟨4405865016373214078464321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5874486688497618771285761 4405865016373214078464321)
  ·
    refine ⟨3304398762279910558848241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4405865016373214078464321 3304398762279910558848241)
    ·
      refine ⟨2478299071709932919136181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3304398762279910558848241 2478299071709932919136181)
      ·
        refine ⟨232340537972806211169017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2478299071709932919136181 232340537972806211169017)
        ·
          refine ⟨174255403479604658376763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232340537972806211169017 174255403479604658376763)
          ·
            refine ⟨261383105219406987565145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174255403479604658376763 261383105219406987565145)
            ·
              refine ⟨196037328914555240673859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261383105219406987565145 196037328914555240673859)
              ·
                refine ⟨294055993371832861010789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196037328914555240673859 294055993371832861010789)
                ·
                  refine ⟨55135498757218661439523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294055993371832861010789 55135498757218661439523)
                  ·
                    rfl

theorem cell21_241596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_241596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241596 prefixEnd_241596 := by exact prefixLift 241596
  have htrace : WordTrace (prefixWord ++ tailWord_241596) baseStart_241596 baseEnd_241596 := by
    simpa [prefixWord, tailWord_241596, baseEnd_241596] using wordTrace_append hprefix tailTrace_241596
  have hstable : (prefixWord ++ tailWord_241596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241596).length < 2 ^ (prefixWord ++ tailWord_241596).sum := by decide
  have hdescent : baseEnd_241596 < baseStart_241596 := by decide
  rcases family_descends (prefixWord ++ tailWord_241596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241725 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 5]
def baseStart_241725 : Nat := 118140960795 + 241725 * 2 ^ 59
def prefixEnd_241725 : Nat := 4983230072969 + 3 ^ 40 * 241725 * 2
def baseEnd_241725 : Nat := 55164938314743103789259

theorem tailTrace_241725 : CollatzResearch.WordTrace tailWord_241725 prefixEnd_241725 55164938314743103789259 := by
  unfold tailWord_241725
  simp only [CollatzResearch.WordTrace]
  refine ⟨8816435049279083188374629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5877623366186055458916419 8816435049279083188374629)
  ·
    refine ⟨1653081571739828097820243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8816435049279083188374629 1653081571739828097820243)
    ·
      refine ⟨2479622357609742146730365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653081571739828097820243 2479622357609742146730365)
      ·
        refine ⟨929858384103653305023887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2479622357609742146730365 929858384103653305023887)
        ·
          refine ⟨1394787576155479957535831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929858384103653305023887 1394787576155479957535831)
          ·
            refine ⟨2092181364233219936303747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394787576155479957535831 2092181364233219936303747)
            ·
              refine ⟨3138272046349829904455621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2092181364233219936303747 3138272046349829904455621)
              ·
                refine ⟨588426008690593107085429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3138272046349829904455621 588426008690593107085429)
                ·
                  refine ⟨55164938314743103789259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 588426008690593107085429 55164938314743103789259)
                  ·
                    rfl

theorem cell21_241725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_241725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241725 prefixEnd_241725 := by exact prefixLift 241725
  have htrace : WordTrace (prefixWord ++ tailWord_241725) baseStart_241725 baseEnd_241725 := by
    simpa [prefixWord, tailWord_241725, baseEnd_241725] using wordTrace_append hprefix tailTrace_241725
  have hstable : (prefixWord ++ tailWord_241725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241725).length < 2 ^ (prefixWord ++ tailWord_241725).sum := by decide
  have hdescent : baseEnd_241725 < baseStart_241725 := by decide
  rcases family_descends (prefixWord ++ tailWord_241725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241756 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_241756 : Nat := 118140960795 + 241756 * 2 ^ 59
def prefixEnd_241756 : Nat := 4983230072969 + 3 ^ 40 * 241756 * 2
def baseEnd_241756 : Nat := 55172012937093938772529

theorem tailTrace_241756 : CollatzResearch.WordTrace tailWord_241756 prefixEnd_241756 55172012937093938772529 := by
  unfold tailWord_241756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4408782856083387741376561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5878377141444516988502081 4408782856083387741376561)
  ·
    refine ⟨3306587142062540806032421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4408782856083387741376561 3306587142062540806032421)
    ·
      refine ⟨619985089136726401131079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3306587142062540806032421 619985089136726401131079)
      ·
        refine ⟨929977633705089601696619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619985089136726401131079 929977633705089601696619)
        ·
          refine ⟨1394966450557634402544929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929977633705089601696619 1394966450557634402544929)
          ·
            refine ⟨1046224837918225801908697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1394966450557634402544929 1046224837918225801908697)
            ·
              refine ⟨784668628438669351431523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046224837918225801908697 784668628438669351431523)
              ·
                refine ⟨1177002942658004027147285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784668628438669351431523 1177002942658004027147285)
                ·
                  refine ⟨55172012937093938772529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1177002942658004027147285 55172012937093938772529)
                  ·
                    rfl

theorem cell21_241756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_241756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241756 prefixEnd_241756 := by exact prefixLift 241756
  have htrace : WordTrace (prefixWord ++ tailWord_241756) baseStart_241756 baseEnd_241756 := by
    simpa [prefixWord, tailWord_241756, baseEnd_241756] using wordTrace_append hprefix tailTrace_241756
  have hstable : (prefixWord ++ tailWord_241756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241756).length < 2 ^ (prefixWord ++ tailWord_241756).sum := by decide
  have hdescent : baseEnd_241756 < baseStart_241756 := by decide
  rcases family_descends (prefixWord ++ tailWord_241756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241784 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_241784 : Nat := 118140960795 + 241784 * 2 ^ 59
def prefixEnd_241784 : Nat := 4983230072969 + 3 ^ 40 * 241784 * 2
def baseEnd_241784 : Nat := 55178402918572112305805

theorem tailTrace_241784 : CollatzResearch.WordTrace tailWord_241784 prefixEnd_241784 55178402918572112305805 := by
  unfold tailWord_241784
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409293478032668132386203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5879057970710224176514937 4409293478032668132386203)
  ·
    refine ⟨6613940217049002198579305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4409293478032668132386203 6613940217049002198579305)
    ·
      refine ⟨4960455162786751648934479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6613940217049002198579305 4960455162786751648934479)
      ·
        refine ⟨7440682744180127473401719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4960455162786751648934479 7440682744180127473401719)
        ·
          refine ⟨11161024116270191210102579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7440682744180127473401719 11161024116270191210102579)
          ·
            refine ⟨16741536174405286815153869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11161024116270191210102579 16741536174405286815153869)
            ·
              refine ⟨6278076065401982555682701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16741536174405286815153869 6278076065401982555682701)
              ·
                refine ⟨2354278524525743458381013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6278076065401982555682701 2354278524525743458381013)
                ·
                  refine ⟨55178402918572112305805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2354278524525743458381013 55178402918572112305805)
                  ·
                    rfl

theorem cell21_241784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_241784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241784 prefixEnd_241784 := by exact prefixLift 241784
  have htrace : WordTrace (prefixWord ++ tailWord_241784) baseStart_241784 baseEnd_241784 := by
    simpa [prefixWord, tailWord_241784, baseEnd_241784] using wordTrace_append hprefix tailTrace_241784
  have hstable : (prefixWord ++ tailWord_241784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241784).length < 2 ^ (prefixWord ++ tailWord_241784).sum := by decide
  have hdescent : baseEnd_241784 < baseStart_241784 := by decide
  rcases family_descends (prefixWord ++ tailWord_241784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_241981 : List Nat := [1, 4, 1, 15]
def baseStart_241981 : Nat := 118140960795 + 241981 * 2 ^ 59
def prefixEnd_241981 : Nat := 4983230072969 + 3 ^ 40 * 241981 * 2
def baseEnd_241981 : Nat := 227256629640096903383

theorem tailTrace_241981 : CollatzResearch.WordTrace tailWord_241981 prefixEnd_241981 227256629640096903383 := by
  unfold tailWord_241981
  simp only [CollatzResearch.WordTrace]
  refine ⟨8825772136351638909693797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5883848090901092606462531 8825772136351638909693797)
  ·
    refine ⟨1654832275565932295567587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8825772136351638909693797 1654832275565932295567587)
    ·
      refine ⟨2482248413348898443351381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654832275565932295567587 2482248413348898443351381)
      ·
        refine ⟨227256629640096903383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 2482248413348898443351381 227256629640096903383)
        ·
          rfl

theorem cell21_241981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 15].length) (baseStart_241981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_241981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_241981 prefixEnd_241981 := by exact prefixLift 241981
  have htrace : WordTrace (prefixWord ++ tailWord_241981) baseStart_241981 baseEnd_241981 := by
    simpa [prefixWord, tailWord_241981, baseEnd_241981] using wordTrace_append hprefix tailTrace_241981
  have hstable : (prefixWord ++ tailWord_241981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_241981).length < 2 ^ (prefixWord ++ tailWord_241981).sum := by decide
  have hdescent : baseEnd_241981 < baseStart_241981 := by decide
  rcases family_descends (prefixWord ++ tailWord_241981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242043 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 6]
def baseStart_242043 : Nat := 118140960795 + 242043 * 2 ^ 59
def prefixEnd_242043 : Nat := 4983230072969 + 3 ^ 40 * 242043 * 2
def baseEnd_242043 : Nat := 55237510247245217488609

theorem tailTrace_242043 : CollatzResearch.WordTrace tailWord_242043 prefixEnd_242043 55237510247245217488609 := by
  unfold tailWord_242043
  simp only [CollatzResearch.WordTrace]
  refine ⟨8828033462127023498450783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5885355641418015665633855 8828033462127023498450783)
  ·
    refine ⟨13242050193190535247676175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8828033462127023498450783 13242050193190535247676175)
    ·
      refine ⟨19863075289785802871514263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13242050193190535247676175 19863075289785802871514263)
      ·
        refine ⟨29794612934678704307271395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19863075289785802871514263 29794612934678704307271395)
        ·
          refine ⟨44691919402018056460907093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29794612934678704307271395 44691919402018056460907093)
          ·
            refine ⟨523733430492399099151255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 44691919402018056460907093 523733430492399099151255)
            ·
              refine ⟨785600145738598648726883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523733430492399099151255 785600145738598648726883)
              ·
                refine ⟨1178400218607897973090325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785600145738598648726883 1178400218607897973090325)
                ·
                  refine ⟨55237510247245217488609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1178400218607897973090325 55237510247245217488609)
                  ·
                    rfl

theorem cell21_242043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 6].length) (baseStart_242043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242043 prefixEnd_242043 := by exact prefixLift 242043
  have htrace : WordTrace (prefixWord ++ tailWord_242043) baseStart_242043 baseEnd_242043 := by
    simpa [prefixWord, tailWord_242043, baseEnd_242043] using wordTrace_append hprefix tailTrace_242043
  have hstable : (prefixWord ++ tailWord_242043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242043).length < 2 ^ (prefixWord ++ tailWord_242043).sum := by decide
  have hdescent : baseEnd_242043 < baseStart_242043 := by decide
  rcases family_descends (prefixWord ++ tailWord_242043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242074 : List Nat := [3, 1, 1, 4, 1, 3, 1, 7]
def baseStart_242074 : Nat := 118140960795 + 242074 * 2 ^ 59
def prefixEnd_242074 : Nat := 4983230072969 + 3 ^ 40 * 242074 * 2
def baseEnd_242074 : Nat := 18414861623198684157293

theorem tailTrace_242074 : CollatzResearch.WordTrace tailWord_242074 prefixEnd_242074 18414861623198684157293 := by
  unfold tailWord_242074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207291031253678948207319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5886109416676477195219517 2207291031253678948207319)
  ·
    refine ⟨3310936546880518422310979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2207291031253678948207319 3310936546880518422310979)
    ·
      refine ⟨4966404820320777633466469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3310936546880518422310979 4966404820320777633466469)
      ·
        refine ⟨931200903810145806274963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4966404820320777633466469 931200903810145806274963)
        ·
          refine ⟨1396801355715218709412445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931200903810145806274963 1396801355715218709412445)
          ·
            refine ⟨523800508393207016029667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1396801355715218709412445 523800508393207016029667)
            ·
              refine ⟨785700762589810524044501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523800508393207016029667 785700762589810524044501)
              ·
                refine ⟨18414861623198684157293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 785700762589810524044501 18414861623198684157293)
                ·
                  rfl

theorem cell21_242074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_242074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242074 prefixEnd_242074 := by exact prefixLift 242074
  have htrace : WordTrace (prefixWord ++ tailWord_242074) baseStart_242074 baseEnd_242074 := by
    simpa [prefixWord, tailWord_242074, baseEnd_242074] using wordTrace_append hprefix tailTrace_242074
  have hstable : (prefixWord ++ tailWord_242074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242074).length < 2 ^ (prefixWord ++ tailWord_242074).sum := by decide
  have hdescent : baseEnd_242074 < baseStart_242074 := by decide
  rcases family_descends (prefixWord ++ tailWord_242074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242105 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 5]
def baseStart_242105 : Nat := 118140960795 + 242105 * 2 ^ 59
def prefixEnd_242105 : Nat := 4983230072969 + 3 ^ 40 * 242105 * 2
def baseEnd_242105 : Nat := 55251659491946887455149

theorem tailTrace_242105 : CollatzResearch.WordTrace tailWord_242105 prefixEnd_242105 55251659491946887455149 := by
  unfold tailWord_242105
  simp only [CollatzResearch.WordTrace]
  refine ⟨8830294787902408087207769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5886863191934938724805179 8830294787902408087207769)
  ·
    refine ⟨6622721090926806065405827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8830294787902408087207769 6622721090926806065405827)
    ·
      refine ⟨9934081636390209098108741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6622721090926806065405827 9934081636390209098108741)
      ·
        refine ⟨1862640306823164205895389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9934081636390209098108741 1862640306823164205895389)
        ·
          refine ⟨698490115058686577210771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1862640306823164205895389 698490115058686577210771)
          ·
            refine ⟨1047735172588029865816157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 698490115058686577210771 1047735172588029865816157)
            ·
              refine ⟨392900689720511199681059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1047735172588029865816157 392900689720511199681059)
              ·
                refine ⟨589351034580766799521589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392900689720511199681059 589351034580766799521589)
                ·
                  refine ⟨55251659491946887455149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 589351034580766799521589 55251659491946887455149)
                  ·
                    rfl

theorem cell21_242105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_242105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242105 prefixEnd_242105 := by exact prefixLift 242105
  have htrace : WordTrace (prefixWord ++ tailWord_242105) baseStart_242105 baseEnd_242105 := by
    simpa [prefixWord, tailWord_242105, baseEnd_242105] using wordTrace_append hprefix tailTrace_242105
  have hstable : (prefixWord ++ tailWord_242105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242105).length < 2 ^ (prefixWord ++ tailWord_242105).sum := by decide
  have hdescent : baseEnd_242105 < baseStart_242105 := by decide
  rcases family_descends (prefixWord ++ tailWord_242105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242209 : List Nat := [1, 2, 3, 2, 2, 1, 10]
def baseStart_242209 : Nat := 118140960795 + 242209 * 2 ^ 59
def prefixEnd_242209 : Nat := 4983230072969 + 3 ^ 40 * 242209 * 2
def baseEnd_242209 : Nat := 6141710412096201969067

theorem tailTrace_242209 : CollatzResearch.WordTrace tailWord_242209 prefixEnd_242209 6141710412096201969067 := by
  unfold tailWord_242209
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834087979525633848993681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5889391986350422565995787 8834087979525633848993681)
  ·
    refine ⟨6625565984644225386745261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8834087979525633848993681 6625565984644225386745261)
    ·
      refine ⟨2484587244241584520029473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6625565984644225386745261 2484587244241584520029473)
      ·
        refine ⟨1863440433181188390022105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2484587244241584520029473 1863440433181188390022105)
        ·
          refine ⟨1397580324885891292516579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1863440433181188390022105 1397580324885891292516579)
          ·
            refine ⟨2096370487328836938774869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397580324885891292516579 2096370487328836938774869)
            ·
              refine ⟨6141710412096201969067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2096370487328836938774869 6141710412096201969067)
              ·
                rfl

theorem cell21_242209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 10].length) (baseStart_242209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242209 prefixEnd_242209 := by exact prefixLift 242209
  have htrace : WordTrace (prefixWord ++ tailWord_242209) baseStart_242209 baseEnd_242209 := by
    simpa [prefixWord, tailWord_242209, baseEnd_242209] using wordTrace_append hprefix tailTrace_242209
  have hstable : (prefixWord ++ tailWord_242209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242209).length < 2 ^ (prefixWord ++ tailWord_242209).sum := by decide
  have hdescent : baseEnd_242209 < baseStart_242209 := by decide
  rcases family_descends (prefixWord ++ tailWord_242209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242215 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 5]
def baseStart_242215 : Nat := 118140960795 + 242215 * 2 ^ 59
def prefixEnd_242215 : Nat := 4983230072969 + 3 ^ 40 * 242215 * 2
def baseEnd_242215 : Nat := 55276762990611140621591

theorem tailTrace_242215 : CollatzResearch.WordTrace tailWord_242215 prefixEnd_242215 55276762990611140621591 := by
  unfold tailWord_242215
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834306817503896873712099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5889537878335931249141399 8834306817503896873712099)
  ·
    refine ⟨13251460226255845310568149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8834306817503896873712099 13251460226255845310568149)
    ·
      refine ⟨310581099052871374466441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13251460226255845310568149 310581099052871374466441)
      ·
        refine ⟨232935824289653530849831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310581099052871374466441 232935824289653530849831)
        ·
          refine ⟨349403736434480296274747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232935824289653530849831 349403736434480296274747)
          ·
            refine ⟨524105604651720444412121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349403736434480296274747 524105604651720444412121)
            ·
              refine ⟨393079203488790333309091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 524105604651720444412121 393079203488790333309091)
              ·
                refine ⟨589618805233185499963637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 393079203488790333309091 589618805233185499963637)
                ·
                  refine ⟨55276762990611140621591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 589618805233185499963637 55276762990611140621591)
                  ·
                    rfl

theorem cell21_242215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 5].length) (baseStart_242215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242215 prefixEnd_242215 := by exact prefixLift 242215
  have htrace : WordTrace (prefixWord ++ tailWord_242215) baseStart_242215 baseEnd_242215 := by
    simpa [prefixWord, tailWord_242215, baseEnd_242215] using wordTrace_append hprefix tailTrace_242215
  have hstable : (prefixWord ++ tailWord_242215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242215).length < 2 ^ (prefixWord ++ tailWord_242215).sum := by decide
  have hdescent : baseEnd_242215 < baseStart_242215 := by decide
  rcases family_descends (prefixWord ++ tailWord_242215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242240 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_242240 : Nat := 118140960795 + 242240 * 2 ^ 59
def prefixEnd_242240 : Nat := 4983230072969 + 3 ^ 40 * 242240 * 2
def baseEnd_242240 : Nat := 55282468331216652704873

theorem tailTrace_242240 : CollatzResearch.WordTrace tailWord_242240 prefixEnd_242240 55282468331216652704873 := by
  unfold tailWord_242240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4417609321206663071686087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5890145761608884095581449 4417609321206663071686087)
  ·
    refine ⟨6626413981809994607529131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4417609321206663071686087 6626413981809994607529131)
    ·
      refine ⟨9939620972714991911293697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6626413981809994607529131 9939620972714991911293697)
      ·
        refine ⟨7454715729536243933470273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9939620972714991911293697 7454715729536243933470273)
        ·
          refine ⟨5591036797152182950102705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7454715729536243933470273 5591036797152182950102705)
          ·
            refine ⟨4193277597864137212577029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5591036797152182950102705 4193277597864137212577029)
            ·
              refine ⟨786239549599525727358193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4193277597864137212577029 786239549599525727358193)
              ·
                refine ⟨589679662199644295518645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 786239549599525727358193 589679662199644295518645)
                ·
                  refine ⟨55282468331216652704873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 589679662199644295518645 55282468331216652704873)
                  ·
                    rfl

theorem cell21_242240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_242240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242240 prefixEnd_242240 := by exact prefixLift 242240
  have htrace : WordTrace (prefixWord ++ tailWord_242240) baseStart_242240 baseEnd_242240 := by
    simpa [prefixWord, tailWord_242240, baseEnd_242240] using wordTrace_append hprefix tailTrace_242240
  have hstable : (prefixWord ++ tailWord_242240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242240).length < 2 ^ (prefixWord ++ tailWord_242240).sum := by decide
  have hdescent : baseEnd_242240 < baseStart_242240 := by decide
  rcases family_descends (prefixWord ++ tailWord_242240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_242288 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 4]
def baseStart_242288 : Nat := 118140960795 + 242288 * 2 ^ 59
def prefixEnd_242288 : Nat := 4983230072969 + 3 ^ 40 * 242288 * 2
def baseEnd_242288 : Nat := 55293422585179235904775

theorem tailTrace_242288 : CollatzResearch.WordTrace tailWord_242288 prefixEnd_242288 55293422585179235904775 := by
  unfold tailWord_242288
  simp only [CollatzResearch.WordTrace]
  refine ⟨4418484673119715170559759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5891312897492953560746345 4418484673119715170559759)
  ·
    refine ⟨6627727009679572755839639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4418484673119715170559759 6627727009679572755839639)
    ·
      refine ⟨9941590514519359133759459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6627727009679572755839639 9941590514519359133759459)
      ·
        refine ⟨14912385771779038700639189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9941590514519359133759459 14912385771779038700639189)
        ·
          refine ⟨349509041526071219546231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14912385771779038700639189 349509041526071219546231)
          ·
            refine ⟨524263562289106829319347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349509041526071219546231 524263562289106829319347)
            ·
              refine ⟨786395343433660243979021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524263562289106829319347 786395343433660243979021)
              ·
                refine ⟨294898253787622591492133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 786395343433660243979021 294898253787622591492133)
                ·
                  refine ⟨55293422585179235904775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 294898253787622591492133 55293422585179235904775)
                  ·
                    rfl

theorem cell21_242288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_242288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_242288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_242288 prefixEnd_242288 := by exact prefixLift 242288
  have htrace : WordTrace (prefixWord ++ tailWord_242288) baseStart_242288 baseEnd_242288 := by
    simpa [prefixWord, tailWord_242288, baseEnd_242288] using wordTrace_append hprefix tailTrace_242288
  have hstable : (prefixWord ++ tailWord_242288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_242288).length < 2 ^ (prefixWord ++ tailWord_242288).sum := by decide
  have hdescent : baseEnd_242288 < baseStart_242288 := by decide
  rcases family_descends (prefixWord ++ tailWord_242288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
