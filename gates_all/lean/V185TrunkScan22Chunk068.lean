import V185TrunkScan22Chunk067

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_611821 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 6]
def baseStart_611821 : Nat := 118140960795 + 611821 * 2 ^ 59
def prefixEnd_611821 : Nat := 4983230072969 + 3 ^ 40 * 611821 * 2
def baseEnd_611821 : Nat := 69812943892123551383065

theorem tailTrace_611821 : CollatzResearch.WordTrace tailWord_611821 prefixEnd_611821 69812943892123551383065 := by
  unfold tailWord_611821
  simp only [CollatzResearch.WordTrace]
  refine ⟨22314945116484482552979317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14876630077656321701986211 22314945116484482552979317)
  ·
    refine ⟨2092026104670420239341811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22314945116484482552979317 2092026104670420239341811)
    ·
      refine ⟨3138039157005630359012717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092026104670420239341811 3138039157005630359012717)
      ·
        refine ⟨1176764683877111384629769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3138039157005630359012717 1176764683877111384629769)
        ·
          refine ⟨882573512907833538472327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1176764683877111384629769 882573512907833538472327)
          ·
            refine ⟨1323860269361750307708491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882573512907833538472327 1323860269361750307708491)
            ·
              refine ⟨1985790404042625461562737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323860269361750307708491 1985790404042625461562737)
              ·
                refine ⟨1489342803031969096172053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1985790404042625461562737 1489342803031969096172053)
                ·
                  refine ⟨69812943892123551383065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1489342803031969096172053 69812943892123551383065)
                  ·
                    rfl

theorem cell22_611821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_611821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611821 prefixEnd_611821 := by exact prefixLift 611821
  have htrace : WordTrace (prefixWord ++ tailWord_611821) baseStart_611821 baseEnd_611821 := by
    simpa [prefixWord, tailWord_611821, baseEnd_611821] using wordTrace_append hprefix tailTrace_611821
  have hstable : (prefixWord ++ tailWord_611821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611821).length < 2 ^ (prefixWord ++ tailWord_611821).sum := by decide
  have hdescent : baseEnd_611821 < baseStart_611821 := by decide
  rcases family_descends (prefixWord ++ tailWord_611821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_611941 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_611941 : Nat := 118140960795 + 611941 * 2 ^ 59
def prefixEnd_611941 : Nat := 4983230072969 + 3 ^ 40 * 611941 * 2
def baseEnd_611941 : Nat := 209479910128730341148827

theorem tailTrace_611941 : CollatzResearch.WordTrace tailWord_611941 prefixEnd_611941 209479910128730341148827 := by
  unfold tailWord_611941
  simp only [CollatzResearch.WordTrace]
  refine ⟨22319321876049743047347677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14879547917366495364898451 22319321876049743047347677)
  ·
    refine ⟨8369745703518653642755379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22319321876049743047347677 8369745703518653642755379)
    ·
      refine ⟨12554618555277980464133069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8369745703518653642755379 12554618555277980464133069)
      ·
        refine ⟨4707981958229242674049901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12554618555277980464133069 4707981958229242674049901)
        ·
          refine ⟨1765493234335966002768713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4707981958229242674049901 1765493234335966002768713)
          ·
            refine ⟨1324119925751974502076535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1765493234335966002768713 1324119925751974502076535)
            ·
              refine ⟨1986179888627961753114803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324119925751974502076535 1986179888627961753114803)
              ·
                refine ⟨2979269832941942629672205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1986179888627961753114803 2979269832941942629672205)
                ·
                  refine ⟨1117226187353228486127077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2979269832941942629672205 1117226187353228486127077)
                  ·
                    refine ⟨209479910128730341148827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1117226187353228486127077 209479910128730341148827)
                    ·
                      rfl

theorem cell22_611941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_611941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_611941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_611941 prefixEnd_611941 := by exact prefixLift 611941
  have htrace : WordTrace (prefixWord ++ tailWord_611941) baseStart_611941 baseEnd_611941 := by
    simpa [prefixWord, tailWord_611941, baseEnd_611941] using wordTrace_append hprefix tailTrace_611941
  have hstable : (prefixWord ++ tailWord_611941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_611941).length < 2 ^ (prefixWord ++ tailWord_611941).sum := by decide
  have hdescent : baseEnd_611941 < baseStart_611941 := by decide
  rcases family_descends (prefixWord ++ tailWord_611941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612022 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_612022 : Nat := 118140960795 + 612022 * 2 ^ 59
def prefixEnd_612022 : Nat := 4983230072969 + 3 ^ 40 * 612022 * 2
def baseEnd_612022 : Nat := 209507638084073129873579

theorem tailTrace_612022 : CollatzResearch.WordTrace tailWord_612022 prefixEnd_612022 209507638084073129873579 := by
  unfold tailWord_612022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1395142261797268367565395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14881517459170862587364213 1395142261797268367565395)
  ·
    refine ⟨2092713392695902551348093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1395142261797268367565395 2092713392695902551348093)
    ·
      refine ⟨784767522260963456755535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2092713392695902551348093 784767522260963456755535)
      ·
        refine ⟨1177151283391445185133303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784767522260963456755535 1177151283391445185133303)
        ·
          refine ⟨1765726925087167777699955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1177151283391445185133303 1765726925087167777699955)
          ·
            refine ⟨2648590387630751666549933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765726925087167777699955 2648590387630751666549933)
            ·
              refine ⟨993221395361531874956225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2648590387630751666549933 993221395361531874956225)
              ·
                refine ⟨744916046521148906217169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993221395361531874956225 744916046521148906217169)
                ·
                  refine ⟨558687034890861679662877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 744916046521148906217169 558687034890861679662877)
                  ·
                    refine ⟨209507638084073129873579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 558687034890861679662877 209507638084073129873579)
                    ·
                      rfl

theorem cell22_612022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_612022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612022 prefixEnd_612022 := by exact prefixLift 612022
  have htrace : WordTrace (prefixWord ++ tailWord_612022) baseStart_612022 baseEnd_612022 := by
    simpa [prefixWord, tailWord_612022, baseEnd_612022] using wordTrace_append hprefix tailTrace_612022
  have hstable : (prefixWord ++ tailWord_612022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612022).length < 2 ^ (prefixWord ++ tailWord_612022).sum := by decide
  have hdescent : baseEnd_612022 < baseStart_612022 := by decide
  rcases family_descends (prefixWord ++ tailWord_612022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612084 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_612084 : Nat := 118140960795 + 612084 * 2 ^ 59
def prefixEnd_612084 : Nat := 4983230072969 + 3 ^ 40 * 612084 * 2
def baseEnd_612084 : Nat := 209528861951125634823389

theorem tailTrace_612084 : CollatzResearch.WordTrace tailWord_612084 prefixEnd_612084 209528861951125634823389 := by
  unfold tailWord_612084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11162268757265839234901653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14883025009687785646535537 11162268757265839234901653)
  ·
    refine ⟨523231347996836214136015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11162268757265839234901653 523231347996836214136015)
    ·
      refine ⟨784847021995254321204023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 523231347996836214136015 784847021995254321204023)
      ·
        refine ⟨1177270532992881481806035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784847021995254321204023 1177270532992881481806035)
        ·
          refine ⟨1765905799489322222709053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1177270532992881481806035 1765905799489322222709053)
          ·
            refine ⟨662214674808495833515895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1765905799489322222709053 662214674808495833515895)
            ·
              refine ⟨993322012212743750273843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662214674808495833515895 993322012212743750273843)
              ·
                refine ⟨1489983018319115625410765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993322012212743750273843 1489983018319115625410765)
                ·
                  refine ⟨558743631869668359529037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1489983018319115625410765 558743631869668359529037)
                  ·
                    refine ⟨209528861951125634823389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 558743631869668359529037 209528861951125634823389)
                    ·
                      rfl

theorem cell22_612084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_612084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612084 prefixEnd_612084 := by exact prefixLift 612084
  have htrace : WordTrace (prefixWord ++ tailWord_612084) baseStart_612084 baseEnd_612084 := by
    simpa [prefixWord, tailWord_612084, baseEnd_612084] using wordTrace_append hprefix tailTrace_612084
  have hstable : (prefixWord ++ tailWord_612084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612084).length < 2 ^ (prefixWord ++ tailWord_612084).sum := by decide
  have hdescent : baseEnd_612084 < baseStart_612084 := by decide
  rcases family_descends (prefixWord ++ tailWord_612084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612136 : List Nat := [2, 1, 5, 1, 1, 12]
def baseStart_612136 : Nat := 118140960795 + 612136 * 2 ^ 59
def prefixEnd_612136 : Nat := 4983230072969 + 3 ^ 40 * 612136 * 2
def baseEnd_612136 : Nat := 2586995834738454722509

theorem tailTrace_612136 : CollatzResearch.WordTrace tailWord_612136 prefixEnd_612136 2586995834738454722509 := by
  unfold tailWord_612136
  simp only [CollatzResearch.WordTrace]
  refine ⟨11163217055171645675348131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14884289406895527567130841 11163217055171645675348131)
  ·
    refine ⟨16744825582757468513022197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11163217055171645675348131 16744825582757468513022197)
    ·
      refine ⟨1569827398383512673095831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16744825582757468513022197 1569827398383512673095831)
      ·
        refine ⟨2354741097575269009643747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569827398383512673095831 2354741097575269009643747)
        ·
          refine ⟨3532111646362903514465621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2354741097575269009643747 3532111646362903514465621)
          ·
            refine ⟨2586995834738454722509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3532111646362903514465621 2586995834738454722509)
            ·
              rfl

theorem cell22_612136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 12].length) (baseStart_612136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612136 prefixEnd_612136 := by exact prefixLift 612136
  have htrace : WordTrace (prefixWord ++ tailWord_612136) baseStart_612136 baseEnd_612136 := by
    simpa [prefixWord, tailWord_612136, baseEnd_612136] using wordTrace_append hprefix tailTrace_612136
  have hstable : (prefixWord ++ tailWord_612136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612136).length < 2 ^ (prefixWord ++ tailWord_612136).sum := by decide
  have hdescent : baseEnd_612136 < baseStart_612136 := by decide
  rcases family_descends (prefixWord ++ tailWord_612136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612140 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 2, 3]
def baseStart_612140 : Nat := 118140960795 + 612140 * 2 ^ 59
def prefixEnd_612140 : Nat := 4983230072969 + 3 ^ 40 * 612140 * 2
def baseEnd_612140 : Nat := 209548031895560155423217

theorem tailTrace_612140 : CollatzResearch.WordTrace tailWord_612140 prefixEnd_612140 209548031895560155423217 := by
  unfold tailWord_612140
  simp only [CollatzResearch.WordTrace]
  refine ⟨11163290001164400016920937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14884386668219200022561249 11163290001164400016920937)
  ·
    refine ⟨8372467500873300012690703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11163290001164400016920937 8372467500873300012690703)
    ·
      refine ⟨12558701251309950019036055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8372467500873300012690703 12558701251309950019036055)
      ·
        refine ⟨18838051876964925028554083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12558701251309950019036055 18838051876964925028554083)
        ·
          refine ⟨28257077815447387542831125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18838051876964925028554083 28257077815447387542831125)
          ·
            refine ⟨1324550522599096291070209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28257077815447387542831125 1324550522599096291070209)
            ·
              refine ⟨993412891949322218302657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1324550522599096291070209 993412891949322218302657)
              ·
                refine ⟨745059668961991663726993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993412891949322218302657 745059668961991663726993)
                ·
                  refine ⟨558794751721493747795245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 745059668961991663726993 558794751721493747795245)
                  ·
                    refine ⟨209548031895560155423217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 558794751721493747795245 209548031895560155423217)
                    ·
                      rfl

theorem cell22_612140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_612140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612140 prefixEnd_612140 := by exact prefixLift 612140
  have htrace : WordTrace (prefixWord ++ tailWord_612140) baseStart_612140 baseEnd_612140 := by
    simpa [prefixWord, tailWord_612140, baseEnd_612140] using wordTrace_append hprefix tailTrace_612140
  have hstable : (prefixWord ++ tailWord_612140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612140).length < 2 ^ (prefixWord ++ tailWord_612140).sum := by decide
  have hdescent : baseEnd_612140 < baseStart_612140 := by decide
  rcases family_descends (prefixWord ++ tailWord_612140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612142 : List Nat := [4, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_612142 : Nat := 118140960795 + 612142 * 2 ^ 59
def prefixEnd_612142 : Nat := 4983230072969 + 3 ^ 40 * 612142 * 2
def baseEnd_612142 : Nat := 69849572178810938957737

theorem tailTrace_612142 : CollatzResearch.WordTrace tailWord_612142 prefixEnd_612142 69849572178810938957737 := by
  unfold tailWord_612142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2790831618540194296926835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14884435298881036250276453 2790831618540194296926835)
  ·
    refine ⟨4186247427810291445390253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2790831618540194296926835 4186247427810291445390253)
    ·
      refine ⟨1569842785428859292021345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4186247427810291445390253 1569842785428859292021345)
      ·
        refine ⟨1177382089071644469016009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1569842785428859292021345 1177382089071644469016009)
        ·
          refine ⟨883036566803733351762007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1177382089071644469016009 883036566803733351762007)
          ·
            refine ⟨1324554850205600027643011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883036566803733351762007 1324554850205600027643011)
            ·
              refine ⟨1986832275308400041464517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324554850205600027643011 1986832275308400041464517)
              ·
                refine ⟨372531051620325007774597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1986832275308400041464517 372531051620325007774597)
                ·
                  refine ⟨69849572178810938957737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372531051620325007774597 69849572178810938957737)
                  ·
                    rfl

theorem cell22_612142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_612142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612142 prefixEnd_612142 := by exact prefixLift 612142
  have htrace : WordTrace (prefixWord ++ tailWord_612142) baseStart_612142 baseEnd_612142 := by
    simpa [prefixWord, tailWord_612142, baseEnd_612142] using wordTrace_append hprefix tailTrace_612142
  have hstable : (prefixWord ++ tailWord_612142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612142).length < 2 ^ (prefixWord ++ tailWord_612142).sum := by decide
  have hdescent : baseEnd_612142 < baseStart_612142 := by decide
  rcases family_descends (prefixWord ++ tailWord_612142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612168 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 5, 3]
def baseStart_612168 : Nat := 118140960795 + 612168 * 2 ^ 59
def prefixEnd_612168 : Nat := 4983230072969 + 3 ^ 40 * 612168 * 2
def baseEnd_612168 : Nat := 209557616867777415723131

theorem tailTrace_612168 : CollatzResearch.WordTrace tailWord_612168 prefixEnd_612168 209557616867777415723131 := by
  unfold tailWord_612168
  simp only [CollatzResearch.WordTrace]
  refine ⟨11163800623113680407930579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14885067497484907210574105 11163800623113680407930579)
  ·
    refine ⟨16745700934670520611895869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11163800623113680407930579 16745700934670520611895869)
    ·
      refine ⟨6279637850501445229460951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16745700934670520611895869 6279637850501445229460951)
      ·
        refine ⟨9419456775752167844191427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6279637850501445229460951 9419456775752167844191427)
        ·
          refine ⟨14129185163628251766287141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9419456775752167844191427 14129185163628251766287141)
          ·
            refine ⟨2649222218180297206178839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14129185163628251766287141 2649222218180297206178839)
            ·
              refine ⟨3973833327270445809268259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649222218180297206178839 3973833327270445809268259)
              ·
                refine ⟨5960749990905668713902389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3973833327270445809268259 5960749990905668713902389)
                ·
                  refine ⟨558820311647406441928349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5960749990905668713902389 558820311647406441928349)
                  ·
                    refine ⟨209557616867777415723131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 558820311647406441928349 209557616867777415723131)
                    ·
                      rfl

theorem cell22_612168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_612168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612168 prefixEnd_612168 := by exact prefixLift 612168
  have htrace : WordTrace (prefixWord ++ tailWord_612168) baseStart_612168 baseEnd_612168 := by
    simpa [prefixWord, tailWord_612168, baseEnd_612168] using wordTrace_append hprefix tailTrace_612168
  have hstable : (prefixWord ++ tailWord_612168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612168).length < 2 ^ (prefixWord ++ tailWord_612168).sum := by decide
  have hdescent : baseEnd_612168 < baseStart_612168 := by decide
  rcases family_descends (prefixWord ++ tailWord_612168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612172 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 2, 4]
def baseStart_612172 : Nat := 118140960795 + 612172 * 2 ^ 59
def prefixEnd_612172 : Nat := 4983230072969 + 3 ^ 40 * 612172 * 2
def baseEnd_612172 : Nat := 209558986149522738623119

theorem tailTrace_612172 : CollatzResearch.WordTrace tailWord_612172 prefixEnd_612172 209558986149522738623119 := by
  unfold tailWord_612172
  simp only [CollatzResearch.WordTrace]
  refine ⟨11163873569106434749503385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14885164758808579666004513 11163873569106434749503385)
  ·
    refine ⟨8372905176829826062127539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11163873569106434749503385 8372905176829826062127539)
    ·
      refine ⟨12559357765244739093191309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8372905176829826062127539 12559357765244739093191309)
      ·
        refine ⟨4709759161966777159946741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12559357765244739093191309 4709759161966777159946741)
        ·
          refine ⟨441539921434385358745007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4709759161966777159946741 441539921434385358745007)
          ·
            refine ⟨662309882151578038117511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441539921434385358745007 662309882151578038117511)
            ·
              refine ⟨993464823227367057176267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662309882151578038117511 993464823227367057176267)
              ·
                refine ⟨1490197234841050585764401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993464823227367057176267 1490197234841050585764401)
                ·
                  refine ⟨1117647926130787939323301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1490197234841050585764401 1117647926130787939323301)
                  ·
                    refine ⟨209558986149522738623119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1117647926130787939323301 209558986149522738623119)
                    ·
                      rfl

theorem cell22_612172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_612172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612172 prefixEnd_612172 := by exact prefixLift 612172
  have htrace : WordTrace (prefixWord ++ tailWord_612172) baseStart_612172 baseEnd_612172 := by
    simpa [prefixWord, tailWord_612172, baseEnd_612172] using wordTrace_append hprefix tailTrace_612172
  have hstable : (prefixWord ++ tailWord_612172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612172).length < 2 ^ (prefixWord ++ tailWord_612172).sum := by decide
  have hdescent : baseEnd_612172 < baseStart_612172 := by decide
  rcases family_descends (prefixWord ++ tailWord_612172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612213 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_612213 : Nat := 118140960795 + 612213 * 2 ^ 59
def prefixEnd_612213 : Nat := 4983230072969 + 3 ^ 40 * 612213 * 2
def baseEnd_612213 : Nat := 209573021287412298347993

theorem tailTrace_612213 : CollatzResearch.WordTrace tailWord_612213 prefixEnd_612213 209573021287412298347993 := by
  unfold tailWord_612213
  simp only [CollatzResearch.WordTrace]
  refine ⟨22329242531064333501249293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14886161687376222334166195 22329242531064333501249293)
  ·
    refine ⟨8373465949149125062968485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22329242531064333501249293 8373465949149125062968485)
    ·
      refine ⟨1570024865465460949306591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8373465949149125062968485 1570024865465460949306591)
      ·
        refine ⟨2355037298198191423959887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1570024865465460949306591 2355037298198191423959887)
        ·
          refine ⟨3532555947297287135939831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2355037298198191423959887 3532555947297287135939831)
          ·
            refine ⟨5298833920945930703909747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3532555947297287135939831 5298833920945930703909747)
            ·
              refine ⟨7948250881418896055864621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5298833920945930703909747 7948250881418896055864621)
              ·
                refine ⟨2980594080532086020949233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7948250881418896055864621 2980594080532086020949233)
                ·
                  refine ⟨2235445560399064515711925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2980594080532086020949233 2235445560399064515711925)
                  ·
                    refine ⟨209573021287412298347993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2235445560399064515711925 209573021287412298347993)
                    ·
                      rfl

theorem cell22_612213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_612213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612213 prefixEnd_612213 := by exact prefixLift 612213
  have htrace : WordTrace (prefixWord ++ tailWord_612213) baseStart_612213 baseEnd_612213 := by
    simpa [prefixWord, tailWord_612213, baseEnd_612213] using wordTrace_append hprefix tailTrace_612213
  have hstable : (prefixWord ++ tailWord_612213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612213).length < 2 ^ (prefixWord ++ tailWord_612213).sum := by decide
  have hdescent : baseEnd_612213 < baseStart_612213 := by decide
  rcases family_descends (prefixWord ++ tailWord_612213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612228 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_612228 : Nat := 118140960795 + 612228 * 2 ^ 59
def prefixEnd_612228 : Nat := 4983230072969 + 3 ^ 40 * 612228 * 2
def baseEnd_612228 : Nat := 209578156093957259222947

theorem tailTrace_612228 : CollatzResearch.WordTrace tailWord_612228 prefixEnd_612228 209578156093957259222947 := by
  unfold tailWord_612228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11164894813004995531522669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14886526417339994042030225 11164894813004995531522669)
  ·
    refine ⟨4186835554876873324321001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11164894813004995531522669 4186835554876873324321001)
    ·
      refine ⟨3140126666157654993240751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4186835554876873324321001 3140126666157654993240751)
      ·
        refine ⟨4710189999236482489861127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3140126666157654993240751 4710189999236482489861127)
        ·
          refine ⟨7065284998854723734791691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4710189999236482489861127 7065284998854723734791691)
          ·
            refine ⟨10597927498282085602187537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7065284998854723734791691 10597927498282085602187537)
            ·
              refine ⟨7948445623711564201640653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10597927498282085602187537 7948445623711564201640653)
              ·
                refine ⟨2980667108891836575615245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7948445623711564201640653 2980667108891836575615245)
                ·
                  refine ⟨1117750165834438715855717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2980667108891836575615245 1117750165834438715855717)
                  ·
                    refine ⟨209578156093957259222947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1117750165834438715855717 209578156093957259222947)
                    ·
                      rfl

theorem cell22_612228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_612228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612228 prefixEnd_612228 := by exact prefixLift 612228
  have htrace : WordTrace (prefixWord ++ tailWord_612228) baseStart_612228 baseEnd_612228 := by
    simpa [prefixWord, tailWord_612228, baseEnd_612228] using wordTrace_append hprefix tailTrace_612228
  have hstable : (prefixWord ++ tailWord_612228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612228).length < 2 ^ (prefixWord ++ tailWord_612228).sum := by decide
  have hdescent : baseEnd_612228 < baseStart_612228 := by decide
  rcases family_descends (prefixWord ++ tailWord_612228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612260 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 6]
def baseStart_612260 : Nat := 118140960795 + 612260 * 2 ^ 59
def prefixEnd_612260 : Nat := 4983230072969 + 3 ^ 40 * 612260 * 2
def baseEnd_612260 : Nat := 69863036782639947474283

theorem tailTrace_612260 : CollatzResearch.WordTrace tailWord_612260 prefixEnd_612260 69863036782639947474283 := by
  unfold tailWord_612260
  simp only [CollatzResearch.WordTrace]
  refine ⟨11165478380947030264105117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14887304507929373685473489 11165478380947030264105117)
  ·
    refine ⟨4187054392855136349039419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11165478380947030264105117 4187054392855136349039419)
    ·
      refine ⟨6280581589282704523559129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4187054392855136349039419 6280581589282704523559129)
      ·
        refine ⟨4710436191962028392669347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6280581589282704523559129 4710436191962028392669347)
        ·
          refine ⟨7065654287943042589004021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4710436191962028392669347 7065654287943042589004021)
          ·
            refine ⟨662405089494660242719127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7065654287943042589004021 662405089494660242719127)
            ·
              refine ⟨993607634241990364078691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662405089494660242719127 993607634241990364078691)
              ·
                refine ⟨1490411451362985546118037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993607634241990364078691 1490411451362985546118037)
                ·
                  refine ⟨69863036782639947474283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1490411451362985546118037 69863036782639947474283)
                  ·
                    rfl

theorem cell22_612260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_612260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612260 prefixEnd_612260 := by exact prefixLift 612260
  have htrace : WordTrace (prefixWord ++ tailWord_612260) baseStart_612260 baseEnd_612260 := by
    simpa [prefixWord, tailWord_612260, baseEnd_612260] using wordTrace_append hprefix tailTrace_612260
  have hstable : (prefixWord ++ tailWord_612260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612260).length < 2 ^ (prefixWord ++ tailWord_612260).sum := by decide
  have hdescent : baseEnd_612260 < baseStart_612260 := by decide
  rcases family_descends (prefixWord ++ tailWord_612260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612275 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 2, 3]
def baseStart_612275 : Nat := 118140960795 + 612275 * 2 ^ 59
def prefixEnd_612275 : Nat := 4983230072969 + 3 ^ 40 * 612275 * 2
def baseEnd_612275 : Nat := 209594245154464803297803

theorem tailTrace_612275 : CollatzResearch.WordTrace tailWord_612275 prefixEnd_612275 209594245154464803297803 := by
  unfold tailWord_612275
  simp only [CollatzResearch.WordTrace]
  refine ⟨22331503856839718090006279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14887669237893145393337519 22331503856839718090006279)
  ·
    refine ⟨33497255785259577135009419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22331503856839718090006279 33497255785259577135009419)
    ·
      refine ⟨50245883677889365702514129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33497255785259577135009419 50245883677889365702514129)
      ·
        refine ⟨37684412758417024276885597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50245883677889365702514129 37684412758417024276885597)
        ·
          refine ⟨14131654784406384103832099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37684412758417024276885597 14131654784406384103832099)
          ·
            refine ⟨21197482176609576155748149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14131654784406384103832099 21197482176609576155748149)
            ·
              refine ⟨1987263954057147764601389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21197482176609576155748149 1987263954057147764601389)
              ·
                refine ⟨745223982771430411725521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1987263954057147764601389 745223982771430411725521)
                ·
                  refine ⟨558917987078572808794141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 745223982771430411725521 558917987078572808794141)
                  ·
                    refine ⟨209594245154464803297803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 558917987078572808794141 209594245154464803297803)
                    ·
                      rfl

theorem cell22_612275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 3].length) (baseStart_612275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612275 prefixEnd_612275 := by exact prefixLift 612275
  have htrace : WordTrace (prefixWord ++ tailWord_612275) baseStart_612275 baseEnd_612275 := by
    simpa [prefixWord, tailWord_612275, baseEnd_612275] using wordTrace_append hprefix tailTrace_612275
  have hstable : (prefixWord ++ tailWord_612275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612275).length < 2 ^ (prefixWord ++ tailWord_612275).sum := by decide
  have hdescent : baseEnd_612275 < baseStart_612275 := by decide
  rcases family_descends (prefixWord ++ tailWord_612275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612337 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 3, 3]
def baseStart_612337 : Nat := 118140960795 + 612337 * 2 ^ 59
def prefixEnd_612337 : Nat := 4983230072969 + 3 ^ 40 * 612337 * 2
def baseEnd_612337 : Nat := 209615469021517308247613

theorem tailTrace_612337 : CollatzResearch.WordTrace tailWord_612337 prefixEnd_612337 209615469021517308247613 := by
  unfold tailWord_612337
  simp only [CollatzResearch.WordTrace]
  refine ⟨22333765182615102678763265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14889176788410068452508843 22333765182615102678763265)
  ·
    refine ⟨16750323886961327009072449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22333765182615102678763265 16750323886961327009072449)
    ·
      refine ⟨12562742915220995256804337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16750323886961327009072449 12562742915220995256804337)
      ·
        refine ⟨9422057186415746442603253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12562742915220995256804337 9422057186415746442603253)
        ·
          refine ⟨883317861226476228994055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9422057186415746442603253 883317861226476228994055)
          ·
            refine ⟨1324976791839714343491083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883317861226476228994055 1324976791839714343491083)
            ·
              refine ⟨1987465187759571515236625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324976791839714343491083 1987465187759571515236625)
              ·
                refine ⟨1490598890819678636427469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1987465187759571515236625 1490598890819678636427469)
                ·
                  refine ⟨558974584057379488660301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1490598890819678636427469 558974584057379488660301)
                  ·
                    refine ⟨209615469021517308247613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 558974584057379488660301 209615469021517308247613)
                    ·
                      rfl

theorem cell22_612337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_612337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612337 prefixEnd_612337 := by exact prefixLift 612337
  have htrace : WordTrace (prefixWord ++ tailWord_612337) baseStart_612337 baseEnd_612337 := by
    simpa [prefixWord, tailWord_612337, baseEnd_612337] using wordTrace_append hprefix tailTrace_612337
  have hstable : (prefixWord ++ tailWord_612337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612337).length < 2 ^ (prefixWord ++ tailWord_612337).sum := by decide
  have hdescent : baseEnd_612337 < baseStart_612337 := by decide
  rcases family_descends (prefixWord ++ tailWord_612337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612348 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_612348 : Nat := 118140960795 + 612348 * 2 ^ 59
def prefixEnd_612348 : Nat := 4983230072969 + 3 ^ 40 * 612348 * 2
def baseEnd_612348 : Nat := 209619234546316946222579

theorem tailTrace_612348 : CollatzResearch.WordTrace tailWord_612348 prefixEnd_612348 209619234546316946222579 := by
  unfold tailWord_612348
  simp only [CollatzResearch.WordTrace]
  refine ⟨11167083192787625778706849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14889444257050167704942465 11167083192787625778706849)
  ·
    refine ⟨8375312394590719334030137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11167083192787625778706849 8375312394590719334030137)
    ·
      refine ⟨6281484295943039500522603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8375312394590719334030137 6281484295943039500522603)
      ·
        refine ⟨9422226443914559250783905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6281484295943039500522603 9422226443914559250783905)
        ·
          refine ⟨7066669832935919438087929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9422226443914559250783905 7066669832935919438087929)
          ·
            refine ⟨5300002374701939578565947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7066669832935919438087929 5300002374701939578565947)
            ·
              refine ⟨7950003562052909367848921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5300002374701939578565947 7950003562052909367848921)
              ·
                refine ⟨5962502671539682025886691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7950003562052909367848921 5962502671539682025886691)
                ·
                  refine ⟨8943754007309523038830037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5962502671539682025886691 8943754007309523038830037)
                  ·
                    refine ⟨209619234546316946222579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8943754007309523038830037 209619234546316946222579)
                    ·
                      rfl

theorem cell22_612348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_612348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612348 prefixEnd_612348 := by exact prefixLift 612348
  have htrace : WordTrace (prefixWord ++ tailWord_612348) baseStart_612348 baseEnd_612348 := by
    simpa [prefixWord, tailWord_612348, baseEnd_612348] using wordTrace_append hprefix tailTrace_612348
  have hstable : (prefixWord ++ tailWord_612348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612348).length < 2 ^ (prefixWord ++ tailWord_612348).sum := by decide
  have hdescent : baseEnd_612348 < baseStart_612348 := by decide
  rcases family_descends (prefixWord ++ tailWord_612348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612425 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 2, 4]
def baseStart_612425 : Nat := 118140960795 + 612425 * 2 ^ 59
def prefixEnd_612425 : Nat := 4983230072969 + 3 ^ 40 * 612425 * 2
def baseEnd_612425 : Nat := 209645593219914412047343

theorem tailTrace_612425 : CollatzResearch.WordTrace tailWord_612425 prefixEnd_612425 209645593219914412047343 := by
  unfold tailWord_612425
  simp only [CollatzResearch.WordTrace]
  refine ⟨22336974806296293707966729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14891316537530862471977819 22336974806296293707966729)
  ·
    refine ⟨16752731104722220280975047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22336974806296293707966729 16752731104722220280975047)
    ·
      refine ⟨25129096657083330421462571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16752731104722220280975047 25129096657083330421462571)
      ·
        refine ⟨37693644985624995632193857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25129096657083330421462571 37693644985624995632193857)
        ·
          refine ⟨28270233739218746724145393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37693644985624995632193857 28270233739218746724145393)
          ·
            refine ⟨21202675304414060043109045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28270233739218746724145393 21202675304414060043109045)
            ·
              refine ⟨1987750809788818129041473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21202675304414060043109045 1987750809788818129041473)
              ·
                refine ⟨1490813107341613596781105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1987750809788818129041473 1490813107341613596781105)
                ·
                  refine ⟨1118109830506210197585829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1490813107341613596781105 1118109830506210197585829)
                  ·
                    refine ⟨209645593219914412047343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1118109830506210197585829 209645593219914412047343)
                    ·
                      rfl

theorem cell22_612425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_612425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612425 prefixEnd_612425 := by exact prefixLift 612425
  have htrace : WordTrace (prefixWord ++ tailWord_612425) baseStart_612425 baseEnd_612425 := by
    simpa [prefixWord, tailWord_612425, baseEnd_612425] using wordTrace_append hprefix tailTrace_612425
  have hstable : (prefixWord ++ tailWord_612425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612425).length < 2 ^ (prefixWord ++ tailWord_612425).sum := by decide
  have hdescent : baseEnd_612425 < baseStart_612425 := by decide
  rcases family_descends (prefixWord ++ tailWord_612425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612440 : List Nat := [2, 1, 2, 2, 1, 5, 2, 7]
def baseStart_612440 : Nat := 118140960795 + 612440 * 2 ^ 59
def prefixEnd_612440 : Nat := 4983230072969 + 3 ^ 40 * 612440 * 2
def baseEnd_612440 : Nat := 23294525336273263658033

theorem tailTrace_612440 : CollatzResearch.WordTrace tailWord_612440 prefixEnd_612440 23294525336273263658033 := by
  unfold tailWord_612440
  simp only [CollatzResearch.WordTrace]
  refine ⟨11168760950620975634881387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14891681267494634179841849 11168760950620975634881387)
  ·
    refine ⟨16753141425931463452322081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11168760950620975634881387 16753141425931463452322081)
    ·
      refine ⟨12564856069448597589241561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16753141425931463452322081 12564856069448597589241561)
      ·
        refine ⟨9423642052086448191931171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12564856069448597589241561 9423642052086448191931171)
        ·
          refine ⟨14135463078129672287896757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9423642052086448191931171 14135463078129672287896757)
          ·
            refine ⟨1325199663574656776990321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14135463078129672287896757 1325199663574656776990321)
            ·
              refine ⟨993899747680992582742741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1325199663574656776990321 993899747680992582742741)
              ·
                refine ⟨23294525336273263658033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 993899747680992582742741 23294525336273263658033)
                ·
                  rfl

theorem cell22_612440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 7].length) (baseStart_612440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612440 prefixEnd_612440 := by exact prefixLift 612440
  have htrace : WordTrace (prefixWord ++ tailWord_612440) baseStart_612440 baseEnd_612440 := by
    simpa [prefixWord, tailWord_612440, baseEnd_612440] using wordTrace_append hprefix tailTrace_612440
  have hstable : (prefixWord ++ tailWord_612440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612440).length < 2 ^ (prefixWord ++ tailWord_612440).sum := by decide
  have hdescent : baseEnd_612440 < baseStart_612440 := by decide
  rcases family_descends (prefixWord ++ tailWord_612440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612444 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 2, 3]
def baseStart_612444 : Nat := 118140960795 + 612444 * 2 ^ 59
def prefixEnd_612444 : Nat := 4983230072969 + 3 ^ 40 * 612444 * 2
def baseEnd_612444 : Nat := 209652097308204695822285

theorem tailTrace_612444 : CollatzResearch.WordTrace tailWord_612444 prefixEnd_612444 209652097308204695822285 := by
  unfold tailWord_612444
  simp only [CollatzResearch.WordTrace]
  refine ⟨11168833896613729976454193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14891778528818306635272257 11168833896613729976454193)
  ·
    refine ⟨8376625422460297482340645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11168833896613729976454193 8376625422460297482340645)
    ·
      refine ⟨1570617266711305777938871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8376625422460297482340645 1570617266711305777938871)
      ·
        refine ⟨2355925900066958666908307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1570617266711305777938871 2355925900066958666908307)
        ·
          refine ⟨3533888850100438000362461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2355925900066958666908307 3533888850100438000362461)
          ·
            refine ⟨1325208318787664250135923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3533888850100438000362461 1325208318787664250135923)
            ·
              refine ⟨1987812478181496375203885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325208318787664250135923 1987812478181496375203885)
              ·
                refine ⟨745429679318061140701457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1987812478181496375203885 745429679318061140701457)
                ·
                  refine ⟨559072259488545855526093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 745429679318061140701457 559072259488545855526093)
                  ·
                    refine ⟨209652097308204695822285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 559072259488545855526093 209652097308204695822285)
                    ·
                      rfl

theorem cell22_612444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_612444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612444 prefixEnd_612444 := by exact prefixLift 612444
  have htrace : WordTrace (prefixWord ++ tailWord_612444) baseStart_612444 baseEnd_612444 := by
    simpa [prefixWord, tailWord_612444, baseEnd_612444] using wordTrace_append hprefix tailTrace_612444
  have hstable : (prefixWord ++ tailWord_612444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612444).length < 2 ^ (prefixWord ++ tailWord_612444).sum := by decide
  have hdescent : baseEnd_612444 < baseStart_612444 := by decide
  rcases family_descends (prefixWord ++ tailWord_612444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612489 : List Nat := [1, 2, 1, 1, 4, 2, 3, 4, 1, 3]
def baseStart_612489 : Nat := 118140960795 + 612489 * 2 ^ 59
def prefixEnd_612489 : Nat := 4983230072969 + 3 ^ 40 * 612489 * 2
def baseEnd_612489 : Nat := 209667501727839578447147

theorem tailTrace_612489 : CollatzResearch.WordTrace tailWord_612489 prefixEnd_612489 209667501727839578447147 := by
  unfold tailWord_612489
  simp only [CollatzResearch.WordTrace]
  refine ⟨22339309078064432638296521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14892872718709621758864347 22339309078064432638296521)
  ·
    refine ⟨16754481808548324478722391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22339309078064432638296521 16754481808548324478722391)
    ·
      refine ⟨25131722712822486718083587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16754481808548324478722391 25131722712822486718083587)
      ·
        refine ⟨37697584069233730077125381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25131722712822486718083587 37697584069233730077125381)
        ·
          refine ⟨7068297012981324389461009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37697584069233730077125381 7068297012981324389461009)
          ·
            refine ⟨5301222759735993292095757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7068297012981324389461009 5301222759735993292095757)
            ·
              refine ⟨1987958534900997484535909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5301222759735993292095757 1987958534900997484535909)
              ·
                refine ⟨372742225293937028350483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1987958534900997484535909 372742225293937028350483)
                ·
                  refine ⟨559113337940905542525725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372742225293937028350483 559113337940905542525725)
                  ·
                    refine ⟨209667501727839578447147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 559113337940905542525725 209667501727839578447147)
                    ·
                      rfl

theorem cell22_612489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 1, 3].length) (baseStart_612489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612489 prefixEnd_612489 := by exact prefixLift 612489
  have htrace : WordTrace (prefixWord ++ tailWord_612489) baseStart_612489 baseEnd_612489 := by
    simpa [prefixWord, tailWord_612489, baseEnd_612489] using wordTrace_append hprefix tailTrace_612489
  have hstable : (prefixWord ++ tailWord_612489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612489).length < 2 ^ (prefixWord ++ tailWord_612489).sum := by decide
  have hdescent : baseEnd_612489 < baseStart_612489 := by decide
  rcases family_descends (prefixWord ++ tailWord_612489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612530 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_612530 : Nat := 118140960795 + 612530 * 2 ^ 59
def prefixEnd_612530 : Nat := 4983230072969 + 3 ^ 40 * 612530 * 2
def baseEnd_612530 : Nat := 69893845621909712724007

theorem tailTrace_612530 : CollatzResearch.WordTrace tailWord_612530 prefixEnd_612530 69893845621909712724007 := by
  unfold tailWord_612530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5585201117728974160134761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14893869647277264427026029 5585201117728974160134761)
  ·
    refine ⟨4188900838296730620101071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5585201117728974160134761 4188900838296730620101071)
    ·
      refine ⟨6283351257445095930151607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4188900838296730620101071 6283351257445095930151607)
      ·
        refine ⟨9425026886167643895227411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6283351257445095930151607 9425026886167643895227411)
        ·
          refine ⟨14137540329251465842841117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9425026886167643895227411 14137540329251465842841117)
          ·
            refine ⟨5301577623469299691065419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14137540329251465842841117 5301577623469299691065419)
            ·
              refine ⟨7952366435203949536598129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5301577623469299691065419 7952366435203949536598129)
              ·
                refine ⟨5964274826402962152448597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7952366435203949536598129 5964274826402962152448597)
                ·
                  refine ⟨69893845621909712724007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5964274826402962152448597 69893845621909712724007)
                  ·
                    rfl

theorem cell22_612530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_612530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612530 prefixEnd_612530 := by exact prefixLift 612530
  have htrace : WordTrace (prefixWord ++ tailWord_612530) baseStart_612530 baseEnd_612530 := by
    simpa [prefixWord, tailWord_612530, baseEnd_612530] using wordTrace_append hprefix tailTrace_612530
  have hstable : (prefixWord ++ tailWord_612530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612530).length < 2 ^ (prefixWord ++ tailWord_612530).sum := by decide
  have hdescent : baseEnd_612530 < baseStart_612530 := by decide
  rcases family_descends (prefixWord ++ tailWord_612530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612566 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_612566 : Nat := 118140960795 + 612566 * 2 ^ 59
def prefixEnd_612566 : Nat := 4983230072969 + 3 ^ 40 * 612566 * 2
def baseEnd_612566 : Nat := 209693860401437044271911

theorem tailTrace_612566 : CollatzResearch.WordTrace tailWord_612566 prefixEnd_612566 209693860401437044271911 := by
  unfold tailWord_612566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396382343674092174303097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14894744999190316525899701 1396382343674092174303097)
  ·
    refine ⟨1047286757755569130727323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1396382343674092174303097 1047286757755569130727323)
    ·
      refine ⟨1570930136633353696090985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1047286757755569130727323 1570930136633353696090985)
      ·
        refine ⟨1178197602475015272068239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1570930136633353696090985 1178197602475015272068239)
        ·
          refine ⟨1767296403712522908102359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178197602475015272068239 1767296403712522908102359)
          ·
            refine ⟨2650944605568784362153539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767296403712522908102359 2650944605568784362153539)
            ·
              refine ⟨3976416908353176543230309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650944605568784362153539 3976416908353176543230309)
              ·
                refine ⟨745578170316220601855683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3976416908353176543230309 745578170316220601855683)
                ·
                  refine ⟨1118367255474330902783525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745578170316220601855683 1118367255474330902783525)
                  ·
                    refine ⟨209693860401437044271911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1118367255474330902783525 209693860401437044271911)
                    ·
                      rfl

theorem cell22_612566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_612566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612566 prefixEnd_612566 := by exact prefixLift 612566
  have htrace : WordTrace (prefixWord ++ tailWord_612566) baseStart_612566 baseEnd_612566 := by
    simpa [prefixWord, tailWord_612566, baseEnd_612566] using wordTrace_append hprefix tailTrace_612566
  have hstable : (prefixWord ++ tailWord_612566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612566).length < 2 ^ (prefixWord ++ tailWord_612566).sum := by decide
  have hdescent : baseEnd_612566 < baseStart_612566 := by decide
  rcases family_descends (prefixWord ++ tailWord_612566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612577 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 2, 4]
def baseStart_612577 : Nat := 118140960795 + 612577 * 2 ^ 59
def prefixEnd_612577 : Nat := 4983230072969 + 3 ^ 40 * 612577 * 2
def baseEnd_612577 : Nat := 209697625926236682246877

theorem tailTrace_612577 : CollatzResearch.WordTrace tailWord_612577 prefixEnd_612577 209697625926236682246877 := by
  unfold tailWord_612577
  simp only [CollatzResearch.WordTrace]
  refine ⟨22342518701745623667499985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14895012467830415778333323 22342518701745623667499985)
  ·
    refine ⟨16756889026309217750624989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22342518701745623667499985 16756889026309217750624989)
    ·
      refine ⟨6283833384865956656484371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16756889026309217750624989 6283833384865956656484371)
      ·
        refine ⟨9425750077298934984726557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6283833384865956656484371 9425750077298934984726557)
        ·
          refine ⟨3534656278987100619272459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9425750077298934984726557 3534656278987100619272459)
          ·
            refine ⟨5301984418480650928908689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534656278987100619272459 5301984418480650928908689)
            ·
              refine ⟨3976488313860488196681517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5301984418480650928908689 3976488313860488196681517)
              ·
                refine ⟨1491183117697683073755569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3976488313860488196681517 1491183117697683073755569)
                ·
                  refine ⟨1118387338273262305316677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1491183117697683073755569 1118387338273262305316677)
                  ·
                    refine ⟨209697625926236682246877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1118387338273262305316677 209697625926236682246877)
                    ·
                      rfl

theorem cell22_612577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_612577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612577 prefixEnd_612577 := by exact prefixLift 612577
  have htrace : WordTrace (prefixWord ++ tailWord_612577) baseStart_612577 baseEnd_612577 := by
    simpa [prefixWord, tailWord_612577, baseEnd_612577] using wordTrace_append hprefix tailTrace_612577
  have hstable : (prefixWord ++ tailWord_612577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612577).length < 2 ^ (prefixWord ++ tailWord_612577).sum := by decide
  have hdescent : baseEnd_612577 < baseStart_612577 := by decide
  rcases family_descends (prefixWord ++ tailWord_612577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612581 : List Nat := [1, 3, 1, 4, 2, 3, 1, 3, 4]
def baseStart_612581 : Nat := 118140960795 + 612581 * 2 ^ 59
def prefixEnd_612581 : Nat := 4983230072969 + 3 ^ 40 * 612581 * 2
def baseEnd_612581 : Nat := 69899665069327335048955

theorem tailTrace_612581 : CollatzResearch.WordTrace tailWord_612581 prefixEnd_612581 69899665069327335048955 := by
  unfold tailWord_612581
  simp only [CollatzResearch.WordTrace]
  refine ⟨22342664593731132350645597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14895109729154088233763731 22342664593731132350645597)
  ·
    refine ⟨8378499222649174631492099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22342664593731132350645597 8378499222649174631492099)
    ·
      refine ⟨12567748833973761947238149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8378499222649174631492099 12567748833973761947238149)
      ·
        refine ⟨2356452906370080365107153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12567748833973761947238149 2356452906370080365107153)
        ·
          refine ⟨1767339679777560273830365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2356452906370080365107153 1767339679777560273830365)
          ·
            refine ⟨662752379916585102686387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1767339679777560273830365 662752379916585102686387)
            ·
              refine ⟨994128569874877654029581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662752379916585102686387 994128569874877654029581)
              ·
                refine ⟨372798213703079120261093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 994128569874877654029581 372798213703079120261093)
                ·
                  refine ⟨69899665069327335048955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372798213703079120261093 69899665069327335048955)
                  ·
                    rfl

theorem cell22_612581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_612581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612581 prefixEnd_612581 := by exact prefixLift 612581
  have htrace : WordTrace (prefixWord ++ tailWord_612581) baseStart_612581 baseEnd_612581 := by
    simpa [prefixWord, tailWord_612581, baseEnd_612581] using wordTrace_append hprefix tailTrace_612581
  have hstable : (prefixWord ++ tailWord_612581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612581).length < 2 ^ (prefixWord ++ tailWord_612581).sum := by decide
  have hdescent : baseEnd_612581 < baseStart_612581 := by decide
  rcases family_descends (prefixWord ++ tailWord_612581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612594 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_612594 : Nat := 118140960795 + 612594 * 2 ^ 59
def prefixEnd_612594 : Nat := 4983230072969 + 3 ^ 40 * 612594 * 2
def baseEnd_612594 : Nat := 209703445373654304571825

theorem tailTrace_612594 : CollatzResearch.WordTrace tailWord_612594 prefixEnd_612594 209703445373654304571825 := by
  unfold tailWord_612594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5585784685671008892717209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14895425828456023713912557 5585784685671008892717209)
  ·
    refine ⟨4189338514253256669537907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5585784685671008892717209 4189338514253256669537907)
    ·
      refine ⟨6284007771379885004306861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4189338514253256669537907 6284007771379885004306861)
      ·
        refine ⟨2356502914267456876615073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6284007771379885004306861 2356502914267456876615073)
        ·
          refine ⟨1767377185700592657461305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2356502914267456876615073 1767377185700592657461305)
          ·
            refine ⟨1325532889275444493095979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1767377185700592657461305 1325532889275444493095979)
            ·
              refine ⟨1988299333913166739643969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325532889275444493095979 1988299333913166739643969)
              ·
                refine ⟨1491224500434875054732977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1988299333913166739643969 1491224500434875054732977)
                ·
                  refine ⟨1118418375326156291049733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1491224500434875054732977 1118418375326156291049733)
                  ·
                    refine ⟨209703445373654304571825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1118418375326156291049733 209703445373654304571825)
                    ·
                      rfl

theorem cell22_612594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_612594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612594 prefixEnd_612594 := by exact prefixLift 612594
  have htrace : WordTrace (prefixWord ++ tailWord_612594) baseStart_612594 baseEnd_612594 := by
    simpa [prefixWord, tailWord_612594, baseEnd_612594] using wordTrace_append hprefix tailTrace_612594
  have hstable : (prefixWord ++ tailWord_612594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612594).length < 2 ^ (prefixWord ++ tailWord_612594).sum := by decide
  have hdescent : baseEnd_612594 < baseStart_612594 := by decide
  rcases family_descends (prefixWord ++ tailWord_612594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612658 : List Nat := [3, 2, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_612658 : Nat := 118140960795 + 612658 * 2 ^ 59
def prefixEnd_612658 : Nat := 4983230072969 + 3 ^ 40 * 612658 * 2
def baseEnd_612658 : Nat := 209725353881579470971629

theorem tailTrace_612658 : CollatzResearch.WordTrace tailWord_612658 prefixEnd_612658 209725353881579470971629 := by
  unfold tailWord_612658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586368253613043625299657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14896982009634783000799085 5586368253613043625299657)
  ·
    refine ⟨4189776190209782718974743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5586368253613043625299657 4189776190209782718974743)
    ·
      refine ⟨6284664285314674078462115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4189776190209782718974743 6284664285314674078462115)
      ·
        refine ⟨9426996427972011117693173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6284664285314674078462115 9426996427972011117693173)
        ·
          refine ⟨883780915122376042283735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9426996427972011117693173 883780915122376042283735)
          ·
            refine ⟨1325671372683564063425603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883780915122376042283735 1325671372683564063425603)
            ·
              refine ⟨1988507059025346095138405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325671372683564063425603 1988507059025346095138405)
              ·
                refine ⟨372845073567252392838451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1988507059025346095138405 372845073567252392838451)
                ·
                  refine ⟨559267610350878589257677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372845073567252392838451 559267610350878589257677)
                  ·
                    refine ⟨209725353881579470971629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 559267610350878589257677 209725353881579470971629)
                    ·
                      rfl

theorem cell22_612658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_612658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612658 prefixEnd_612658 := by exact prefixLift 612658
  have htrace : WordTrace (prefixWord ++ tailWord_612658) baseStart_612658 baseEnd_612658 := by
    simpa [prefixWord, tailWord_612658, baseEnd_612658] using wordTrace_append hprefix tailTrace_612658
  have hstable : (prefixWord ++ tailWord_612658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612658).length < 2 ^ (prefixWord ++ tailWord_612658).sum := by decide
  have hdescent : baseEnd_612658 < baseStart_612658 := by decide
  rcases family_descends (prefixWord ++ tailWord_612658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612684 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_612684 : Nat := 118140960795 + 612684 * 2 ^ 59
def prefixEnd_612684 : Nat := 4983230072969 + 3 ^ 40 * 612684 * 2
def baseEnd_612684 : Nat := 209734254212924069821549

theorem tailTrace_612684 : CollatzResearch.WordTrace tailWord_612684 prefixEnd_612684 209734254212924069821549 := by
  unfold tailWord_612684
  simp only [CollatzResearch.WordTrace]
  refine ⟨11173210656178990470822553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14897614208238653961096737 11173210656178990470822553)
  ·
    refine ⟨8379907992134242853116915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11173210656178990470822553 8379907992134242853116915)
    ·
      refine ⟨12569861988201364279675373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8379907992134242853116915 12569861988201364279675373)
      ·
        refine ⟨4713698245575511604878265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12569861988201364279675373 4713698245575511604878265)
        ·
          refine ⟨3535273684181633703658699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4713698245575511604878265 3535273684181633703658699)
          ·
            refine ⟨5302910526272450555488049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535273684181633703658699 5302910526272450555488049)
            ·
              refine ⟨3977182894704337916616037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5302910526272450555488049 3977182894704337916616037)
              ·
                refine ⟨745721792757063359365507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3977182894704337916616037 745721792757063359365507)
                ·
                  refine ⟨1118582689135595039048261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 745721792757063359365507 1118582689135595039048261)
                  ·
                    refine ⟨209734254212924069821549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1118582689135595039048261 209734254212924069821549)
                    ·
                      rfl

theorem cell22_612684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_612684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612684 prefixEnd_612684 := by exact prefixLift 612684
  have htrace : WordTrace (prefixWord ++ tailWord_612684) baseStart_612684 baseEnd_612684 := by
    simpa [prefixWord, tailWord_612684, baseEnd_612684] using wordTrace_append hprefix tailTrace_612684
  have hstable : (prefixWord ++ tailWord_612684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612684).length < 2 ^ (prefixWord ++ tailWord_612684).sum := by decide
  have hdescent : baseEnd_612684 < baseStart_612684 := by decide
  rcases family_descends (prefixWord ++ tailWord_612684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612757 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_612757 : Nat := 118140960795 + 612757 * 2 ^ 59
def prefixEnd_612757 : Nat := 4983230072969 + 3 ^ 40 * 612757 * 2
def baseEnd_612757 : Nat := 209759243604776212746325

theorem tailTrace_612757 : CollatzResearch.WordTrace tailWord_612757 prefixEnd_612757 209759243604776212746325 := by
  unfold tailWord_612757
  simp only [CollatzResearch.WordTrace]
  refine ⟨22349083841093514409052525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14899389227395676272701683 22349083841093514409052525)
  ·
    refine ⟨8380906440410067903394697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22349083841093514409052525 8380906440410067903394697)
    ·
      refine ⟨6285679830307550927546023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8380906440410067903394697 6285679830307550927546023)
      ·
        refine ⟨9428519745461326391319035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6285679830307550927546023 9428519745461326391319035)
        ·
          refine ⟨14142779618191989586978553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9428519745461326391319035 14142779618191989586978553)
          ·
            refine ⟨10607084713643992190233915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14142779618191989586978553 10607084713643992190233915)
            ·
              refine ⟨15910627070465988285350873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10607084713643992190233915 15910627070465988285350873)
              ·
                refine ⟨11932970302849491214013155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15910627070465988285350873 11932970302849491214013155)
                ·
                  refine ⟨17899455454274236821019733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11932970302849491214013155 17899455454274236821019733)
                  ·
                    refine ⟨209759243604776212746325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17899455454274236821019733 209759243604776212746325)
                    ·
                      rfl

theorem cell22_612757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_612757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612757 prefixEnd_612757 := by exact prefixLift 612757
  have htrace : WordTrace (prefixWord ++ tailWord_612757) baseStart_612757 baseEnd_612757 := by
    simpa [prefixWord, tailWord_612757, baseEnd_612757] using wordTrace_append hprefix tailTrace_612757
  have hstable : (prefixWord ++ tailWord_612757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612757).length < 2 ^ (prefixWord ++ tailWord_612757).sum := by decide
  have hdescent : baseEnd_612757 < baseStart_612757 := by decide
  rcases family_descends (prefixWord ++ tailWord_612757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612759 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 5, 3]
def baseStart_612759 : Nat := 118140960795 + 612759 * 2 ^ 59
def prefixEnd_612759 : Nat := 4983230072969 + 3 ^ 40 * 612759 * 2
def baseEnd_612759 : Nat := 209759928245648874196319

theorem tailTrace_612759 : CollatzResearch.WordTrace tailWord_612759 prefixEnd_612759 209759928245648874196319 := by
  unfold tailWord_612759
  simp only [CollatzResearch.WordTrace]
  refine ⟨22349156787086268750625331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14899437858057512500416887 22349156787086268750625331)
  ·
    refine ⟨33523735180629403125937997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22349156787086268750625331 33523735180629403125937997)
    ·
      refine ⟨12571400692736026172226749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33523735180629403125937997 12571400692736026172226749)
      ·
        refine ⟨4714275259776009814585031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12571400692736026172226749 4714275259776009814585031)
        ·
          refine ⟨7071412889664014721877547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4714275259776009814585031 7071412889664014721877547)
          ·
            refine ⟨10607119334496022082816321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7071412889664014721877547 10607119334496022082816321)
            ·
              refine ⟨7955339500872016562112241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10607119334496022082816321 7955339500872016562112241)
              ·
                refine ⟨5966504625654012421584181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7955339500872016562112241 5966504625654012421584181)
                ·
                  refine ⟨559359808655063664523517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5966504625654012421584181 559359808655063664523517)
                  ·
                    refine ⟨209759928245648874196319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 559359808655063664523517 209759928245648874196319)
                    ·
                      rfl

theorem cell22_612759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_612759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612759 prefixEnd_612759 := by exact prefixLift 612759
  have htrace : WordTrace (prefixWord ++ tailWord_612759) baseStart_612759 baseEnd_612759 := by
    simpa [prefixWord, tailWord_612759, baseEnd_612759] using wordTrace_append hprefix tailTrace_612759
  have hstable : (prefixWord ++ tailWord_612759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612759).length < 2 ^ (prefixWord ++ tailWord_612759).sum := by decide
  have hdescent : baseEnd_612759 < baseStart_612759 := by decide
  rcases family_descends (prefixWord ++ tailWord_612759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612868 : List Nat := [2, 3, 2, 3, 1, 1, 1, 5, 4]
def baseStart_612868 : Nat := 118140960795 + 612868 * 2 ^ 59
def prefixEnd_612868 : Nat := 4983230072969 + 3 ^ 40 * 612868 * 2
def baseEnd_612868 : Nat := 69932413724402974406995

theorem tailTrace_612868 : CollatzResearch.WordTrace tailWord_612868 prefixEnd_612868 69932413724402974406995 := by
  unfold tailWord_612868
  simp only [CollatzResearch.WordTrace]
  refine ⟨11176566171845690183171629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14902088229127586910895505 11176566171845690183171629)
  ·
    refine ⟨4191212314442133818689361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11176566171845690183171629 4191212314442133818689361)
    ·
      refine ⟨3143409235831600364017021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4191212314442133818689361 3143409235831600364017021)
      ·
        refine ⟨1178778463436850136506383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3143409235831600364017021 1178778463436850136506383)
        ·
          refine ⟨1768167695155275204759575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178778463436850136506383 1768167695155275204759575)
          ·
            refine ⟨2652251542732912807139363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768167695155275204759575 2652251542732912807139363)
            ·
              refine ⟨3978377314099369210709045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652251542732912807139363 3978377314099369210709045)
              ·
                refine ⟨372972873196815863503973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3978377314099369210709045 372972873196815863503973)
                ·
                  refine ⟨69932413724402974406995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372972873196815863503973 69932413724402974406995)
                  ·
                    rfl

theorem cell22_612868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_612868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612868 prefixEnd_612868 := by exact prefixLift 612868
  have htrace : WordTrace (prefixWord ++ tailWord_612868) baseStart_612868 baseEnd_612868 := by
    simpa [prefixWord, tailWord_612868, baseEnd_612868] using wordTrace_append hprefix tailTrace_612868
  have hstable : (prefixWord ++ tailWord_612868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612868).length < 2 ^ (prefixWord ++ tailWord_612868).sum := by decide
  have hdescent : baseEnd_612868 < baseStart_612868 := by decide
  rcases family_descends (prefixWord ++ tailWord_612868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612900 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_612900 : Nat := 118140960795 + 612900 * 2 ^ 59
def prefixEnd_612900 : Nat := 4983230072969 + 3 ^ 40 * 612900 * 2
def baseEnd_612900 : Nat := 209808195427171506420887

theorem tailTrace_612900 : CollatzResearch.WordTrace tailWord_612900 prefixEnd_612900 209808195427171506420887 := by
  unfold tailWord_612900
  simp only [CollatzResearch.WordTrace]
  refine ⟨11177149739787724915754077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14902866319716966554338769 11177149739787724915754077)
  ·
    refine ⟨4191431152420396843407779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11177149739787724915754077 4191431152420396843407779)
    ·
      refine ⟨6287146728630595265111669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4191431152420396843407779 6287146728630595265111669)
      ·
        refine ⟨589420005809118306104219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6287146728630595265111669 589420005809118306104219)
        ·
          refine ⟨884130008713677459156329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589420005809118306104219 884130008713677459156329)
          ·
            refine ⟨663097506535258094367247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 884130008713677459156329 663097506535258094367247)
            ·
              refine ⟨994646259802887141550871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663097506535258094367247 994646259802887141550871)
              ·
                refine ⟨1491969389704330712326307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994646259802887141550871 1491969389704330712326307)
                ·
                  refine ⟨2237954084556496068489461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491969389704330712326307 2237954084556496068489461)
                  ·
                    refine ⟨209808195427171506420887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2237954084556496068489461 209808195427171506420887)
                    ·
                      rfl

theorem cell22_612900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_612900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612900 prefixEnd_612900 := by exact prefixLift 612900
  have htrace : WordTrace (prefixWord ++ tailWord_612900) baseStart_612900 baseEnd_612900 := by
    simpa [prefixWord, tailWord_612900, baseEnd_612900] using wordTrace_append hprefix tailTrace_612900
  have hstable : (prefixWord ++ tailWord_612900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612900).length < 2 ^ (prefixWord ++ tailWord_612900).sum := by decide
  have hdescent : baseEnd_612900 < baseStart_612900 := by decide
  rcases family_descends (prefixWord ++ tailWord_612900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612932 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_612932 : Nat := 118140960795 + 612932 * 2 ^ 59
def prefixEnd_612932 : Nat := 4983230072969 + 3 ^ 40 * 612932 * 2
def baseEnd_612932 : Nat := 209819149681134089620789

theorem tailTrace_612932 : CollatzResearch.WordTrace tailWord_612932 prefixEnd_612932 209819149681134089620789 := by
  unfold tailWord_612932
  simp only [CollatzResearch.WordTrace]
  refine ⟨11177733307729759648336525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14903644410306346197782033 11177733307729759648336525)
  ·
    refine ⟨4191649990398659868126197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11177733307729759648336525 4191649990398659868126197)
    ·
      refine ⟨392967186599874362636831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4191649990398659868126197 392967186599874362636831)
      ·
        refine ⟨589450779899811543955247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392967186599874362636831 589450779899811543955247)
        ·
          refine ⟨884176169849717315932871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589450779899811543955247 884176169849717315932871)
          ·
            refine ⟨1326264254774575973899307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884176169849717315932871 1326264254774575973899307)
            ·
              refine ⟨1989396382161863960848961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326264254774575973899307 1989396382161863960848961)
              ·
                refine ⟨1492047286621397970636721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989396382161863960848961 1492047286621397970636721)
                ·
                  refine ⟨1119035464966048477977541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1492047286621397970636721 1119035464966048477977541)
                  ·
                    refine ⟨209819149681134089620789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1119035464966048477977541 209819149681134089620789)
                    ·
                      rfl

theorem cell22_612932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_612932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612932 prefixEnd_612932 := by exact prefixLift 612932
  have htrace : WordTrace (prefixWord ++ tailWord_612932) baseStart_612932 baseEnd_612932 := by
    simpa [prefixWord, tailWord_612932, baseEnd_612932] using wordTrace_append hprefix tailTrace_612932
  have hstable : (prefixWord ++ tailWord_612932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612932).length < 2 ^ (prefixWord ++ tailWord_612932).sum := by decide
  have hdescent : baseEnd_612932 < baseStart_612932 := by decide
  rcases family_descends (prefixWord ++ tailWord_612932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612939 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 4, 5]
def baseStart_612939 : Nat := 118140960795 + 612939 * 2 ^ 59
def prefixEnd_612939 : Nat := 4983230072969 + 3 ^ 40 * 612939 * 2
def baseEnd_612939 : Nat := 209821545924188404695767

theorem tailTrace_612939 : CollatzResearch.WordTrace tailWord_612939 prefixEnd_612939 209821545924188404695767 := by
  unfold tailWord_612939
  simp only [CollatzResearch.WordTrace]
  refine ⟨22355721926434159492177871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14903814617622772994785247 22355721926434159492177871)
  ·
    refine ⟨33533582889651239238266807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22355721926434159492177871 33533582889651239238266807)
    ·
      refine ⟨50300374334476858857400211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33533582889651239238266807 50300374334476858857400211)
      ·
        refine ⟨75450561501715288286100317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50300374334476858857400211 75450561501715288286100317)
        ·
          refine ⟨28293960563143233107287619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75450561501715288286100317 28293960563143233107287619)
          ·
            refine ⟨42440940844714849660931429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28293960563143233107287619 42440940844714849660931429)
            ·
              refine ⟨7957676408384034311424643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42440940844714849660931429 7957676408384034311424643)
              ·
                refine ⟨11936514612576051467136965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7957676408384034311424643 11936514612576051467136965)
                ·
                  refine ⟨2238096489858009650088181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11936514612576051467136965 2238096489858009650088181)
                  ·
                    refine ⟨209821545924188404695767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2238096489858009650088181 209821545924188404695767)
                    ·
                      rfl

theorem cell22_612939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_612939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612939 prefixEnd_612939 := by exact prefixLift 612939
  have htrace : WordTrace (prefixWord ++ tailWord_612939) baseStart_612939 baseEnd_612939 := by
    simpa [prefixWord, tailWord_612939, baseEnd_612939] using wordTrace_append hprefix tailTrace_612939
  have hstable : (prefixWord ++ tailWord_612939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612939).length < 2 ^ (prefixWord ++ tailWord_612939).sum := by decide
  have hdescent : baseEnd_612939 < baseStart_612939 := by decide
  rcases family_descends (prefixWord ++ tailWord_612939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612954 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_612954 : Nat := 118140960795 + 612954 * 2 ^ 59
def prefixEnd_612954 : Nat := 4983230072969 + 3 ^ 40 * 612954 * 2
def baseEnd_612954 : Nat := 209826680730733365570721

theorem tailTrace_612954 : CollatzResearch.WordTrace tailWord_612954 prefixEnd_612954 209826680730733365570721 := by
  unfold tailWord_612954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5589067255344954263493479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14904179347586544702649277 5589067255344954263493479)
  ·
    refine ⟨8383600883017431395240219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5589067255344954263493479 8383600883017431395240219)
    ·
      refine ⟨12575401324526147092860329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8383600883017431395240219 12575401324526147092860329)
      ·
        refine ⟨9431550993394610319645247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12575401324526147092860329 9431550993394610319645247)
        ·
          refine ⟨14147326490091915479467871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9431550993394610319645247 14147326490091915479467871)
          ·
            refine ⟨21220989735137873219201807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14147326490091915479467871 21220989735137873219201807)
            ·
              refine ⟨31831484602706809828802711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21220989735137873219201807 31831484602706809828802711)
              ·
                refine ⟨47747226904060214743204067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31831484602706809828802711 47747226904060214743204067)
                ·
                  refine ⟨71620840356090322114806101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47747226904060214743204067 71620840356090322114806101)
                  ·
                    refine ⟨209826680730733365570721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 71620840356090322114806101 209826680730733365570721)
                    ·
                      rfl

theorem cell22_612954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_612954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612954 prefixEnd_612954 := by exact prefixLift 612954
  have htrace : WordTrace (prefixWord ++ tailWord_612954) baseStart_612954 baseEnd_612954 := by
    simpa [prefixWord, tailWord_612954, baseEnd_612954] using wordTrace_append hprefix tailTrace_612954
  have hstable : (prefixWord ++ tailWord_612954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612954).length < 2 ^ (prefixWord ++ tailWord_612954).sum := by decide
  have hdescent : baseEnd_612954 < baseStart_612954 := by decide
  rcases family_descends (prefixWord ++ tailWord_612954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612969 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 8]
def baseStart_612969 : Nat := 118140960795 + 612969 * 2 ^ 59
def prefixEnd_612969 : Nat := 4983230072969 + 3 ^ 40 * 612969 * 2
def baseEnd_612969 : Nat := 69943938512426108815225

theorem tailTrace_612969 : CollatzResearch.WordTrace tailWord_612969 prefixEnd_612969 69943938512426108815225 := by
  unfold tailWord_612969
  simp only [CollatzResearch.WordTrace]
  refine ⟨22356816116325474615769961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14904544077550316410513307 22356816116325474615769961)
  ·
    refine ⟨16767612087244105961827471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22356816116325474615769961 16767612087244105961827471)
    ·
      refine ⟨25151418130866158942741207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16767612087244105961827471 25151418130866158942741207)
      ·
        refine ⟨37727127196299238414111811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25151418130866158942741207 37727127196299238414111811)
        ·
          refine ⟨56590690794448857621167717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37727127196299238414111811 56590690794448857621167717)
          ·
            refine ⟨10610754523959160803968947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56590690794448857621167717 10610754523959160803968947)
            ·
              refine ⟨15916131785938741205953421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10610754523959160803968947 15916131785938741205953421)
              ·
                refine ⟨5968549419727027952232533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15916131785938741205953421 5968549419727027952232533)
                ·
                  refine ⟨69943938512426108815225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5968549419727027952232533 69943938512426108815225)
                  ·
                    rfl

theorem cell22_612969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_612969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612969 prefixEnd_612969 := by exact prefixLift 612969
  have htrace : WordTrace (prefixWord ++ tailWord_612969) baseStart_612969 baseEnd_612969 := by
    simpa [prefixWord, tailWord_612969, baseEnd_612969] using wordTrace_append hprefix tailTrace_612969
  have hstable : (prefixWord ++ tailWord_612969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612969).length < 2 ^ (prefixWord ++ tailWord_612969).sum := by decide
  have hdescent : baseEnd_612969 < baseStart_612969 := by decide
  rcases family_descends (prefixWord ++ tailWord_612969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_612971 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 1, 4]
def baseStart_612971 : Nat := 118140960795 + 612971 * 2 ^ 59
def prefixEnd_612971 : Nat := 4983230072969 + 3 ^ 40 * 612971 * 2
def baseEnd_612971 : Nat := 209832500178150987895669

theorem tailTrace_612971 : CollatzResearch.WordTrace tailWord_612971 prefixEnd_612971 209832500178150987895669 := by
  unfold tailWord_612971
  simp only [CollatzResearch.WordTrace]
  refine ⟨22356889062318228957342767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14904592708212152638228511 22356889062318228957342767)
  ·
    refine ⟨33535333593477343436014151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22356889062318228957342767 33535333593477343436014151)
    ·
      refine ⟨50303000390216015154021227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33535333593477343436014151 50303000390216015154021227)
      ·
        refine ⟨75454500585324022731031841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50303000390216015154021227 75454500585324022731031841)
        ·
          refine ⟨56590875438993017048273881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75454500585324022731031841 56590875438993017048273881)
          ·
            refine ⟨42443156579244762786205411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56590875438993017048273881 42443156579244762786205411)
            ·
              refine ⟨63664734868867144179308117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42443156579244762786205411 63664734868867144179308117)
              ·
                refine ⟨746071111744536845851267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 63664734868867144179308117 746071111744536845851267)
                ·
                  refine ⟨1119106667616805268776901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 746071111744536845851267 1119106667616805268776901)
                  ·
                    refine ⟨209832500178150987895669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1119106667616805268776901 209832500178150987895669)
                    ·
                      rfl

theorem cell22_612971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 4].length) (baseStart_612971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_612971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_612971 prefixEnd_612971 := by exact prefixLift 612971
  have htrace : WordTrace (prefixWord ++ tailWord_612971) baseStart_612971 baseEnd_612971 := by
    simpa [prefixWord, tailWord_612971, baseEnd_612971] using wordTrace_append hprefix tailTrace_612971
  have hstable : (prefixWord ++ tailWord_612971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_612971).length < 2 ^ (prefixWord ++ tailWord_612971).sum := by decide
  have hdescent : baseEnd_612971 < baseStart_612971 := by decide
  rcases family_descends (prefixWord ++ tailWord_612971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613016 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_613016 : Nat := 118140960795 + 613016 * 2 ^ 59
def prefixEnd_613016 : Nat := 4983230072969 + 3 ^ 40 * 613016 * 2
def baseEnd_613016 : Nat := 209847904597785870520531

theorem tailTrace_613016 : CollatzResearch.WordTrace tailWord_613016 prefixEnd_613016 209847904597785870520531 := by
  unfold tailWord_613016
  simp only [CollatzResearch.WordTrace]
  refine ⟨11179265173577600821365451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14905686898103467761820601 11179265173577600821365451)
  ·
    refine ⟨16768897760366401232048177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11179265173577600821365451 16768897760366401232048177)
    ·
      refine ⟨12576673320274800924036133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16768897760366401232048177 12576673320274800924036133)
      ·
        refine ⟨2358126247551525173256775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12576673320274800924036133 2358126247551525173256775)
        ·
          refine ⟨3537189371327287759885163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358126247551525173256775 3537189371327287759885163)
          ·
            refine ⟨5305784056990931639827745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3537189371327287759885163 5305784056990931639827745)
            ·
              refine ⟨3979338042743198729870809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5305784056990931639827745 3979338042743198729870809)
              ·
                refine ⟨2984503532057399047403107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3979338042743198729870809 2984503532057399047403107)
                ·
                  refine ⟨4476755298086098571104661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984503532057399047403107 4476755298086098571104661)
                  ·
                    refine ⟨209847904597785870520531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4476755298086098571104661 209847904597785870520531)
                    ·
                      rfl

theorem cell22_613016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_613016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613016 prefixEnd_613016 := by exact prefixLift 613016
  have htrace : WordTrace (prefixWord ++ tailWord_613016) baseStart_613016 baseEnd_613016 := by
    simpa [prefixWord, tailWord_613016, baseEnd_613016] using wordTrace_append hprefix tailTrace_613016
  have hstable : (prefixWord ++ tailWord_613016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613016).length < 2 ^ (prefixWord ++ tailWord_613016).sum := by decide
  have hdescent : baseEnd_613016 < baseStart_613016 := by decide
  rcases family_descends (prefixWord ++ tailWord_613016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613069 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_613069 : Nat := 118140960795 + 613069 * 2 ^ 59
def prefixEnd_613069 : Nat := 4983230072969 + 3 ^ 40 * 613069 * 2
def baseEnd_613069 : Nat := 209866047580911398945369

theorem tailTrace_613069 : CollatzResearch.WordTrace tailWord_613069 prefixEnd_613069 209866047580911398945369 := by
  unfold tailWord_613069
  simp only [CollatzResearch.WordTrace]
  refine ⟨22360463415963191694410261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14906975610642127796273507 22360463415963191694410261)
  ·
    refine ⟨1048146722623274610675481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22360463415963191694410261 1048146722623274610675481)
    ·
      refine ⟨786110041967455958006611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1048146722623274610675481 786110041967455958006611)
      ·
        refine ⟨1179165062951183937009917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786110041967455958006611 1179165062951183937009917)
        ·
          refine ⟨442186898606693976378719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1179165062951183937009917 442186898606693976378719)
          ·
            refine ⟨663280347910040964568079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442186898606693976378719 663280347910040964568079)
            ·
              refine ⟨994920521865061446852119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663280347910040964568079 994920521865061446852119)
              ·
                refine ⟨1492380782797592170278179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994920521865061446852119 1492380782797592170278179)
                ·
                  refine ⟨2238571174196388255417269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492380782797592170278179 2238571174196388255417269)
                  ·
                    refine ⟨209866047580911398945369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2238571174196388255417269 209866047580911398945369)
                    ·
                      rfl

theorem cell22_613069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_613069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613069 prefixEnd_613069 := by exact prefixLift 613069
  have htrace : WordTrace (prefixWord ++ tailWord_613069) baseStart_613069 baseEnd_613069 := by
    simpa [prefixWord, tailWord_613069, baseEnd_613069] using wordTrace_append hprefix tailTrace_613069
  have hstable : (prefixWord ++ tailWord_613069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613069).length < 2 ^ (prefixWord ++ tailWord_613069).sum := by decide
  have hdescent : baseEnd_613069 < baseStart_613069 := by decide
  rcases family_descends (prefixWord ++ tailWord_613069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613127 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 5]
def baseStart_613127 : Nat := 118140960795 + 613127 * 2 ^ 59
def prefixEnd_613127 : Nat := 4983230072969 + 3 ^ 40 * 613127 * 2
def baseEnd_613127 : Nat := 69961967388739526998397

theorem tailTrace_613127 : CollatzResearch.WordTrace tailWord_613127 prefixEnd_613127 69961967388739526998397 := by
  unfold tailWord_613127
  simp only [CollatzResearch.WordTrace]
  refine ⟨22362578849753067600021635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14908385899835378400014423 22362578849753067600021635)
  ·
    refine ⟨33543868274629601400032453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22362578849753067600021635 33543868274629601400032453)
    ·
      refine ⟨6289475301493050262506085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33543868274629601400032453 6289475301493050262506085)
      ·
        refine ⟨1179276619029946924219891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6289475301493050262506085 1179276619029946924219891)
        ·
          refine ⟨1768914928544920386329837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179276619029946924219891 1768914928544920386329837)
          ·
            refine ⟨663343098204345144873689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1768914928544920386329837 663343098204345144873689)
            ·
              refine ⟨497507323653258858655267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663343098204345144873689 497507323653258858655267)
              ·
                refine ⟨746260985479888287982901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497507323653258858655267 746260985479888287982901)
                ·
                  refine ⟨69961967388739526998397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 746260985479888287982901 69961967388739526998397)
                  ·
                    rfl

theorem cell22_613127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 5].length) (baseStart_613127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613127 prefixEnd_613127 := by exact prefixLift 613127
  have htrace : WordTrace (prefixWord ++ tailWord_613127) baseStart_613127 baseEnd_613127 := by
    simpa [prefixWord, tailWord_613127, baseEnd_613127] using wordTrace_append hprefix tailTrace_613127
  have hstable : (prefixWord ++ tailWord_613127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613127).length < 2 ^ (prefixWord ++ tailWord_613127).sum := by decide
  have hdescent : baseEnd_613127 < baseStart_613127 := by decide
  rcases family_descends (prefixWord ++ tailWord_613127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613153 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 1, 5]
def baseStart_613153 : Nat := 118140960795 + 613153 * 2 ^ 59
def prefixEnd_613153 : Nat := 4983230072969 + 3 ^ 40 * 613153 * 2
def baseEnd_613153 : Nat := 209894802497563179845111

theorem tailTrace_613153 : CollatzResearch.WordTrace tailWord_613153 prefixEnd_613153 209894802497563179845111 := by
  unfold tailWord_613153
  simp only [CollatzResearch.WordTrace]
  refine ⟨22363527147658874040468113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14909018098439249360312075 22363527147658874040468113)
  ·
    refine ⟨16772645360744155530351085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22363527147658874040468113 16772645360744155530351085)
    ·
      refine ⟨6289742010279058323881657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16772645360744155530351085 6289742010279058323881657)
      ·
        refine ⟨4717306507709293742911243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6289742010279058323881657 4717306507709293742911243)
        ·
          refine ⟨7075959761563940614366865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4717306507709293742911243 7075959761563940614366865)
          ·
            refine ⟨5306969821172955460775149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7075959761563940614366865 5306969821172955460775149)
            ·
              refine ⟨1990113682939858297790681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5306969821172955460775149 1990113682939858297790681)
              ·
                refine ⟨1492585262204893723343011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1990113682939858297790681 1492585262204893723343011)
                ·
                  refine ⟨2238877893307340585014517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492585262204893723343011 2238877893307340585014517)
                  ·
                    refine ⟨209894802497563179845111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2238877893307340585014517 209894802497563179845111)
                    ·
                      rfl

theorem cell22_613153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_613153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613153 prefixEnd_613153 := by exact prefixLift 613153
  have htrace : WordTrace (prefixWord ++ tailWord_613153) baseStart_613153 baseEnd_613153 := by
    simpa [prefixWord, tailWord_613153, baseEnd_613153] using wordTrace_append hprefix tailTrace_613153
  have hstable : (prefixWord ++ tailWord_613153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613153).length < 2 ^ (prefixWord ++ tailWord_613153).sum := by decide
  have hdescent : baseEnd_613153 < baseStart_613153 := by decide
  rcases family_descends (prefixWord ++ tailWord_613153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613165 : List Nat := [1, 5, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_613165 : Nat := 118140960795 + 613165 * 2 ^ 59
def prefixEnd_613165 : Nat := 4983230072969 + 3 ^ 40 * 613165 * 2
def baseEnd_613165 : Nat := 209898910342799148545075

theorem tailTrace_613165 : CollatzResearch.WordTrace tailWord_613165 prefixEnd_613165 209898910342799148545075 := by
  unfold tailWord_613165
  simp only [CollatzResearch.WordTrace]
  refine ⟨22363964823615400089904949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14909309882410266726603299 22363964823615400089904949)
  ·
    refine ⟨2096621702213943758428589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22363964823615400089904949 2096621702213943758428589)
    ·
      refine ⟨786233138330228909410721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2096621702213943758428589 786233138330228909410721)
      ·
        refine ⟨589674853747671682058041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 786233138330228909410721 589674853747671682058041)
        ·
          refine ⟨442256140310753761543531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589674853747671682058041 442256140310753761543531)
          ·
            refine ⟨663384210466130642315297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442256140310753761543531 663384210466130642315297)
            ·
              refine ⟨497538157849597981736473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663384210466130642315297 497538157849597981736473)
              ·
                refine ⟨373153618387198486302355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497538157849597981736473 373153618387198486302355)
                ·
                  refine ⟨559730427580797729453533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373153618387198486302355 559730427580797729453533)
                  ·
                    refine ⟨209898910342799148545075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 559730427580797729453533 209898910342799148545075)
                    ·
                      rfl

theorem cell22_613165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_613165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613165 prefixEnd_613165 := by exact prefixLift 613165
  have htrace : WordTrace (prefixWord ++ tailWord_613165) baseStart_613165 baseEnd_613165 := by
    simpa [prefixWord, tailWord_613165, baseEnd_613165] using wordTrace_append hprefix tailTrace_613165
  have hstable : (prefixWord ++ tailWord_613165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613165).length < 2 ^ (prefixWord ++ tailWord_613165).sum := by decide
  have hdescent : baseEnd_613165 < baseStart_613165 := by decide
  rcases family_descends (prefixWord ++ tailWord_613165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613183 : List Nat := [1, 1, 2, 2, 5, 1, 3, 7]
def baseStart_613183 : Nat := 118140960795 + 613183 * 2 ^ 59
def prefixEnd_613183 : Nat := 4983230072969 + 3 ^ 40 * 613183 * 2
def baseEnd_613183 : Nat := 23322785790072566843891

theorem tailTrace_613183 : CollatzResearch.WordTrace tailWord_613183 prefixEnd_613183 23322785790072566843891 := by
  unfold tailWord_613183
  simp only [CollatzResearch.WordTrace]
  refine ⟨22364621337550189164060203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14909747558366792776040135 22364621337550189164060203)
  ·
    refine ⟨33546932006325283746090305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22364621337550189164060203 33546932006325283746090305)
    ·
      refine ⟨25160199004743962809567729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33546932006325283746090305 25160199004743962809567729)
      ·
        refine ⟨18870149253557972107175797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25160199004743962809567729 18870149253557972107175797)
        ·
          refine ⟨1769076492521059885047731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18870149253557972107175797 1769076492521059885047731)
          ·
            refine ⟨2653614738781589827571597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769076492521059885047731 2653614738781589827571597)
            ·
              refine ⟨995105527043096185339349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2653614738781589827571597 995105527043096185339349)
              ·
                refine ⟨23322785790072566843891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 995105527043096185339349 23322785790072566843891)
                ·
                  rfl

theorem cell22_613183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 7].length) (baseStart_613183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613183 prefixEnd_613183 := by exact prefixLift 613183
  have htrace : WordTrace (prefixWord ++ tailWord_613183) baseStart_613183 baseEnd_613183 := by
    simpa [prefixWord, tailWord_613183, baseEnd_613183] using wordTrace_append hprefix tailTrace_613183
  have hstable : (prefixWord ++ tailWord_613183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613183).length < 2 ^ (prefixWord ++ tailWord_613183).sum := by decide
  have hdescent : baseEnd_613183 < baseStart_613183 := by decide
  rcases family_descends (prefixWord ++ tailWord_613183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613228 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 7]
def baseStart_613228 : Nat := 118140960795 + 613228 * 2 ^ 59
def prefixEnd_613228 : Nat := 4983230072969 + 3 ^ 40 * 613228 * 2
def baseEnd_613228 : Nat := 69973492176762661406627

theorem tailTrace_613228 : CollatzResearch.WordTrace tailWord_613228 prefixEnd_613228 69973492176762661406627 := by
  unfold tailWord_613228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11183131311193580924724169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14910841748258107899632225 11183131311193580924724169)
  ·
    refine ⟨8387348483395185693543127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11183131311193580924724169 8387348483395185693543127)
    ·
      refine ⟨12581022725092778540314691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8387348483395185693543127 12581022725092778540314691)
      ·
        refine ⟨18871534087639167810472037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12581022725092778540314691 18871534087639167810472037)
        ·
          refine ⟨3538412641432343964463507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18871534087639167810472037 3538412641432343964463507)
          ·
            refine ⟨5307618962148515946695261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3538412641432343964463507 5307618962148515946695261)
            ·
              refine ⟨1990357110805693480010723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5307618962148515946695261 1990357110805693480010723)
              ·
                refine ⟨2985535666208540220016085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990357110805693480010723 2985535666208540220016085)
                ·
                  refine ⟨69973492176762661406627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2985535666208540220016085 69973492176762661406627)
                  ·
                    rfl

theorem cell22_613228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_613228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613228 prefixEnd_613228 := by exact prefixLift 613228
  have htrace : WordTrace (prefixWord ++ tailWord_613228) baseStart_613228 baseEnd_613228 := by
    simpa [prefixWord, tailWord_613228, baseEnd_613228] using wordTrace_append hprefix tailTrace_613228
  have hstable : (prefixWord ++ tailWord_613228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613228).length < 2 ^ (prefixWord ++ tailWord_613228).sum := by decide
  have hdescent : baseEnd_613228 < baseStart_613228 := by decide
  rcases family_descends (prefixWord ++ tailWord_613228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613232 : List Nat := [2, 1, 1, 1, 4, 1, 4, 4, 1, 3]
def baseStart_613232 : Nat := 118140960795 + 613232 * 2 ^ 59
def prefixEnd_613232 : Nat := 4983230072969 + 3 ^ 40 * 613232 * 2
def baseEnd_613232 : Nat := 209921845812033307119869

theorem tailTrace_613232 : CollatzResearch.WordTrace tailWord_613232 prefixEnd_613232 209921845812033307119869 := by
  unfold tailWord_613232
  simp only [CollatzResearch.WordTrace]
  refine ⟨11183204257186335266296975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14910939009581780355062633 11183204257186335266296975)
  ·
    refine ⟨16774806385779502899445463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11183204257186335266296975 16774806385779502899445463)
    ·
      refine ⟨25162209578669254349168195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16774806385779502899445463 25162209578669254349168195)
      ·
        refine ⟨37743314368003881523752293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25162209578669254349168195 37743314368003881523752293)
        ·
          refine ⟨7076871444000727785703555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37743314368003881523752293 7076871444000727785703555)
          ·
            refine ⟨10615307166001091678555333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7076871444000727785703555 10615307166001091678555333)
            ·
              refine ⟨1990370093625204689729125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10615307166001091678555333 1990370093625204689729125)
              ·
                refine ⟨373194392554725879324211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1990370093625204689729125 373194392554725879324211)
                ·
                  refine ⟨559791588832088818986317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373194392554725879324211 559791588832088818986317)
                  ·
                    refine ⟨209921845812033307119869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 559791588832088818986317 209921845812033307119869)
                    ·
                      rfl

theorem cell22_613232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 1, 3].length) (baseStart_613232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613232 prefixEnd_613232 := by exact prefixLift 613232
  have htrace : WordTrace (prefixWord ++ tailWord_613232) baseStart_613232 baseEnd_613232 := by
    simpa [prefixWord, tailWord_613232, baseEnd_613232] using wordTrace_append hprefix tailTrace_613232
  have hstable : (prefixWord ++ tailWord_613232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613232).length < 2 ^ (prefixWord ++ tailWord_613232).sum := by decide
  have hdescent : baseEnd_613232 < baseStart_613232 := by decide
  rcases family_descends (prefixWord ++ tailWord_613232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613243 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 2, 5]
def baseStart_613243 : Nat := 118140960795 + 613243 * 2 ^ 59
def prefixEnd_613243 : Nat := 4983230072969 + 3 ^ 40 * 613243 * 2
def baseEnd_613243 : Nat := 209925611336832945094835

theorem tailTrace_613243 : CollatzResearch.WordTrace tailWord_613243 prefixEnd_613243 209925611336832945094835 := by
  unfold tailWord_613243
  simp only [CollatzResearch.WordTrace]
  refine ⟨22366809717332819411244383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14911206478221879607496255 22366809717332819411244383)
  ·
    refine ⟨33550214575999229116866575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22366809717332819411244383 33550214575999229116866575)
    ·
      refine ⟨50325321863998843675299863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33550214575999229116866575 50325321863998843675299863)
      ·
        refine ⟨75487982795998265512949795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50325321863998843675299863 75487982795998265512949795)
        ·
          refine ⟨113231974193997398269424693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75487982795998265512949795 113231974193997398269424693)
          ·
            refine ⟨10615497580687256087758565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113231974193997398269424693 10615497580687256087758565)
            ·
              refine ⟨1990405796378860516454731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10615497580687256087758565 1990405796378860516454731)
              ·
                refine ⟨2985608694568290774682097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990405796378860516454731 2985608694568290774682097)
                ·
                  refine ⟨2239206520926218081011573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2985608694568290774682097 2239206520926218081011573)
                  ·
                    refine ⟨209925611336832945094835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2239206520926218081011573 209925611336832945094835)
                    ·
                      rfl

theorem cell22_613243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 5].length) (baseStart_613243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613243 prefixEnd_613243 := by exact prefixLift 613243
  have htrace : WordTrace (prefixWord ++ tailWord_613243) baseStart_613243 baseEnd_613243 := by
    simpa [prefixWord, tailWord_613243, baseEnd_613243] using wordTrace_append hprefix tailTrace_613243
  have hstable : (prefixWord ++ tailWord_613243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613243).length < 2 ^ (prefixWord ++ tailWord_613243).sum := by decide
  have hdescent : baseEnd_613243 < baseStart_613243 := by decide
  rcases family_descends (prefixWord ++ tailWord_613243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613303 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 3, 6]
def baseStart_613303 : Nat := 118140960795 + 613303 * 2 ^ 59
def prefixEnd_613303 : Nat := 4983230072969 + 3 ^ 40 * 613303 * 2
def baseEnd_613303 : Nat := 209946150563012788594651

theorem tailTrace_613303 : CollatzResearch.WordTrace tailWord_613303 prefixEnd_613303 209946150563012788594651 := by
  unfold tailWord_613303
  simp only [CollatzResearch.WordTrace]
  refine ⟨22368998097115449658428563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14912665398076966438952375 22368998097115449658428563)
  ·
    refine ⟨33553497145673174487642845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22368998097115449658428563 33553497145673174487642845)
    ·
      refine ⟨12582561429627440432866067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33553497145673174487642845 12582561429627440432866067)
      ·
        refine ⟨18873842144441160649299101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12582561429627440432866067 18873842144441160649299101)
        ·
          refine ⟨7077690804165435243487163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18873842144441160649299101 7077690804165435243487163)
          ·
            refine ⟨10616536206248152865230745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7077690804165435243487163 10616536206248152865230745)
            ·
              refine ⟨7962402154686114648923059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10616536206248152865230745 7962402154686114648923059)
              ·
                refine ⟨11943603232029171973384589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7962402154686114648923059 11943603232029171973384589)
                ·
                  refine ⟨4478851212010939490019221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11943603232029171973384589 4478851212010939490019221)
                  ·
                    refine ⟨209946150563012788594651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4478851212010939490019221 209946150563012788594651)
                    ·
                      rfl

theorem cell22_613303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_613303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613303 prefixEnd_613303 := by exact prefixLift 613303
  have htrace : WordTrace (prefixWord ++ tailWord_613303) baseStart_613303 baseEnd_613303 := by
    simpa [prefixWord, tailWord_613303, baseEnd_613303] using wordTrace_append hprefix tailTrace_613303
  have hstable : (prefixWord ++ tailWord_613303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613303).length < 2 ^ (prefixWord ++ tailWord_613303).sum := by decide
  have hdescent : baseEnd_613303 < baseStart_613303 := by decide
  rcases family_descends (prefixWord ++ tailWord_613303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613309 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_613309 : Nat := 118140960795 + 613309 * 2 ^ 59
def prefixEnd_613309 : Nat := 4983230072969 + 3 ^ 40 * 613309 * 2
def baseEnd_613309 : Nat := 209948204485630772944633

theorem tailTrace_613309 : CollatzResearch.WordTrace tailWord_613309 prefixEnd_613309 209948204485630772944633 := by
  unfold tailWord_613309
  simp only [CollatzResearch.WordTrace]
  refine ⟨22369216935093712683146981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14912811290062475122097987 22369216935093712683146981)
  ·
    refine ⟨4194228175330071128090059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22369216935093712683146981 4194228175330071128090059)
    ·
      refine ⟨6291342262995106692135089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4194228175330071128090059 6291342262995106692135089)
      ·
        refine ⟨4718506697246330019101317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6291342262995106692135089 4718506697246330019101317)
        ·
          refine ⟨884720005733686878581497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4718506697246330019101317 884720005733686878581497)
          ·
            refine ⟨663540004300265158936123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 884720005733686878581497 663540004300265158936123)
            ·
              refine ⟨995310006450397738404185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663540004300265158936123 995310006450397738404185)
              ·
                refine ⟨746482504837798303803139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 995310006450397738404185 746482504837798303803139)
                ·
                  refine ⟨1119723757256697455704709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 746482504837798303803139 1119723757256697455704709)
                  ·
                    refine ⟨209948204485630772944633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1119723757256697455704709 209948204485630772944633)
                    ·
                      rfl

theorem cell22_613309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_613309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613309 prefixEnd_613309 := by exact prefixLift 613309
  have htrace : WordTrace (prefixWord ++ tailWord_613309) baseStart_613309 baseEnd_613309 := by
    simpa [prefixWord, tailWord_613309, baseEnd_613309] using wordTrace_append hprefix tailTrace_613309
  have hstable : (prefixWord ++ tailWord_613309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613309).length < 2 ^ (prefixWord ++ tailWord_613309).sum := by decide
  have hdescent : baseEnd_613309 < baseStart_613309 := by decide
  rcases family_descends (prefixWord ++ tailWord_613309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613341 : List Nat := [1, 4, 3, 1, 2, 3, 2, 2, 4]
def baseStart_613341 : Nat := 118140960795 + 613341 * 2 ^ 59
def prefixEnd_613341 : Nat := 4983230072969 + 3 ^ 40 * 613341 * 2
def baseEnd_613341 : Nat := 69986386246531118714845

theorem tailTrace_613341 : CollatzResearch.WordTrace tailWord_613341 prefixEnd_613341 69986386246531118714845 := by
  unfold tailWord_613341
  simp only [CollatzResearch.WordTrace]
  refine ⟨22370384070977782148311877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14913589380651854765541251 22370384070977782148311877)
  ·
    refine ⟨4194447013308334152808477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22370384070977782148311877 4194447013308334152808477)
    ·
      refine ⟨1572917629990625307303179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4194447013308334152808477 1572917629990625307303179)
      ·
        refine ⟨2359376444985937960954769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572917629990625307303179 2359376444985937960954769)
        ·
          refine ⟨1769532333739453470716077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2359376444985937960954769 1769532333739453470716077)
          ·
            refine ⟨663574625152295051518529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1769532333739453470716077 663574625152295051518529)
            ·
              refine ⟨497680968864221288638897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663574625152295051518529 497680968864221288638897)
              ·
                refine ⟨373260726648165966479173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497680968864221288638897 373260726648165966479173)
                ·
                  refine ⟨69986386246531118714845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373260726648165966479173 69986386246531118714845)
                  ·
                    rfl

theorem cell22_613341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_613341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613341 prefixEnd_613341 := by exact prefixLift 613341
  have htrace : WordTrace (prefixWord ++ tailWord_613341) baseStart_613341 baseEnd_613341 := by
    simpa [prefixWord, tailWord_613341, baseEnd_613341] using wordTrace_append hprefix tailTrace_613341
  have hstable : (prefixWord ++ tailWord_613341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613341).length < 2 ^ (prefixWord ++ tailWord_613341).sum := by decide
  have hdescent : baseEnd_613341 < baseStart_613341 := by decide
  rcases family_descends (prefixWord ++ tailWord_613341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613363 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 11]
def baseStart_613363 : Nat := 118140960795 + 613363 * 2 ^ 59
def prefixEnd_613363 : Nat := 4983230072969 + 3 ^ 40 * 613363 * 2
def baseEnd_613363 : Nat := 69988896596397544031489

theorem tailTrace_613363 : CollatzResearch.WordTrace tailWord_613363 prefixEnd_613363 69988896596397544031489 := by
  unfold tailWord_613363
  simp only [CollatzResearch.WordTrace]
  refine ⟨22371186476898079905612743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14914124317932053270408495 22371186476898079905612743)
  ·
    refine ⟨33556779715347119858419115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22371186476898079905612743 33556779715347119858419115)
    ·
      refine ⟨50335169573020679787628673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33556779715347119858419115 50335169573020679787628673)
      ·
        refine ⟨37751377179765509840721505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50335169573020679787628673 37751377179765509840721505)
        ·
          refine ⟨28313532884824132380541129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37751377179765509840721505 28313532884824132380541129)
          ·
            refine ⟨21235149663618099285405847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28313532884824132380541129 21235149663618099285405847)
            ·
              refine ⟨31852724495427148928108771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21235149663618099285405847 31852724495427148928108771)
              ·
                refine ⟨47779086743140723392163157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31852724495427148928108771 47779086743140723392163157)
                ·
                  refine ⟨69988896596397544031489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 47779086743140723392163157 69988896596397544031489)
                  ·
                    rfl

theorem cell22_613363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 11].length) (baseStart_613363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613363 prefixEnd_613363 := by exact prefixLift 613363
  have htrace : WordTrace (prefixWord ++ tailWord_613363) baseStart_613363 baseEnd_613363 := by
    simpa [prefixWord, tailWord_613363, baseEnd_613363] using wordTrace_append hprefix tailTrace_613363
  have hstable : (prefixWord ++ tailWord_613363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613363).length < 2 ^ (prefixWord ++ tailWord_613363).sum := by decide
  have hdescent : baseEnd_613363 < baseStart_613363 := by decide
  rcases family_descends (prefixWord ++ tailWord_613363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613384 : List Nat := [2, 1, 3, 2, 1, 3, 1, 5, 1, 3]
def baseStart_613384 : Nat := 118140960795 + 613384 * 2 ^ 59
def prefixEnd_613384 : Nat := 4983230072969 + 3 ^ 40 * 613384 * 2
def baseEnd_613384 : Nat := 209973878518355577319403

theorem tailTrace_613384 : CollatzResearch.WordTrace tailWord_613384 prefixEnd_613384 209973878518355577319403 := by
  unfold tailWord_613384
  simp only [CollatzResearch.WordTrace]
  refine ⟨11185976204911000246063603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14914634939881333661418137 11185976204911000246063603)
  ·
    refine ⟨16778964307366500369095405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11185976204911000246063603 16778964307366500369095405)
    ·
      refine ⟨6292111615262437638410777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16778964307366500369095405 6292111615262437638410777)
      ·
        refine ⟨4719083711446828228808083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6292111615262437638410777 4719083711446828228808083)
        ·
          refine ⟨7078625567170242343212125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4719083711446828228808083 7078625567170242343212125)
          ·
            refine ⟨2654484587688840878704547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7078625567170242343212125 2654484587688840878704547)
            ·
              refine ⟨3981726881533261318056821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2654484587688840878704547 3981726881533261318056821)
              ·
                refine ⟨373286895143743248567827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3981726881533261318056821 373286895143743248567827)
                ·
                  refine ⟨559930342715614872851741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373286895143743248567827 559930342715614872851741)
                  ·
                    refine ⟨209973878518355577319403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 559930342715614872851741 209973878518355577319403)
                    ·
                      rfl

theorem cell22_613384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_613384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613384 prefixEnd_613384 := by exact prefixLift 613384
  have htrace : WordTrace (prefixWord ++ tailWord_613384) baseStart_613384 baseEnd_613384 := by
    simpa [prefixWord, tailWord_613384, baseEnd_613384] using wordTrace_append hprefix tailTrace_613384
  have hstable : (prefixWord ++ tailWord_613384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613384).length < 2 ^ (prefixWord ++ tailWord_613384).sum := by decide
  have hdescent : baseEnd_613384 < baseStart_613384 := by decide
  rcases family_descends (prefixWord ++ tailWord_613384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613397 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 5]
def baseStart_613397 : Nat := 118140960795 + 613397 * 2 ^ 59
def prefixEnd_613397 : Nat := 4983230072969 + 3 ^ 40 * 613397 * 2
def baseEnd_613397 : Nat := 69992776228009292248121

theorem tailTrace_613397 : CollatzResearch.WordTrace tailWord_613397 prefixEnd_613397 69992776228009292248121 := by
  unfold tailWord_613397
  simp only [CollatzResearch.WordTrace]
  refine ⟨22372426558774903712350445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14914951039183269141566963 22372426558774903712350445)
  ·
    refine ⟨8389659959540588892131417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22372426558774903712350445 8389659959540588892131417)
    ·
      refine ⟨6292244969655441669098563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8389659959540588892131417 6292244969655441669098563)
      ·
        refine ⟨9438367454483162503647845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6292244969655441669098563 9438367454483162503647845)
        ·
          refine ⟨1769693897715592969433971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9438367454483162503647845 1769693897715592969433971)
          ·
            refine ⟨2654540846573389454150957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769693897715592969433971 2654540846573389454150957)
            ·
              refine ⟨995452817465021045306609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2654540846573389454150957 995452817465021045306609)
              ·
                refine ⟨746589613098765783979957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 995452817465021045306609 746589613098765783979957)
                ·
                  refine ⟨69992776228009292248121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 746589613098765783979957 69992776228009292248121)
                  ·
                    rfl

theorem cell22_613397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_613397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613397 prefixEnd_613397 := by exact prefixLift 613397
  have htrace : WordTrace (prefixWord ++ tailWord_613397) baseStart_613397 baseEnd_613397 := by
    simpa [prefixWord, tailWord_613397, baseEnd_613397] using wordTrace_append hprefix tailTrace_613397
  have hstable : (prefixWord ++ tailWord_613397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613397).length < 2 ^ (prefixWord ++ tailWord_613397).sum := by decide
  have hdescent : baseEnd_613397 < baseStart_613397 := by decide
  rcases family_descends (prefixWord ++ tailWord_613397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613412 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_613412 : Nat := 118140960795 + 613412 * 2 ^ 59
def prefixEnd_613412 : Nat := 4983230072969 + 3 ^ 40 * 613412 * 2
def baseEnd_613412 : Nat := 209983463490572837619317

theorem tailTrace_613412 : CollatzResearch.WordTrace tailWord_613412 prefixEnd_613412 209983463490572837619317 := by
  unfold tailWord_613412
  simp only [CollatzResearch.WordTrace]
  refine ⟨11186486826860280637073245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14915315769147040849430993 11186486826860280637073245)
  ·
    refine ⟨4194932560072605238902467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11186486826860280637073245 4194932560072605238902467)
    ·
      refine ⟨6292398840108907858353701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4194932560072605238902467 6292398840108907858353701)
      ·
        refine ⟨1179824782520420223441319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6292398840108907858353701 1179824782520420223441319)
        ·
          refine ⟨1769737173780630335161979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179824782520420223441319 1769737173780630335161979)
          ·
            refine ⟨2654605760670945502742969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769737173780630335161979 2654605760670945502742969)
            ·
              refine ⟨1990954320503209127057227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2654605760670945502742969 1990954320503209127057227)
              ·
                refine ⟨2986431480754813690585841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990954320503209127057227 2986431480754813690585841)
                ·
                  refine ⟨2239823610566110267939381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2986431480754813690585841 2239823610566110267939381)
                  ·
                    refine ⟨209983463490572837619317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2239823610566110267939381 209983463490572837619317)
                    ·
                      rfl

theorem cell22_613412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_613412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613412 prefixEnd_613412 := by exact prefixLift 613412
  have htrace : WordTrace (prefixWord ++ tailWord_613412) baseStart_613412 baseEnd_613412 := by
    simpa [prefixWord, tailWord_613412, baseEnd_613412] using wordTrace_append hprefix tailTrace_613412
  have hstable : (prefixWord ++ tailWord_613412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613412).length < 2 ^ (prefixWord ++ tailWord_613412).sum := by decide
  have hdescent : baseEnd_613412 < baseStart_613412 := by decide
  rcases family_descends (prefixWord ++ tailWord_613412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613425 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 6]
def baseStart_613425 : Nat := 118140960795 + 613425 * 2 ^ 59
def prefixEnd_613425 : Nat := 4983230072969 + 3 ^ 40 * 613425 * 2
def baseEnd_613425 : Nat := 69995971218748379014759

theorem tailTrace_613425 : CollatzResearch.WordTrace tailWord_613425 prefixEnd_613425 69995971218748379014759 := by
  unfold tailWord_613425
  simp only [CollatzResearch.WordTrace]
  refine ⟨22373447802673464494369729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14915631868448976329579819 22373447802673464494369729)
  ·
    refine ⟨16780085852005098370777297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22373447802673464494369729 16780085852005098370777297)
    ·
      refine ⟨12585064389003823778082973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16780085852005098370777297 12585064389003823778082973)
      ·
        refine ⟨4719399145876433916781115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12585064389003823778082973 4719399145876433916781115)
        ·
          refine ⟨7079098718814650875171673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4719399145876433916781115 7079098718814650875171673)
          ·
            refine ⟨5309324039110988156378755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7079098718814650875171673 5309324039110988156378755)
            ·
              refine ⟨7963986058666482234568133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5309324039110988156378755 7963986058666482234568133)
              ·
                refine ⟨1493247385999965418981525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7963986058666482234568133 1493247385999965418981525)
                ·
                  refine ⟨69995971218748379014759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1493247385999965418981525 69995971218748379014759)
                  ·
                    rfl

theorem cell22_613425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_613425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613425 prefixEnd_613425 := by exact prefixLift 613425
  have htrace : WordTrace (prefixWord ++ tailWord_613425) baseStart_613425 baseEnd_613425 := by
    simpa [prefixWord, tailWord_613425, baseEnd_613425] using wordTrace_append hprefix tailTrace_613425
  have hstable : (prefixWord ++ tailWord_613425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613425).length < 2 ^ (prefixWord ++ tailWord_613425).sum := by decide
  have hdescent : baseEnd_613425 < baseStart_613425 := by decide
  rcases family_descends (prefixWord ++ tailWord_613425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613440 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_613440 : Nat := 118140960795 + 613440 * 2 ^ 59
def prefixEnd_613440 : Nat := 4983230072969 + 3 ^ 40 * 613440 * 2
def baseEnd_613440 : Nat := 209993048462790097919231

theorem tailTrace_613440 : CollatzResearch.WordTrace tailWord_613440 prefixEnd_613440 209993048462790097919231 := by
  unfold tailWord_613440
  simp only [CollatzResearch.WordTrace]
  refine ⟨11186997448809561028082887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14915996598412748037443849 11186997448809561028082887)
  ·
    refine ⟨16780496173214341542124331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11186997448809561028082887 16780496173214341542124331)
    ·
      refine ⟨25170744259821512313186497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16780496173214341542124331 25170744259821512313186497)
      ·
        refine ⟨18878058194866134234889873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25170744259821512313186497 18878058194866134234889873)
        ·
          refine ⟨14158543646149600676167405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18878058194866134234889873 14158543646149600676167405)
          ·
            refine ⟨5309453867306100253562777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14158543646149600676167405 5309453867306100253562777)
            ·
              refine ⟨3982090400479575190172083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5309453867306100253562777 3982090400479575190172083)
              ·
                refine ⟨5973135600719362785258125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3982090400479575190172083 5973135600719362785258125)
                ·
                  refine ⟨2239925850269761044471797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5973135600719362785258125 2239925850269761044471797)
                  ·
                    refine ⟨209993048462790097919231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2239925850269761044471797 209993048462790097919231)
                    ·
                      rfl

theorem cell22_613440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_613440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613440 prefixEnd_613440 := by exact prefixLift 613440
  have htrace : WordTrace (prefixWord ++ tailWord_613440) baseStart_613440 baseEnd_613440 := by
    simpa [prefixWord, tailWord_613440, baseEnd_613440] using wordTrace_append hprefix tailTrace_613440
  have hstable : (prefixWord ++ tailWord_613440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613440).length < 2 ^ (prefixWord ++ tailWord_613440).sum := by decide
  have hdescent : baseEnd_613440 < baseStart_613440 := by decide
  rcases family_descends (prefixWord ++ tailWord_613440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613457 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 4, 3]
def baseStart_613457 : Nat := 118140960795 + 613457 * 2 ^ 59
def prefixEnd_613457 : Nat := 4983230072969 + 3 ^ 40 * 613457 * 2
def baseEnd_613457 : Nat := 209998867910207720244179

theorem tailTrace_613457 : CollatzResearch.WordTrace tailWord_613457 prefixEnd_613457 209998867910207720244179 := by
  unfold tailWord_613457
  simp only [CollatzResearch.WordTrace]
  refine ⟨22374614938557533959534625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14916409959038355973023083 22374614938557533959534625)
  ·
    refine ⟨16780961203918150469650969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22374614938557533959534625 16780961203918150469650969)
    ·
      refine ⟨12585720902938612852238227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16780961203918150469650969 12585720902938612852238227)
      ·
        refine ⟨18878581354407919278357341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12585720902938612852238227 18878581354407919278357341)
        ·
          refine ⟨7079468007902969729384003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18878581354407919278357341 7079468007902969729384003)
          ·
            refine ⟨10619202011854454594076005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7079468007902969729384003 10619202011854454594076005)
            ·
              refine ⟨1991100377222710236389251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10619202011854454594076005 1991100377222710236389251)
              ·
                refine ⟨2986650565834065354583877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1991100377222710236389251 2986650565834065354583877)
                ·
                  refine ⟨559996981093887253984477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2986650565834065354583877 559996981093887253984477)
                  ·
                    refine ⟨209998867910207720244179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 559996981093887253984477 209998867910207720244179)
                    ·
                      rfl

theorem cell22_613457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_613457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613457 prefixEnd_613457 := by exact prefixLift 613457
  have htrace : WordTrace (prefixWord ++ tailWord_613457) baseStart_613457 baseEnd_613457 := by
    simpa [prefixWord, tailWord_613457, baseEnd_613457] using wordTrace_append hprefix tailTrace_613457
  have hstable : (prefixWord ++ tailWord_613457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613457).length < 2 ^ (prefixWord ++ tailWord_613457).sum := by decide
  have hdescent : baseEnd_613457 < baseStart_613457 := by decide
  rcases family_descends (prefixWord ++ tailWord_613457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613515 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 7]
def baseStart_613515 : Nat := 118140960795 + 613515 * 2 ^ 59
def prefixEnd_613515 : Nat := 4983230072969 + 3 ^ 40 * 613515 * 2
def baseEnd_613515 : Nat := 70006240831838300764667

theorem tailTrace_613515 : CollatzResearch.WordTrace tailWord_613515 prefixEnd_613515 70006240831838300764667 := by
  unfold tailWord_613515
  simp only [CollatzResearch.WordTrace]
  refine ⟨22376730372347409865145999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14917820248231606576763999 22376730372347409865145999)
  ·
    refine ⟨33565095558521114797718999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22376730372347409865145999 33565095558521114797718999)
    ·
      refine ⟨50347643337781672196578499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33565095558521114797718999 50347643337781672196578499)
      ·
        refine ⟨75521465006672508294867749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50347643337781672196578499 75521465006672508294867749)
        ·
          refine ⟨14160274688751095305287703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75521465006672508294867749 14160274688751095305287703)
          ·
            refine ⟨21240412033126642957931555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14160274688751095305287703 21240412033126642957931555)
            ·
              refine ⟨31860618049689964436897333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21240412033126642957931555 31860618049689964436897333)
              ·
                refine ⟨2986932942158434165959125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31860618049689964436897333 2986932942158434165959125)
                ·
                  refine ⟨70006240831838300764667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2986932942158434165959125 70006240831838300764667)
                  ·
                    rfl

theorem cell22_613515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 7].length) (baseStart_613515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613515 prefixEnd_613515 := by exact prefixLift 613515
  have htrace : WordTrace (prefixWord ++ tailWord_613515) baseStart_613515 baseEnd_613515 := by
    simpa [prefixWord, tailWord_613515, baseEnd_613515] using wordTrace_append hprefix tailTrace_613515
  have hstable : (prefixWord ++ tailWord_613515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613515).length < 2 ^ (prefixWord ++ tailWord_613515).sum := by decide
  have hdescent : baseEnd_613515 < baseStart_613515 := by decide
  rcases family_descends (prefixWord ++ tailWord_613515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613545 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_613545 : Nat := 118140960795 + 613545 * 2 ^ 59
def prefixEnd_613545 : Nat := 4983230072969 + 3 ^ 40 * 613545 * 2
def baseEnd_613545 : Nat := 210028992108604824043909

theorem tailTrace_613545 : CollatzResearch.WordTrace tailWord_613545 prefixEnd_613545 210028992108604824043909 := by
  unfold tailWord_613545
  simp only [CollatzResearch.WordTrace]
  refine ⟨22377824562238724988738089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14918549708159149992492059 22377824562238724988738089)
  ·
    refine ⟨16783368421679043741553567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22377824562238724988738089 16783368421679043741553567)
    ·
      refine ⟨25175052632518565612330351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16783368421679043741553567 25175052632518565612330351)
      ·
        refine ⟨37762578948777848418495527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25175052632518565612330351 37762578948777848418495527)
        ·
          refine ⟨56643868423166772627743291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37762578948777848418495527 56643868423166772627743291)
          ·
            refine ⟨84965802634750158941614937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56643868423166772627743291 84965802634750158941614937)
            ·
              refine ⟨63724351976062619206211203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84965802634750158941614937 63724351976062619206211203)
              ·
                refine ⟨95586527964093928809316805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63724351976062619206211203 95586527964093928809316805)
                ·
                  refine ⟨17922473993267611651746901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95586527964093928809316805 17922473993267611651746901)
                  ·
                    refine ⟨210028992108604824043909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17922473993267611651746901 210028992108604824043909)
                    ·
                      rfl

theorem cell22_613545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_613545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613545 prefixEnd_613545 := by exact prefixLift 613545
  have htrace : WordTrace (prefixWord ++ tailWord_613545) baseStart_613545 baseEnd_613545 := by
    simpa [prefixWord, tailWord_613545, baseEnd_613545] using wordTrace_append hprefix tailTrace_613545
  have hstable : (prefixWord ++ tailWord_613545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613545).length < 2 ^ (prefixWord ++ tailWord_613545).sum := by decide
  have hdescent : baseEnd_613545 < baseStart_613545 := by decide
  rcases family_descends (prefixWord ++ tailWord_613545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613553 : List Nat := [1, 2, 2, 5, 1, 2, 2, 3, 1, 3]
def baseStart_613553 : Nat := 118140960795 + 613553 * 2 ^ 59
def prefixEnd_613553 : Nat := 4983230072969 + 3 ^ 40 * 613553 * 2
def baseEnd_613553 : Nat := 210031730672095469843885

theorem tailTrace_613553 : CollatzResearch.WordTrace tailWord_613553 prefixEnd_613553 210031730672095469843885 := by
  unfold tailWord_613553
  simp only [CollatzResearch.WordTrace]
  refine ⟨22378116346209742355029313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14918744230806494903352875 22378116346209742355029313)
  ·
    refine ⟨16783587259657306766271985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22378116346209742355029313 16783587259657306766271985)
    ·
      refine ⟨12587690444742980074703989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16783587259657306766271985 12587690444742980074703989)
      ·
        refine ⟨1180095979194654382003499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12587690444742980074703989 1180095979194654382003499)
        ·
          refine ⟨1770143968791981573005249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180095979194654382003499 1770143968791981573005249)
          ·
            refine ⟨1327607976593986179753937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1770143968791981573005249 1327607976593986179753937)
            ·
              refine ⟨995705982445489634815453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1327607976593986179753937 995705982445489634815453)
              ·
                refine ⟨373389743417058613055795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 995705982445489634815453 373389743417058613055795)
                ·
                  refine ⟨560084615125587919583693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373389743417058613055795 560084615125587919583693)
                  ·
                    refine ⟨210031730672095469843885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560084615125587919583693 210031730672095469843885)
                    ·
                      rfl

theorem cell22_613553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_613553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613553 prefixEnd_613553 := by exact prefixLift 613553
  have htrace : WordTrace (prefixWord ++ tailWord_613553) baseStart_613553 baseEnd_613553 := by
    simpa [prefixWord, tailWord_613553, baseEnd_613553] using wordTrace_append hprefix tailTrace_613553
  have hstable : (prefixWord ++ tailWord_613553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613553).length < 2 ^ (prefixWord ++ tailWord_613553).sum := by decide
  have hdescent : baseEnd_613553 < baseStart_613553 := by decide
  rcases family_descends (prefixWord ++ tailWord_613553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613566 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_613566 : Nat := 118140960795 + 613566 * 2 ^ 59
def prefixEnd_613566 : Nat := 4983230072969 + 3 ^ 40 * 613566 * 2
def baseEnd_613566 : Nat := 70012060279255923089615

theorem tailTrace_613566 : CollatzResearch.WordTrace tailWord_613566 prefixEnd_613566 70012060279255923089615 := by
  unfold tailWord_613566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797323811895330696906569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14919060330108430383501701 2797323811895330696906569)
  ·
    refine ⟨2097992858921498022679927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2797323811895330696906569 2097992858921498022679927)
    ·
      refine ⟨3146989288382247034019891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2097992858921498022679927 3146989288382247034019891)
      ·
        refine ⟨4720483932573370551029837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3146989288382247034019891 4720483932573370551029837)
        ·
          refine ⟨1770181474715013956636189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4720483932573370551029837 1770181474715013956636189)
          ·
            refine ⟨663818053018130233738571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1770181474715013956636189 663818053018130233738571)
            ·
              refine ⟨995727079527195350607857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663818053018130233738571 995727079527195350607857)
              ·
                refine ⟨746795309645396512955893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 995727079527195350607857 746795309645396512955893)
                ·
                  refine ⟨70012060279255923089615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 746795309645396512955893 70012060279255923089615)
                  ·
                    rfl

theorem cell22_613566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_613566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613566 prefixEnd_613566 := by exact prefixLift 613566
  have htrace : WordTrace (prefixWord ++ tailWord_613566) baseStart_613566 baseEnd_613566 := by
    simpa [prefixWord, tailWord_613566, baseEnd_613566] using wordTrace_append hprefix tailTrace_613566
  have hstable : (prefixWord ++ tailWord_613566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613566).length < 2 ^ (prefixWord ++ tailWord_613566).sum := by decide
  have hdescent : baseEnd_613566 < baseStart_613566 := by decide
  rcases family_descends (prefixWord ++ tailWord_613566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613570 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_613570 : Nat := 118140960795 + 613570 * 2 ^ 59
def prefixEnd_613570 : Nat := 4983230072969 + 3 ^ 40 * 613570 * 2
def baseEnd_613570 : Nat := 210037550119513092168833

theorem tailTrace_613570 : CollatzResearch.WordTrace tailWord_613570 prefixEnd_613570 210037550119513092168833 := by
  unfold tailWord_613570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5594684096787038564599541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14919157591432102838932109 5594684096787038564599541)
  ·
    refine ⟨524501634073784865431207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5594684096787038564599541 524501634073784865431207)
    ·
      refine ⟨786752451110677298146811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 524501634073784865431207 786752451110677298146811)
      ·
        refine ⟨1180128676666015947220217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786752451110677298146811 1180128676666015947220217)
        ·
          refine ⟨885096507499511960415163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1180128676666015947220217 885096507499511960415163)
          ·
            refine ⟨1327644761249267940622745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885096507499511960415163 1327644761249267940622745)
            ·
              refine ⟨995733570936950955467059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1327644761249267940622745 995733570936950955467059)
              ·
                refine ⟨1493600356405426433200589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995733570936950955467059 1493600356405426433200589)
                ·
                  refine ⟨560100133652034912450221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1493600356405426433200589 560100133652034912450221)
                  ·
                    refine ⟨210037550119513092168833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560100133652034912450221 210037550119513092168833)
                    ·
                      rfl

theorem cell22_613570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_613570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613570 prefixEnd_613570 := by exact prefixLift 613570
  have htrace : WordTrace (prefixWord ++ tailWord_613570) baseStart_613570 baseEnd_613570 := by
    simpa [prefixWord, tailWord_613570, baseEnd_613570] using wordTrace_append hprefix tailTrace_613570
  have hstable : (prefixWord ++ tailWord_613570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613570).length < 2 ^ (prefixWord ++ tailWord_613570).sum := by decide
  have hdescent : baseEnd_613570 < baseStart_613570 := by decide
  rcases family_descends (prefixWord ++ tailWord_613570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613611 : List Nat := [1, 1, 1, 1, 2, 8, 1, 3, 4]
def baseStart_613611 : Nat := 118140960795 + 613611 * 2 ^ 59
def prefixEnd_613611 : Nat := 4983230072969 + 3 ^ 40 * 613611 * 2
def baseEnd_613611 : Nat := 70017195085800883964569

theorem tailTrace_613611 : CollatzResearch.WordTrace tailWord_613611 prefixEnd_613611 70017195085800883964569 := by
  unfold tailWord_613611
  simp only [CollatzResearch.WordTrace]
  refine ⟨22380231779999618260640687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14920154519999745507093791 22380231779999618260640687)
  ·
    refine ⟨33570347669999427390961031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22380231779999618260640687 33570347669999427390961031)
    ·
      refine ⟨50355521504999141086441547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33570347669999427390961031 50355521504999141086441547)
      ·
        refine ⟨75533282257498711629662321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50355521504999141086441547 75533282257498711629662321)
        ·
          refine ⟨56649961693124033722246741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75533282257498711629662321 56649961693124033722246741)
          ·
            refine ⟨663866738591297270182579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 56649961693124033722246741 663866738591297270182579)
            ·
              refine ⟨995800107886945905273869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663866738591297270182579 995800107886945905273869)
              ·
                refine ⟨373425040457604714477701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 995800107886945905273869 373425040457604714477701)
                ·
                  refine ⟨70017195085800883964569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373425040457604714477701 70017195085800883964569)
                  ·
                    rfl

theorem cell22_613611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 4].length) (baseStart_613611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613611 prefixEnd_613611 := by exact prefixLift 613611
  have htrace : WordTrace (prefixWord ++ tailWord_613611) baseStart_613611 baseEnd_613611 := by
    simpa [prefixWord, tailWord_613611, baseEnd_613611] using wordTrace_append hprefix tailTrace_613611
  have hstable : (prefixWord ++ tailWord_613611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613611).length < 2 ^ (prefixWord ++ tailWord_613611).sum := by decide
  have hdescent : baseEnd_613611 < baseStart_613611 := by decide
  rcases family_descends (prefixWord ++ tailWord_613611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613628 : List Nat := [2, 2, 2, 1, 5, 1, 3, 2, 4]
def baseStart_613628 : Nat := 118140960795 + 613628 * 2 ^ 59
def prefixEnd_613628 : Nat := 4983230072969 + 3 ^ 40 * 613628 * 2
def baseEnd_613628 : Nat := 70019134901606758072885

theorem tailTrace_613628 : CollatzResearch.WordTrace tailWord_613628 prefixEnd_613628 70019134901606758072885 := by
  unfold tailWord_613628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11190425910469015082004769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14920567880625353442673025 11190425910469015082004769)
  ·
    refine ⟨8392819432851761311503577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11190425910469015082004769 8392819432851761311503577)
    ·
      refine ⟨6294614574638820983627683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8392819432851761311503577 6294614574638820983627683)
      ·
        refine ⟨9441921861958231475441525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6294614574638820983627683 9441921861958231475441525)
        ·
          refine ⟨885180174558584200822643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9441921861958231475441525 885180174558584200822643)
          ·
            refine ⟨1327770261837876301233965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885180174558584200822643 1327770261837876301233965)
            ·
              refine ⟨497913848189203612962737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1327770261837876301233965 497913848189203612962737)
              ·
                refine ⟨373435386141902709722053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497913848189203612962737 373435386141902709722053)
                ·
                  refine ⟨70019134901606758072885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373435386141902709722053 70019134901606758072885)
                  ·
                    rfl

theorem cell22_613628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_613628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613628 prefixEnd_613628 := by exact prefixLift 613628
  have htrace : WordTrace (prefixWord ++ tailWord_613628) baseStart_613628 baseEnd_613628 := by
    simpa [prefixWord, tailWord_613628, baseEnd_613628] using wordTrace_append hprefix tailTrace_613628
  have hstable : (prefixWord ++ tailWord_613628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613628).length < 2 ^ (prefixWord ++ tailWord_613628).sum := by decide
  have hdescent : baseEnd_613628 < baseStart_613628 := by decide
  rcases family_descends (prefixWord ++ tailWord_613628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613643 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 2, 3]
def baseStart_613643 : Nat := 118140960795 + 613643 * 2 ^ 59
def prefixEnd_613643 : Nat := 4983230072969 + 3 ^ 40 * 613643 * 2
def baseEnd_613643 : Nat := 210062539511365235093609

theorem tailTrace_613643 : CollatzResearch.WordTrace tailWord_613643 prefixEnd_613643 210062539511365235093609 := by
  unfold tailWord_613643
  simp only [CollatzResearch.WordTrace]
  refine ⟨22381398915883687725805583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14920932610589125150537055 22381398915883687725805583)
  ·
    refine ⟨33572098373825531588708375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22381398915883687725805583 33572098373825531588708375)
    ·
      refine ⟨50358147560738297383062563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33572098373825531588708375 50358147560738297383062563)
      ·
        refine ⟨75537221341107446074593845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50358147560738297383062563 75537221341107446074593845)
        ·
          refine ⟨7081614500728823069493173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75537221341107446074593845 7081614500728823069493173)
          ·
            refine ⟨663901359443327162764985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7081614500728823069493173 663901359443327162764985)
            ·
              refine ⟨497926019582495372073739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663901359443327162764985 497926019582495372073739)
              ·
                refine ⟨746889029373743058110609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497926019582495372073739 746889029373743058110609)
                ·
                  refine ⟨560166772030307293582957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 746889029373743058110609 560166772030307293582957)
                  ·
                    refine ⟨210062539511365235093609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560166772030307293582957 210062539511365235093609)
                    ·
                      rfl

theorem cell22_613643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 2, 3].length) (baseStart_613643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613643 prefixEnd_613643 := by exact prefixLift 613643
  have htrace : WordTrace (prefixWord ++ tailWord_613643) baseStart_613643 baseEnd_613643 := by
    simpa [prefixWord, tailWord_613643, baseEnd_613643] using wordTrace_append hprefix tailTrace_613643
  have hstable : (prefixWord ++ tailWord_613643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613643).length < 2 ^ (prefixWord ++ tailWord_613643).sum := by decide
  have hdescent : baseEnd_613643 < baseStart_613643 := by decide
  rcases family_descends (prefixWord ++ tailWord_613643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613731 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 1, 4]
def baseStart_613731 : Nat := 118140960795 + 613731 * 2 ^ 59
def prefixEnd_613731 : Nat := 4983230072969 + 3 ^ 40 * 613731 * 2
def baseEnd_613731 : Nat := 210092663709762338893339

theorem tailTrace_613731 : CollatzResearch.WordTrace tailWord_613731 prefixEnd_613731 210092663709762338893339 := by
  unfold tailWord_613731
  simp only [CollatzResearch.WordTrace]
  refine ⟨22384608539564878755009047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14923072359709919170006031 22384608539564878755009047)
  ·
    refine ⟨33576912809347318132513571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22384608539564878755009047 33576912809347318132513571)
    ·
      refine ⟨50365369214020977198770357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33576912809347318132513571 50365369214020977198770357)
      ·
        refine ⟨4721753363814466612384721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50365369214020977198770357 4721753363814466612384721)
        ·
          refine ⟨3541315022860849959288541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4721753363814466612384721 3541315022860849959288541)
          ·
            refine ⟨1327993133572818734733203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3541315022860849959288541 1327993133572818734733203)
            ·
              refine ⟨1991989700359228102099805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1327993133572818734733203 1991989700359228102099805)
              ·
                refine ⟨746996137634710538287427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1991989700359228102099805 746996137634710538287427)
                ·
                  refine ⟨1120494206452065807431141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 746996137634710538287427 1120494206452065807431141)
                  ·
                    refine ⟨210092663709762338893339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1120494206452065807431141 210092663709762338893339)
                    ·
                      rfl

theorem cell22_613731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 4].length) (baseStart_613731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613731 prefixEnd_613731 := by exact prefixLift 613731
  have htrace : WordTrace (prefixWord ++ tailWord_613731) baseStart_613731 baseEnd_613731 := by
    simpa [prefixWord, tailWord_613731, baseEnd_613731] using wordTrace_append hprefix tailTrace_613731
  have hstable : (prefixWord ++ tailWord_613731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613731).length < 2 ^ (prefixWord ++ tailWord_613731).sum := by decide
  have hdescent : baseEnd_613731 < baseStart_613731 := by decide
  rcases family_descends (prefixWord ++ tailWord_613731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613746 : List Nat := [3, 2, 1, 2, 1, 2, 1, 6, 4]
def baseStart_613746 : Nat := 118140960795 + 613746 * 2 ^ 59
def prefixEnd_613746 : Nat := 4983230072969 + 3 ^ 40 * 613746 * 2
def baseEnd_613746 : Nat := 70032599505435766589431

theorem tailTrace_613746 : CollatzResearch.WordTrace tailWord_613746 prefixEnd_613746 70032599505435766589431 := by
  unfold tailWord_613746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5596288908627634079201273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14923437089673690877870061 5596288908627634079201273)
  ·
    refine ⟨4197216681470725559400955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5596288908627634079201273 4197216681470725559400955)
    ·
      refine ⟨6295825022206088339101433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4197216681470725559400955 6295825022206088339101433)
      ·
        refine ⟨4721868766654566254326075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6295825022206088339101433 4721868766654566254326075)
        ·
          refine ⟨7082803149981849381489113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721868766654566254326075 7082803149981849381489113)
          ·
            refine ⟨5312102362486387036116835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7082803149981849381489113 5312102362486387036116835)
            ·
              refine ⟨7968153543729580554175253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5312102362486387036116835 7968153543729580554175253)
              ·
                refine ⟨373507197362324088476965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7968153543729580554175253 373507197362324088476965)
                ·
                  refine ⟨70032599505435766589431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373507197362324088476965 70032599505435766589431)
                  ·
                    rfl

theorem cell22_613746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_613746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613746 prefixEnd_613746 := by exact prefixLift 613746
  have htrace : WordTrace (prefixWord ++ tailWord_613746) baseStart_613746 baseEnd_613746 := by
    simpa [prefixWord, tailWord_613746, baseEnd_613746] using wordTrace_append hprefix tailTrace_613746
  have hstable : (prefixWord ++ tailWord_613746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613746).length < 2 ^ (prefixWord ++ tailWord_613746).sum := by decide
  have hdescent : baseEnd_613746 < baseStart_613746 := by decide
  rcases family_descends (prefixWord ++ tailWord_613746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613780 : List Nat := [2, 4, 2, 1, 2, 3, 1, 3, 4]
def baseStart_613780 : Nat := 118140960795 + 613780 * 2 ^ 59
def prefixEnd_613780 : Nat := 4983230072969 + 3 ^ 40 * 613780 * 2
def baseEnd_613780 : Nat := 70036479137047514806063

theorem tailTrace_613780 : CollatzResearch.WordTrace tailWord_613780 prefixEnd_613780 70036479137047514806063 := by
  unfold tailWord_613780
  simp only [CollatzResearch.WordTrace]
  refine ⟨11193197858193680061771397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14924263810924906749028529 11193197858193680061771397)
  ·
    refine ⟨2098724598411315011582137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11193197858193680061771397 2098724598411315011582137)
    ·
      refine ⟨1574043448808486258686603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2098724598411315011582137 1574043448808486258686603)
      ·
        refine ⟨2361065173212729388029905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574043448808486258686603 2361065173212729388029905)
        ·
          refine ⟨1770798879909547041022429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2361065173212729388029905 1770798879909547041022429)
          ·
            refine ⟨664049579966080140383411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1770798879909547041022429 664049579966080140383411)
            ·
              refine ⟨996074369949120210575117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664049579966080140383411 996074369949120210575117)
              ·
                refine ⟨373527888730920078965669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 996074369949120210575117 373527888730920078965669)
                ·
                  refine ⟨70036479137047514806063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373527888730920078965669 70036479137047514806063)
                  ·
                    rfl

theorem cell22_613780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_613780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613780 prefixEnd_613780 := by exact prefixLift 613780
  have htrace : WordTrace (prefixWord ++ tailWord_613780) baseStart_613780 baseEnd_613780 := by
    simpa [prefixWord, tailWord_613780, baseEnd_613780] using wordTrace_append hprefix tailTrace_613780
  have hstable : (prefixWord ++ tailWord_613780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613780).length < 2 ^ (prefixWord ++ tailWord_613780).sum := by decide
  have hdescent : baseEnd_613780 < baseStart_613780 := by decide
  rcases family_descends (prefixWord ++ tailWord_613780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613853 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 5]
def baseStart_613853 : Nat := 118140960795 + 613853 * 2 ^ 59
def prefixEnd_613853 : Nat := 4983230072969 + 3 ^ 40 * 613853 * 2
def baseEnd_613853 : Nat := 70044808934331562447655

theorem tailTrace_613853 : CollatzResearch.WordTrace tailWord_613853 prefixEnd_613853 70044808934331562447655 := by
  unfold tailWord_613853
  simp only [CollatzResearch.WordTrace]
  refine ⟨22389058245122893590950213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14926038830081929060633475 22389058245122893590950213)
  ·
    refine ⟨4197948420960542548303165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22389058245122893590950213 4197948420960542548303165)
    ·
      refine ⟨1574230657860203455613687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4197948420960542548303165 1574230657860203455613687)
      ·
        refine ⟨2361345986790305183420531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574230657860203455613687 2361345986790305183420531)
        ·
          refine ⟨3542018980185457775130797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361345986790305183420531 3542018980185457775130797)
          ·
            refine ⟨1328257117569546665674049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3542018980185457775130797 1328257117569546665674049)
            ·
              refine ⟨996192838177159999255537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328257117569546665674049 996192838177159999255537)
              ·
                refine ⟨747144628632869999441653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 996192838177159999255537 747144628632869999441653)
                ·
                  refine ⟨70044808934331562447655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 747144628632869999441653 70044808934331562447655)
                  ·
                    rfl

theorem cell22_613853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_613853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613853 prefixEnd_613853 := by exact prefixLift 613853
  have htrace : WordTrace (prefixWord ++ tailWord_613853) baseStart_613853 baseEnd_613853 := by
    simpa [prefixWord, tailWord_613853, baseEnd_613853] using wordTrace_append hprefix tailTrace_613853
  have hstable : (prefixWord ++ tailWord_613853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613853).length < 2 ^ (prefixWord ++ tailWord_613853).sum := by decide
  have hdescent : baseEnd_613853 < baseStart_613853 := by decide
  rcases family_descends (prefixWord ++ tailWord_613853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613857 : List Nat := [1, 2, 3, 1, 2, 5, 2, 2, 1, 3]
def baseStart_613857 : Nat := 118140960795 + 613857 * 2 ^ 59
def prefixEnd_613857 : Nat := 4983230072969 + 3 ^ 40 * 613857 * 2
def baseEnd_613857 : Nat := 210135796084740010242953

theorem tailTrace_613857 : CollatzResearch.WordTrace tailWord_613857 prefixEnd_613857 210135796084740010242953 := by
  unfold tailWord_613857
  simp only [CollatzResearch.WordTrace]
  refine ⟨22389204137108402274095825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14926136091405601516063883 22389204137108402274095825)
  ·
    refine ⟨16791903102831301705571869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22389204137108402274095825 16791903102831301705571869)
    ·
      refine ⟨6296963663561738139589451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16791903102831301705571869 6296963663561738139589451)
      ·
        refine ⟨9445445495342607209384177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6296963663561738139589451 9445445495342607209384177)
        ·
          refine ⟨7084084121506955407038133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9445445495342607209384177 7084084121506955407038133)
          ·
            refine ⟨664132886391277069409825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7084084121506955407038133 664132886391277069409825)
            ·
              refine ⟨498099664793457802057369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664132886391277069409825 498099664793457802057369)
              ·
                refine ⟨373574748595093351543027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498099664793457802057369 373574748595093351543027)
                ·
                  refine ⟨560362122892640027314541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373574748595093351543027 560362122892640027314541)
                  ·
                    refine ⟨210135796084740010242953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560362122892640027314541 210135796084740010242953)
                    ·
                      rfl

theorem cell22_613857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_613857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613857 prefixEnd_613857 := by exact prefixLift 613857
  have htrace : WordTrace (prefixWord ++ tailWord_613857) baseStart_613857 baseEnd_613857 := by
    simpa [prefixWord, tailWord_613857, baseEnd_613857] using wordTrace_append hprefix tailTrace_613857
  have hstable : (prefixWord ++ tailWord_613857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613857).length < 2 ^ (prefixWord ++ tailWord_613857).sum := by decide
  have hdescent : baseEnd_613857 < baseStart_613857 := by decide
  rcases family_descends (prefixWord ++ tailWord_613857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613896 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 1, 5]
def baseStart_613896 : Nat := 118140960795 + 613896 * 2 ^ 59
def prefixEnd_613896 : Nat := 4983230072969 + 3 ^ 40 * 613896 * 2
def baseEnd_613896 : Nat := 210149146581756908517833

theorem tailTrace_613896 : CollatzResearch.WordTrace tailWord_613896 prefixEnd_613896 210149146581756908517833 := by
  unfold tailWord_613896
  simp only [CollatzResearch.WordTrace]
  refine ⟨11195313291983555967382771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14927084389311407956510361 11195313291983555967382771)
  ·
    refine ⟨16792969937975333951074157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11195313291983555967382771 16792969937975333951074157)
    ·
      refine ⟨6297363726740750231652809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16792969937975333951074157 6297363726740750231652809)
      ·
        refine ⟨4723022795055562673739607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6297363726740750231652809 4723022795055562673739607)
        ·
          refine ⟨7084534192583344010609411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4723022795055562673739607 7084534192583344010609411)
          ·
            refine ⟨10626801288875016015914117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7084534192583344010609411 10626801288875016015914117)
            ·
              refine ⟨1992525241664065502983897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10626801288875016015914117 1992525241664065502983897)
              ·
                refine ⟨1494393931248049127237923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1992525241664065502983897 1494393931248049127237923)
                ·
                  refine ⟨2241590896872073690856885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494393931248049127237923 2241590896872073690856885)
                  ·
                    refine ⟨210149146581756908517833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2241590896872073690856885 210149146581756908517833)
                    ·
                      rfl

theorem cell22_613896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_613896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613896 prefixEnd_613896 := by exact prefixLift 613896
  have htrace : WordTrace (prefixWord ++ tailWord_613896) baseStart_613896 baseEnd_613896 := by
    simpa [prefixWord, tailWord_613896, baseEnd_613896] using wordTrace_append hprefix tailTrace_613896
  have hstable : (prefixWord ++ tailWord_613896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613896).length < 2 ^ (prefixWord ++ tailWord_613896).sum := by decide
  have hdescent : baseEnd_613896 < baseStart_613896 := by decide
  rcases family_descends (prefixWord ++ tailWord_613896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613898 : List Nat := [3, 1, 2, 2, 2, 2, 1, 5, 4]
def baseStart_613898 : Nat := 118140960795 + 613898 * 2 ^ 59
def prefixEnd_613898 : Nat := 4983230072969 + 3 ^ 40 * 613898 * 2
def baseEnd_613898 : Nat := 70049943740876523322609

theorem tailTrace_613898 : CollatzResearch.WordTrace tailWord_613898 prefixEnd_613898 70049943740876523322609 := by
  unfold tailWord_613898
  simp only [CollatzResearch.WordTrace]
  refine ⟨5597674882489966569084587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14927133019973244184225565 5597674882489966569084587)
  ·
    refine ⟨8396512323734949853626881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5597674882489966569084587 8396512323734949853626881)
    ·
      refine ⟨6297384242801212390220161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8396512323734949853626881 6297384242801212390220161)
      ·
        refine ⟨4723038182100909292665121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6297384242801212390220161 4723038182100909292665121)
        ·
          refine ⟨3542278636575681969498841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4723038182100909292665121 3542278636575681969498841)
          ·
            refine ⟨2656708977431761477124131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3542278636575681969498841 2656708977431761477124131)
            ·
              refine ⟨3985063466147642215686197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2656708977431761477124131 3985063466147642215686197)
              ·
                refine ⟨373599699951341457720581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3985063466147642215686197 373599699951341457720581)
                ·
                  refine ⟨70049943740876523322609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373599699951341457720581 70049943740876523322609)
                  ·
                    rfl

theorem cell22_613898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_613898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613898 prefixEnd_613898 := by exact prefixLift 613898
  have htrace : WordTrace (prefixWord ++ tailWord_613898) baseStart_613898 baseEnd_613898 := by
    simpa [prefixWord, tailWord_613898, baseEnd_613898] using wordTrace_append hprefix tailTrace_613898
  have hstable : (prefixWord ++ tailWord_613898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613898).length < 2 ^ (prefixWord ++ tailWord_613898).sum := by decide
  have hdescent : baseEnd_613898 < baseStart_613898 := by decide
  rcases family_descends (prefixWord ++ tailWord_613898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613943 : List Nat := [1, 1, 3, 1, 2, 6, 2, 6]
def baseStart_613943 : Nat := 118140960795 + 613943 * 2 ^ 59
def prefixEnd_613943 : Nat := 4983230072969 + 3 ^ 40 * 613943 * 2
def baseEnd_613943 : Nat := 23351692849140494732521

theorem tailTrace_613943 : CollatzResearch.WordTrace tailWord_613943 prefixEnd_613943 23351692849140494732521 := by
  unfold tailWord_613943
  simp only [CollatzResearch.WordTrace]
  refine ⟨22392340814796838961726483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14928227209864559307817655 22392340814796838961726483)
  ·
    refine ⟨33588511222195258442589725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22392340814796838961726483 33588511222195258442589725)
    ·
      refine ⟨12595691708323221915971147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33588511222195258442589725 12595691708323221915971147)
      ·
        refine ⟨18893537562484832873956721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12595691708323221915971147 18893537562484832873956721)
        ·
          refine ⟨14170153171863624655467541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18893537562484832873956721 14170153171863624655467541)
          ·
            refine ⟨664225929931107405725041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14170153171863624655467541 664225929931107405725041)
            ·
              refine ⟨498169447448330554293781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664225929931107405725041 498169447448330554293781)
              ·
                refine ⟨23351692849140494732521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 498169447448330554293781 23351692849140494732521)
                ·
                  rfl

theorem cell22_613943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 6].length) (baseStart_613943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613943 prefixEnd_613943 := by exact prefixLift 613943
  have htrace : WordTrace (prefixWord ++ tailWord_613943) baseStart_613943 baseEnd_613943 := by
    simpa [prefixWord, tailWord_613943, baseEnd_613943] using wordTrace_append hprefix tailTrace_613943
  have hstable : (prefixWord ++ tailWord_613943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613943).length < 2 ^ (prefixWord ++ tailWord_613943).sum := by decide
  have hdescent : baseEnd_613943 < baseStart_613943 := by decide
  rcases family_descends (prefixWord ++ tailWord_613943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613975 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 3, 3]
def baseStart_613975 : Nat := 118140960795 + 613975 * 2 ^ 59
def prefixEnd_613975 : Nat := 4983230072969 + 3 ^ 40 * 613975 * 2
def baseEnd_613975 : Nat := 210176189896227035792591

theorem tailTrace_613975 : CollatzResearch.WordTrace tailWord_613975 prefixEnd_613975 210176189896227035792591 := by
  unfold tailWord_613975
  simp only [CollatzResearch.WordTrace]
  refine ⟨22393507950680908426891379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14929005300453938951260919 22393507950680908426891379)
  ·
    refine ⟨33590261926021362640337069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22393507950680908426891379 33590261926021362640337069)
    ·
      refine ⟨12596348222258010990126401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33590261926021362640337069 12596348222258010990126401)
      ·
        refine ⟨9447261166693508242594801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12596348222258010990126401 9447261166693508242594801)
        ·
          refine ⟨7085445875020131181946101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9447261166693508242594801 7085445875020131181946101)
          ·
            refine ⟨664260550783137298307447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7085445875020131181946101 664260550783137298307447)
            ·
              refine ⟨996390826174705947461171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664260550783137298307447 996390826174705947461171)
              ·
                refine ⟨1494586239262058921191757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996390826174705947461171 1494586239262058921191757)
                ·
                  refine ⟨560469839723272095446909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1494586239262058921191757 560469839723272095446909)
                  ·
                    refine ⟨210176189896227035792591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560469839723272095446909 210176189896227035792591)
                    ·
                      rfl

theorem cell22_613975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_613975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613975 prefixEnd_613975 := by exact prefixLift 613975
  have htrace : WordTrace (prefixWord ++ tailWord_613975) baseStart_613975 baseEnd_613975 := by
    simpa [prefixWord, tailWord_613975, baseEnd_613975] using wordTrace_append hprefix tailTrace_613975
  have hstable : (prefixWord ++ tailWord_613975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613975).length < 2 ^ (prefixWord ++ tailWord_613975).sum := by decide
  have hdescent : baseEnd_613975 < baseStart_613975 := by decide
  rcases family_descends (prefixWord ++ tailWord_613975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613981 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_613981 : Nat := 118140960795 + 613981 * 2 ^ 59
def prefixEnd_613981 : Nat := 4983230072969 + 3 ^ 40 * 613981 * 2
def baseEnd_613981 : Nat := 210178243818845020142573

theorem tailTrace_613981 : CollatzResearch.WordTrace tailWord_613981 prefixEnd_613981 210178243818845020142573 := by
  unfold tailWord_613981
  simp only [CollatzResearch.WordTrace]
  refine ⟨22393726788659171451609797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14929151192439447634406531 22393726788659171451609797)
  ·
    refine ⟨4198823772873594647176837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22393726788659171451609797 4198823772873594647176837)
    ·
      refine ⟨787279457413798996345657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4198823772873594647176837 787279457413798996345657)
      ·
        refine ⟨590459593060349247259243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 787279457413798996345657 590459593060349247259243)
        ·
          refine ⟨885689389590523870888865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590459593060349247259243 885689389590523870888865)
          ·
            refine ⟨664267042192892903166649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885689389590523870888865 664267042192892903166649)
            ·
              refine ⟨498200281644669677374987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664267042192892903166649 498200281644669677374987)
              ·
                refine ⟨747300422467004516062481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498200281644669677374987 747300422467004516062481)
                ·
                  refine ⟨560475316850253387046861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 747300422467004516062481 560475316850253387046861)
                  ·
                    refine ⟨210178243818845020142573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560475316850253387046861 210178243818845020142573)
                    ·
                      rfl

theorem cell22_613981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_613981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613981 prefixEnd_613981 := by exact prefixLift 613981
  have htrace : WordTrace (prefixWord ++ tailWord_613981) baseStart_613981 baseEnd_613981 := by
    simpa [prefixWord, tailWord_613981, baseEnd_613981] using wordTrace_append hprefix tailTrace_613981
  have hstable : (prefixWord ++ tailWord_613981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613981).length < 2 ^ (prefixWord ++ tailWord_613981).sum := by decide
  have hdescent : baseEnd_613981 < baseStart_613981 := by decide
  rcases family_descends (prefixWord ++ tailWord_613981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_613988 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 5]
def baseStart_613988 : Nat := 118140960795 + 613988 * 2 ^ 59
def prefixEnd_613988 : Nat := 4983230072969 + 3 ^ 40 * 613988 * 2
def baseEnd_613988 : Nat := 70060213353966445072517

theorem tailTrace_613988 : CollatzResearch.WordTrace tailWord_613988 prefixEnd_613988 70060213353966445072517 := by
  unfold tailWord_613988
  simp only [CollatzResearch.WordTrace]
  refine ⟨11196991049816905823557309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14929321399755874431409745 11196991049816905823557309)
  ·
    refine ⟨4198871643681339683833991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11196991049816905823557309 4198871643681339683833991)
    ·
      refine ⟨6298307465522009525750987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4198871643681339683833991 6298307465522009525750987)
      ·
        refine ⟨9447461198283014288626481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6298307465522009525750987 9447461198283014288626481)
        ·
          refine ⟨7085595898712260716469861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9447461198283014288626481 7085595898712260716469861)
          ·
            refine ⟨1328549231008548884338099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7085595898712260716469861 1328549231008548884338099)
            ·
              refine ⟨1992823846512823326507149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328549231008548884338099 1992823846512823326507149)
              ·
                refine ⟨747308942442308747440181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1992823846512823326507149 747308942442308747440181)
                ·
                  refine ⟨70060213353966445072517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 747308942442308747440181 70060213353966445072517)
                  ·
                    rfl

theorem cell22_613988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_613988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_613988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_613988 prefixEnd_613988 := by exact prefixLift 613988
  have htrace : WordTrace (prefixWord ++ tailWord_613988) baseStart_613988 baseEnd_613988 := by
    simpa [prefixWord, tailWord_613988, baseEnd_613988] using wordTrace_append hprefix tailTrace_613988
  have hstable : (prefixWord ++ tailWord_613988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_613988).length < 2 ^ (prefixWord ++ tailWord_613988).sum := by decide
  have hdescent : baseEnd_613988 < baseStart_613988 := by decide
  rcases family_descends (prefixWord ++ tailWord_613988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614048 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 1, 5]
def baseStart_614048 : Nat := 118140960795 + 614048 * 2 ^ 59
def prefixEnd_614048 : Nat := 4983230072969 + 3 ^ 40 * 614048 * 2
def baseEnd_614048 : Nat := 210201179288079178717367

theorem tailTrace_614048 : CollatzResearch.WordTrace tailWord_614048 prefixEnd_614048 210201179288079178717367 := by
  unfold tailWord_614048
  simp only [CollatzResearch.WordTrace]
  refine ⟨11198085239708220947149399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14930780319610961262865865 11198085239708220947149399)
  ·
    refine ⟨16797127859562331420724099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11198085239708220947149399 16797127859562331420724099)
    ·
      refine ⟨25195691789343497131086149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16797127859562331420724099 25195691789343497131086149)
      ·
        refine ⟨4724192210501905712078653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25195691789343497131086149 4724192210501905712078653)
        ·
          refine ⟨1771572078938214642029495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4724192210501905712078653 1771572078938214642029495)
          ·
            refine ⟨2657358118407321963044243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771572078938214642029495 2657358118407321963044243)
            ·
              refine ⟨3986037177610982944566365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657358118407321963044243 3986037177610982944566365)
              ·
                refine ⟨1494763941604118604212387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3986037177610982944566365 1494763941604118604212387)
                ·
                  refine ⟨2242145912406177906318581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494763941604118604212387 2242145912406177906318581)
                  ·
                    refine ⟨210201179288079178717367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2242145912406177906318581 210201179288079178717367)
                    ·
                      rfl

theorem cell22_614048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_614048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614048 prefixEnd_614048 := by exact prefixLift 614048
  have htrace : WordTrace (prefixWord ++ tailWord_614048) baseStart_614048 baseEnd_614048 := by
    simpa [prefixWord, tailWord_614048, baseEnd_614048] using wordTrace_append hprefix tailTrace_614048
  have hstable : (prefixWord ++ tailWord_614048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614048).length < 2 ^ (prefixWord ++ tailWord_614048).sum := by decide
  have hdescent : baseEnd_614048 < baseStart_614048 := by decide
  rcases family_descends (prefixWord ++ tailWord_614048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614069 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 1, 4]
def baseStart_614069 : Nat := 118140960795 + 614069 * 2 ^ 59
def prefixEnd_614069 : Nat := 4983230072969 + 3 ^ 40 * 614069 * 2
def baseEnd_614069 : Nat := 210208368017242123942303

theorem tailTrace_614069 : CollatzResearch.WordTrace tailWord_614069 prefixEnd_614069 210208368017242123942303 := by
  unfold tailWord_614069
  simp only [CollatzResearch.WordTrace]
  refine ⟨22396936412340362480813261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14931290941560241653875507 22396936412340362480813261)
  ·
    refine ⟨8398851154627635930304973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22396936412340362480813261 8398851154627635930304973)
    ·
      refine ⟨3149569182985363473864365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8398851154627635930304973 3149569182985363473864365)
      ·
        refine ⟨1181088443619511302699137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3149569182985363473864365 1181088443619511302699137)
        ·
          refine ⟨885816332714633477024353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1181088443619511302699137 885816332714633477024353)
          ·
            refine ⟨664362249535975107768265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885816332714633477024353 664362249535975107768265)
            ·
              refine ⟨498271687151981330826199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664362249535975107768265 498271687151981330826199)
              ·
                refine ⟨747407530727971996239299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498271687151981330826199 747407530727971996239299)
                ·
                  refine ⟨1121111296091957994358949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747407530727971996239299 1121111296091957994358949)
                  ·
                    refine ⟨210208368017242123942303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1121111296091957994358949 210208368017242123942303)
                    ·
                      rfl

theorem cell22_614069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_614069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614069 prefixEnd_614069 := by exact prefixLift 614069
  have htrace : WordTrace (prefixWord ++ tailWord_614069) baseStart_614069 baseEnd_614069 := by
    simpa [prefixWord, tailWord_614069, baseEnd_614069] using wordTrace_append hprefix tailTrace_614069
  have hstable : (prefixWord ++ tailWord_614069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614069).length < 2 ^ (prefixWord ++ tailWord_614069).sum := by decide
  have hdescent : baseEnd_614069 < baseStart_614069 := by decide
  rcases family_descends (prefixWord ++ tailWord_614069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614078 : List Nat := [4, 2, 1, 1, 2, 3, 9]
def baseStart_614078 : Nat := 118140960795 + 614078 * 2 ^ 59
def prefixEnd_614078 : Nat := 4983230072969 + 3 ^ 40 * 614078 * 2
def baseEnd_614078 : Nat := 7785609218561818535825

theorem tailTrace_614078 : CollatzResearch.WordTrace tailWord_614078 prefixEnd_614078 7785609218561818535825 := by
  unfold tailWord_614078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799658083663469627236361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14931509779538504678593925 2799658083663469627236361)
  ·
    refine ⟨2099743562747602220427271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2799658083663469627236361 2099743562747602220427271)
    ·
      refine ⟨3149615344121403330640907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2099743562747602220427271 3149615344121403330640907)
      ·
        refine ⟨4724423016182104995961361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3149615344121403330640907 4724423016182104995961361)
        ·
          refine ⟨3543317262136578746971021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4724423016182104995961361 3543317262136578746971021)
          ·
            refine ⟨1328743973301217030114133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3543317262136578746971021 1328743973301217030114133)
            ·
              refine ⟨7785609218561818535825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1328743973301217030114133 7785609218561818535825)
              ·
                rfl

theorem cell22_614078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 9].length) (baseStart_614078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614078 prefixEnd_614078 := by exact prefixLift 614078
  have htrace : WordTrace (prefixWord ++ tailWord_614078) baseStart_614078 baseEnd_614078 := by
    simpa [prefixWord, tailWord_614078, baseEnd_614078] using wordTrace_append hprefix tailTrace_614078
  have hstable : (prefixWord ++ tailWord_614078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614078).length < 2 ^ (prefixWord ++ tailWord_614078).sum := by decide
  have hdescent : baseEnd_614078 < baseStart_614078 := by decide
  rcases family_descends (prefixWord ++ tailWord_614078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614091 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 1, 8]
def baseStart_614091 : Nat := 118140960795 + 614091 * 2 ^ 59
def prefixEnd_614091 : Nat := 4983230072969 + 3 ^ 40 * 614091 * 2
def baseEnd_614091 : Nat := 210215899066841399892235

theorem tailTrace_614091 : CollatzResearch.WordTrace tailWord_614091 prefixEnd_614091 210215899066841399892235 := by
  unfold tailWord_614091
  simp only [CollatzResearch.WordTrace]
  refine ⟨22397738818260660238114127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14931825878840440158742751 22397738818260660238114127)
  ·
    refine ⟨33596608227390990357171191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22397738818260660238114127 33596608227390990357171191)
    ·
      refine ⟨50394912341086485535756787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33596608227390990357171191 50394912341086485535756787)
      ·
        refine ⟨75592368511629728303635181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50394912341086485535756787 75592368511629728303635181)
        ·
          refine ⟨28347138191861148113863193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75592368511629728303635181 28347138191861148113863193)
          ·
            refine ⟨21260353643895861085397395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28347138191861148113863193 21260353643895861085397395)
            ·
              refine ⟨31890530465843791628096093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21260353643895861085397395 31890530465843791628096093)
              ·
                refine ⟨11958948924691421860536035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31890530465843791628096093 11958948924691421860536035)
                ·
                  refine ⟨17938423387037132790804053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11958948924691421860536035 17938423387037132790804053)
                  ·
                    refine ⟨210215899066841399892235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17938423387037132790804053 210215899066841399892235)
                    ·
                      rfl

theorem cell22_614091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_614091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614091 prefixEnd_614091 := by exact prefixLift 614091
  have htrace : WordTrace (prefixWord ++ tailWord_614091) baseStart_614091 baseEnd_614091 := by
    simpa [prefixWord, tailWord_614091, baseEnd_614091] using wordTrace_append hprefix tailTrace_614091
  have hstable : (prefixWord ++ tailWord_614091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614091).length < 2 ^ (prefixWord ++ tailWord_614091).sum := by decide
  have hdescent : baseEnd_614091 < baseStart_614091 := by decide
  rcases family_descends (prefixWord ++ tailWord_614091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614150 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_614150 : Nat := 118140960795 + 614150 * 2 ^ 59
def prefixEnd_614150 : Nat := 4983230072969 + 3 ^ 40 * 614150 * 2
def baseEnd_614150 : Nat := 210236095972584912667055

theorem tailTrace_614150 : CollatzResearch.WordTrace tailWord_614150 prefixEnd_614150 210236095972584912667055 := by
  unfold tailWord_614150
  simp only [CollatzResearch.WordTrace]
  refine ⟨699996585157716041078497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14933260483364608876341269 699996585157716041078497)
  ·
    refine ⟨524997438868287030808873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 699996585157716041078497 524997438868287030808873)
    ·
      refine ⟨393748079151215273106655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 524997438868287030808873 393748079151215273106655)
      ·
        refine ⟨590622118726822909659983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393748079151215273106655 590622118726822909659983)
        ·
          refine ⟨885933178090234364489975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590622118726822909659983 885933178090234364489975)
          ·
            refine ⟨1328899767135351546734963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885933178090234364489975 1328899767135351546734963)
            ·
              refine ⟨1993349650703027320102445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328899767135351546734963 1993349650703027320102445)
              ·
                refine ⟨747506119013635245038417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1993349650703027320102445 747506119013635245038417)
                ·
                  refine ⟨560629589260226433778813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 747506119013635245038417 560629589260226433778813)
                  ·
                    refine ⟨210236095972584912667055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560629589260226433778813 210236095972584912667055)
                    ·
                      rfl

theorem cell22_614150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_614150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614150 prefixEnd_614150 := by exact prefixLift 614150
  have htrace : WordTrace (prefixWord ++ tailWord_614150) baseStart_614150 baseEnd_614150 := by
    simpa [prefixWord, tailWord_614150, baseEnd_614150] using wordTrace_append hprefix tailTrace_614150
  have hstable : (prefixWord ++ tailWord_614150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614150).length < 2 ^ (prefixWord ++ tailWord_614150).sum := by decide
  have hdescent : baseEnd_614150 < baseStart_614150 := by decide
  rcases family_descends (prefixWord ++ tailWord_614150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614153 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 3, 4]
def baseStart_614153 : Nat := 118140960795 + 614153 * 2 ^ 59
def prefixEnd_614153 : Nat := 4983230072969 + 3 ^ 40 * 614153 * 2
def baseEnd_614153 : Nat := 210237122933893904842045

theorem tailTrace_614153 : CollatzResearch.WordTrace tailWord_614153 prefixEnd_614153 210237122933893904842045 := by
  unfold tailWord_614153
  simp only [CollatzResearch.WordTrace]
  refine ⟨22400000144036044826871113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14933333429357363217914075 22400000144036044826871113)
  ·
    refine ⟨16800000108027033620153335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22400000144036044826871113 16800000108027033620153335)
    ·
      refine ⟨25200000162040550430230003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16800000108027033620153335 25200000162040550430230003)
      ·
        refine ⟨37800000243060825645345005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25200000162040550430230003 37800000243060825645345005)
        ·
          refine ⟨14175000091147809617004377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37800000243060825645345005 14175000091147809617004377)
          ·
            refine ⟨10631250068360857212753283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14175000091147809617004377 10631250068360857212753283)
            ·
              refine ⟨15946875102541285819129925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10631250068360857212753283 15946875102541285819129925)
              ·
                refine ⟨2990039081726491091086861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15946875102541285819129925 2990039081726491091086861)
                ·
                  refine ⟨1121264655647434159157573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2990039081726491091086861 1121264655647434159157573)
                  ·
                    refine ⟨210237122933893904842045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1121264655647434159157573 210237122933893904842045)
                    ·
                      rfl

theorem cell22_614153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_614153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614153 prefixEnd_614153 := by exact prefixLift 614153
  have htrace : WordTrace (prefixWord ++ tailWord_614153) baseStart_614153 baseEnd_614153 := by
    simpa [prefixWord, tailWord_614153, baseEnd_614153] using wordTrace_append hprefix tailTrace_614153
  have hstable : (prefixWord ++ tailWord_614153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614153).length < 2 ^ (prefixWord ++ tailWord_614153).sum := by decide
  have hdescent : baseEnd_614153 < baseStart_614153 := by decide
  rcases family_descends (prefixWord ++ tailWord_614153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614168 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 6]
def baseStart_614168 : Nat := 118140960795 + 614168 * 2 ^ 59
def prefixEnd_614168 : Nat := 4983230072969 + 3 ^ 40 * 614168 * 2
def baseEnd_614168 : Nat := 70080752580146288572333

theorem tailTrace_614168 : CollatzResearch.WordTrace tailWord_614168 prefixEnd_614168 70080752580146288572333 := by
  unfold tailWord_614168
  simp only [CollatzResearch.WordTrace]
  refine ⟨11200273619490851194333579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14933698159321134925778105 11200273619490851194333579)
  ·
    refine ⟨16800410429236276791500369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11200273619490851194333579 16800410429236276791500369)
    ·
      refine ⟨12600307821927207593625277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16800410429236276791500369 12600307821927207593625277)
      ·
        refine ⟨4725115433222702847609479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12600307821927207593625277 4725115433222702847609479)
        ·
          refine ⟨7087673149834054271414219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4725115433222702847609479 7087673149834054271414219)
          ·
            refine ⟨10631509724751081407121329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7087673149834054271414219 10631509724751081407121329)
            ·
              refine ⟨7973632293563311055340997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10631509724751081407121329 7973632293563311055340997)
              ·
                refine ⟨1495056055043120822876437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7973632293563311055340997 1495056055043120822876437)
                ·
                  refine ⟨70080752580146288572333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1495056055043120822876437 70080752580146288572333)
                  ·
                    rfl

theorem cell22_614168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_614168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614168 prefixEnd_614168 := by exact prefixLift 614168
  have htrace : WordTrace (prefixWord ++ tailWord_614168) baseStart_614168 baseEnd_614168 := by
    simpa [prefixWord, tailWord_614168, baseEnd_614168] using wordTrace_append hprefix tailTrace_614168
  have hstable : (prefixWord ++ tailWord_614168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614168).length < 2 ^ (prefixWord ++ tailWord_614168).sum := by decide
  have hdescent : baseEnd_614168 < baseStart_614168 := by decide
  rcases family_descends (prefixWord ++ tailWord_614168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614170 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 3, 4]
def baseStart_614170 : Nat := 118140960795 + 614170 * 2 ^ 59
def prefixEnd_614170 : Nat := 4983230072969 + 3 ^ 40 * 614170 * 2
def baseEnd_614170 : Nat := 210242942381311527166993

theorem tailTrace_614170 : CollatzResearch.WordTrace tailWord_614170 prefixEnd_614170 210242942381311527166993 := by
  unfold tailWord_614170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600155046243614182559991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14933746789982971153493309 5600155046243614182559991)
  ·
    refine ⟨8400232569365421273839987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5600155046243614182559991 8400232569365421273839987)
    ·
      refine ⟨12600348854048131910759981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8400232569365421273839987 12600348854048131910759981)
      ·
        refine ⟨4725130820268049466534993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12600348854048131910759981 4725130820268049466534993)
        ·
          refine ⟨3543848115201037099901245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4725130820268049466534993 3543848115201037099901245)
          ·
            refine ⟨1328943043200388912462967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3543848115201037099901245 1328943043200388912462967)
            ·
              refine ⟨1993414564800583368694451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328943043200388912462967 1993414564800583368694451)
              ·
                refine ⟨2990121847200875053041677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1993414564800583368694451 2990121847200875053041677)
                ·
                  refine ⟨1121295692700328144890629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2990121847200875053041677 1121295692700328144890629)
                  ·
                    refine ⟨210242942381311527166993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1121295692700328144890629 210242942381311527166993)
                    ·
                      rfl

theorem cell22_614170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_614170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614170 prefixEnd_614170 := by exact prefixLift 614170
  have htrace : WordTrace (prefixWord ++ tailWord_614170) baseStart_614170 baseEnd_614170 := by
    simpa [prefixWord, tailWord_614170, baseEnd_614170] using wordTrace_append hprefix tailTrace_614170
  have hstable : (prefixWord ++ tailWord_614170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614170).length < 2 ^ (prefixWord ++ tailWord_614170).sum := by decide
  have hdescent : baseEnd_614170 < baseStart_614170 := by decide
  rcases family_descends (prefixWord ++ tailWord_614170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614202 : List Nat := [3, 1, 1, 1, 5, 2, 1, 4, 4]
def baseStart_614202 : Nat := 118140960795 + 614202 * 2 ^ 59
def prefixEnd_614202 : Nat := 4983230072969 + 3 ^ 40 * 614202 * 2
def baseEnd_614202 : Nat := 70084632211758036788965

theorem tailTrace_614202 : CollatzResearch.WordTrace tailWord_614202 prefixEnd_614202 70084632211758036788965 := by
  unfold tailWord_614202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600446830214631548851215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14934524880572350796936573 5600446830214631548851215)
  ·
    refine ⟨8400670245321947323276823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5600446830214631548851215 8400670245321947323276823)
    ·
      refine ⟨12601005367982920984915235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8400670245321947323276823 12601005367982920984915235)
      ·
        refine ⟨18901508051974381477372853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12601005367982920984915235 18901508051974381477372853)
        ·
          refine ⟨1772016379872598263503705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18901508051974381477372853 1772016379872598263503705)
          ·
            refine ⟨1329012284904448697627779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1772016379872598263503705 1329012284904448697627779)
            ·
              refine ⟨1993518427356673046441669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329012284904448697627779 1993518427356673046441669)
              ·
                refine ⟨373784705129376196207813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1993518427356673046441669 373784705129376196207813)
                ·
                  refine ⟨70084632211758036788965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373784705129376196207813 70084632211758036788965)
                  ·
                    rfl

theorem cell22_614202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_614202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614202 prefixEnd_614202 := by exact prefixLift 614202
  have htrace : WordTrace (prefixWord ++ tailWord_614202) baseStart_614202 baseEnd_614202 := by
    simpa [prefixWord, tailWord_614202, baseEnd_614202] using wordTrace_append hprefix tailTrace_614202
  have hstable : (prefixWord ++ tailWord_614202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614202).length < 2 ^ (prefixWord ++ tailWord_614202).sum := by decide
  have hdescent : baseEnd_614202 < baseStart_614202 := by decide
  rcases family_descends (prefixWord ++ tailWord_614202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614245 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 7, 3]
def baseStart_614245 : Nat := 118140960795 + 614245 * 2 ^ 59
def prefixEnd_614245 : Nat := 4983230072969 + 3 ^ 40 * 614245 * 2
def baseEnd_614245 : Nat := 210268616414036331541763

theorem tailTrace_614245 : CollatzResearch.WordTrace tailWord_614245 prefixEnd_614245 210268616414036331541763 := by
  unfold tailWord_614245
  simp only [CollatzResearch.WordTrace]
  refine ⟨22403355659702744539220189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14935570439801829692813459 22403355659702744539220189)
  ·
    refine ⟨8401258372388529202207571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22403355659702744539220189 8401258372388529202207571)
    ·
      refine ⟨12601887558582793803311357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8401258372388529202207571 12601887558582793803311357)
      ·
        refine ⟨4725707834468547676241759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12601887558582793803311357 4725707834468547676241759)
        ·
          refine ⟨7088561751702821514362639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4725707834468547676241759 7088561751702821514362639)
          ·
            refine ⟨10632842627554232271543959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7088561751702821514362639 10632842627554232271543959)
            ·
              refine ⟨15949263941331348407315939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10632842627554232271543959 15949263941331348407315939)
              ·
                refine ⟨23923895911997022610973909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15949263941331348407315939 23923895911997022610973909)
                ·
                  refine ⟨560716310437430217444701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 23923895911997022610973909 560716310437430217444701)
                  ·
                    refine ⟨210268616414036331541763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560716310437430217444701 210268616414036331541763)
                    ·
                      rfl

theorem cell22_614245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_614245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614245 prefixEnd_614245 := by exact prefixLift 614245
  have htrace : WordTrace (prefixWord ++ tailWord_614245) baseStart_614245 baseEnd_614245 := by
    simpa [prefixWord, tailWord_614245, baseEnd_614245] using wordTrace_append hprefix tailTrace_614245
  have hstable : (prefixWord ++ tailWord_614245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614245).length < 2 ^ (prefixWord ++ tailWord_614245).sum := by decide
  have hdescent : baseEnd_614245 < baseStart_614245 := by decide
  rcases family_descends (prefixWord ++ tailWord_614245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614335 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 1, 5]
def baseStart_614335 : Nat := 118140960795 + 614335 * 2 ^ 59
def prefixEnd_614335 : Nat := 4983230072969 + 3 ^ 40 * 614335 * 2
def baseEnd_614335 : Nat := 210299425253306096791487

theorem tailTrace_614335 : CollatzResearch.WordTrace tailWord_614335 prefixEnd_614335 210299425253306096791487 := by
  unfold tailWord_614335
  simp only [CollatzResearch.WordTrace]
  refine ⟨22406638229376689909996459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14937758819584459939997639 22406638229376689909996459)
  ·
    refine ⟨33609957344065034864994689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22406638229376689909996459 33609957344065034864994689)
    ·
      refine ⟨25207468008048776148746017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33609957344065034864994689 25207468008048776148746017)
      ·
        refine ⟨18905601006036582111559513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25207468008048776148746017 18905601006036582111559513)
        ·
          refine ⟨14179200754527436583669635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18905601006036582111559513 14179200754527436583669635)
          ·
            refine ⟨21268801131791154875504453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14179200754527436583669635 21268801131791154875504453)
            ·
              refine ⟨3987900212210841539157085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21268801131791154875504453 3987900212210841539157085)
              ·
                refine ⟨1495462579579065577183907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3987900212210841539157085 1495462579579065577183907)
                ·
                  refine ⟨2243193869368598365775861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1495462579579065577183907 2243193869368598365775861)
                  ·
                    refine ⟨210299425253306096791487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2243193869368598365775861 210299425253306096791487)
                    ·
                      rfl

theorem cell22_614335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_614335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614335 prefixEnd_614335 := by exact prefixLift 614335
  have htrace : WordTrace (prefixWord ++ tailWord_614335) baseStart_614335 baseEnd_614335 := by
    simpa [prefixWord, tailWord_614335, baseEnd_614335] using wordTrace_append hprefix tailTrace_614335
  have hstable : (prefixWord ++ tailWord_614335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614335).length < 2 ^ (prefixWord ++ tailWord_614335).sum := by decide
  have hdescent : baseEnd_614335 < baseStart_614335 := by decide
  rcases family_descends (prefixWord ++ tailWord_614335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614364 : List Nat := [2, 2, 6, 1, 2, 1, 2, 2, 1, 3]
def baseStart_614364 : Nat := 118140960795 + 614364 * 2 ^ 59
def prefixEnd_614364 : Nat := 4983230072969 + 3 ^ 40 * 614364 * 2
def baseEnd_614364 : Nat := 210309352545959687816399

theorem tailTrace_614364 : CollatzResearch.WordTrace tailWord_614364 prefixEnd_614364 210309352545959687816399 := by
  unfold tailWord_614364
  simp only [CollatzResearch.WordTrace]
  refine ⟨11203847973135813931401073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14938463964181085241868097 11203847973135813931401073)
  ·
    refine ⟨8402885979851860448550805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11203847973135813931401073 8402885979851860448550805)
    ·
      refine ⟨393885280305555958525819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8402885979851860448550805 393885280305555958525819)
      ·
        refine ⟨590827920458333937788729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393885280305555958525819 590827920458333937788729)
        ·
          refine ⟨443120940343750453341547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 590827920458333937788729 443120940343750453341547)
          ·
            refine ⟨664681410515625680012321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443120940343750453341547 664681410515625680012321)
            ·
              refine ⟨498511057886719260009241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664681410515625680012321 498511057886719260009241)
              ·
                refine ⟨373883293415039445006931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498511057886719260009241 373883293415039445006931)
                ·
                  refine ⟨560824940122559167510397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373883293415039445006931 560824940122559167510397)
                  ·
                    refine ⟨210309352545959687816399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560824940122559167510397 210309352545959687816399)
                    ·
                      rfl

theorem cell22_614364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_614364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614364 prefixEnd_614364 := by exact prefixLift 614364
  have htrace : WordTrace (prefixWord ++ tailWord_614364) baseStart_614364 baseEnd_614364 := by
    simpa [prefixWord, tailWord_614364, baseEnd_614364] using wordTrace_append hprefix tailTrace_614364
  have hstable : (prefixWord ++ tailWord_614364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614364).length < 2 ^ (prefixWord ++ tailWord_614364).sum := by decide
  have hdescent : baseEnd_614364 < baseStart_614364 := by decide
  rcases family_descends (prefixWord ++ tailWord_614364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614365 : List Nat := [1, 4, 3, 1, 13]
def baseStart_614365 : Nat := 118140960795 + 614365 * 2 ^ 59
def prefixEnd_614365 : Nat := 4983230072969 + 3 ^ 40 * 614365 * 2
def baseEnd_614365 : Nat := 865471995334963039265

theorem tailTrace_614365 : CollatzResearch.WordTrace tailWord_614365 prefixEnd_614365 865471995334963039265 := by
  unfold tailWord_614365
  simp only [CollatzResearch.WordTrace]
  refine ⟨22407732419268005033588549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14938488279512003355725699 22407732419268005033588549)
  ·
    refine ⟨4201449828612750943797853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22407732419268005033588549 4201449828612750943797853)
    ·
      refine ⟨1575543685729781603924195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4201449828612750943797853 1575543685729781603924195)
      ·
        refine ⟨2363315528594672405886293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1575543685729781603924195 2363315528594672405886293)
        ·
          refine ⟨865471995334963039265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 2363315528594672405886293 865471995334963039265)
          ·
            rfl

theorem cell22_614365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 13].length) (baseStart_614365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614365 prefixEnd_614365 := by exact prefixLift 614365
  have htrace : WordTrace (prefixWord ++ tailWord_614365) baseStart_614365 baseEnd_614365 := by
    simpa [prefixWord, tailWord_614365, baseEnd_614365] using wordTrace_append hprefix tailTrace_614365
  have hstable : (prefixWord ++ tailWord_614365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614365).length < 2 ^ (prefixWord ++ tailWord_614365).sum := by decide
  have hdescent : baseEnd_614365 < baseStart_614365 := by decide
  rcases family_descends (prefixWord ++ tailWord_614365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614367 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 2, 4]
def baseStart_614367 : Nat := 118140960795 + 614367 * 2 ^ 59
def prefixEnd_614367 : Nat := 4983230072969 + 3 ^ 40 * 614367 * 2
def baseEnd_614367 : Nat := 210310379507268679991389

theorem tailTrace_614367 : CollatzResearch.WordTrace tailWord_614367 prefixEnd_614367 210310379507268679991389 := by
  unfold tailWord_614367
  simp only [CollatzResearch.WordTrace]
  refine ⟨22407805365260759375161355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14938536910173839583440903 22407805365260759375161355)
  ·
    refine ⟨33611708047891139062742033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22407805365260759375161355 33611708047891139062742033)
    ·
      refine ⟨25208781035918354297056525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33611708047891139062742033 25208781035918354297056525)
      ·
        refine ⟨9453292888469382861396197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25208781035918354297056525 9453292888469382861396197)
        ·
          refine ⟨1772492416588009286511787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9453292888469382861396197 1772492416588009286511787)
          ·
            refine ⟨2658738624882013929767681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772492416588009286511787 2658738624882013929767681)
            ·
              refine ⟨1994053968661510447325761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2658738624882013929767681 1994053968661510447325761)
              ·
                refine ⟨1495540476496132835494321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1994053968661510447325761 1495540476496132835494321)
                ·
                  refine ⟨1121655357372099626620741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1495540476496132835494321 1121655357372099626620741)
                  ·
                    refine ⟨210310379507268679991389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1121655357372099626620741 210310379507268679991389)
                    ·
                      rfl

theorem cell22_614367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_614367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614367 prefixEnd_614367 := by exact prefixLift 614367
  have htrace : WordTrace (prefixWord ++ tailWord_614367) baseStart_614367 baseEnd_614367 := by
    simpa [prefixWord, tailWord_614367, baseEnd_614367] using wordTrace_append hprefix tailTrace_614367
  have hstable : (prefixWord ++ tailWord_614367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614367).length < 2 ^ (prefixWord ++ tailWord_614367).sum := by decide
  have hdescent : baseEnd_614367 < baseStart_614367 := by decide
  rcases family_descends (prefixWord ++ tailWord_614367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614371 : List Nat := [1, 1, 1, 6, 1, 4, 2, 2, 4]
def baseStart_614371 : Nat := 118140960795 + 614371 * 2 ^ 59
def prefixEnd_614371 : Nat := 4983230072969 + 3 ^ 40 * 614371 * 2
def baseEnd_614371 : Nat := 70103916263004667630459

theorem tailTrace_614371 : CollatzResearch.WordTrace tailWord_614371 prefixEnd_614371 70103916263004667630459 := by
  unfold tailWord_614371
  simp only [CollatzResearch.WordTrace]
  refine ⟨22407951257246268058306967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14938634171497512038871311 22407951257246268058306967)
  ·
    refine ⟨33611926885869402087460451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22407951257246268058306967 33611926885869402087460451)
    ·
      refine ⟨50417890328804103131190677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33611926885869402087460451 50417890328804103131190677)
      ·
        refine ⟨2363338609162692334274563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50417890328804103131190677 2363338609162692334274563)
        ·
          refine ⟨3545007913744038501411845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2363338609162692334274563 3545007913744038501411845)
          ·
            refine ⟨664688983827007219014721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3545007913744038501411845 664688983827007219014721)
            ·
              refine ⟨498516737870255414261041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664688983827007219014721 498516737870255414261041)
              ·
                refine ⟨373887553402691560695781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498516737870255414261041 373887553402691560695781)
                ·
                  refine ⟨70103916263004667630459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373887553402691560695781 70103916263004667630459)
                  ·
                    rfl

theorem cell22_614371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 4].length) (baseStart_614371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614371 prefixEnd_614371 := by exact prefixLift 614371
  have htrace : WordTrace (prefixWord ++ tailWord_614371) baseStart_614371 baseEnd_614371 := by
    simpa [prefixWord, tailWord_614371, baseEnd_614371] using wordTrace_append hprefix tailTrace_614371
  have hstable : (prefixWord ++ tailWord_614371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614371).length < 2 ^ (prefixWord ++ tailWord_614371).sum := by decide
  have hdescent : baseEnd_614371 < baseStart_614371 := by decide
  rcases family_descends (prefixWord ++ tailWord_614371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614382 : List Nat := [4, 1, 2, 1, 3, 1, 3, 7]
def baseStart_614382 : Nat := 118140960795 + 614382 * 2 ^ 59
def prefixEnd_614382 : Nat := 4983230072969 + 3 ^ 40 * 614382 * 2
def baseEnd_614382 : Nat := 23368390479312626762927

theorem tailTrace_614382 : CollatzResearch.WordTrace tailWord_614382 prefixEnd_614382 23368390479312626762927 := by
  unfold tailWord_614382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2801044057525802117119675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14938901640137611291304933 2801044057525802117119675)
  ·
    refine ⟨4201566086288703175679513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2801044057525802117119675 4201566086288703175679513)
    ·
      refine ⟨3151174564716527381759635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4201566086288703175679513 3151174564716527381759635)
      ·
        refine ⟨4726761847074791072639453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3151174564716527381759635 4726761847074791072639453)
        ·
          refine ⟨1772535692653046652239795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4726761847074791072639453 1772535692653046652239795)
          ·
            refine ⟨2658803538979569978359693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1772535692653046652239795 2658803538979569978359693)
            ·
              refine ⟨997051327117338741884885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2658803538979569978359693 997051327117338741884885)
              ·
                refine ⟨23368390479312626762927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 997051327117338741884885 23368390479312626762927)
                ·
                  rfl

theorem cell22_614382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_614382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614382 prefixEnd_614382 := by exact prefixLift 614382
  have htrace : WordTrace (prefixWord ++ tailWord_614382) baseStart_614382 baseEnd_614382 := by
    simpa [prefixWord, tailWord_614382, baseEnd_614382] using wordTrace_append hprefix tailTrace_614382
  have hstable : (prefixWord ++ tailWord_614382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614382).length < 2 ^ (prefixWord ++ tailWord_614382).sum := by decide
  have hdescent : baseEnd_614382 < baseStart_614382 := by decide
  rcases family_descends (prefixWord ++ tailWord_614382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614397 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_614397 : Nat := 118140960795 + 614397 * 2 ^ 59
def prefixEnd_614397 : Nat := 4983230072969 + 3 ^ 40 * 614397 * 2
def baseEnd_614397 : Nat := 210320649120358601741297

theorem tailTrace_614397 : CollatzResearch.WordTrace tailWord_614397 prefixEnd_614397 210320649120358601741297 := by
  unfold tailWord_614397
  simp only [CollatzResearch.WordTrace]
  refine ⟨22408899555152074498753445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14939266370101382999168963 22408899555152074498753445)
  ·
    refine ⟨4201668666591013968516271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22408899555152074498753445 4201668666591013968516271)
    ·
      refine ⟨6302502999886520952774407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4201668666591013968516271 6302502999886520952774407)
      ·
        refine ⟨9453754499829781429161611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6302502999886520952774407 9453754499829781429161611)
        ·
          refine ⟨14180631749744672143742417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9453754499829781429161611 14180631749744672143742417)
          ·
            refine ⟨10635473812308504107806813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14180631749744672143742417 10635473812308504107806813)
            ·
              refine ⟨3988302679615689040427555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10635473812308504107806813 3988302679615689040427555)
              ·
                refine ⟨5982454019423533560641333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3988302679615689040427555 5982454019423533560641333)
                ·
                  refine ⟨560855064320956271310125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5982454019423533560641333 560855064320956271310125)
                  ·
                    refine ⟨210320649120358601741297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560855064320956271310125 210320649120358601741297)
                    ·
                      rfl

theorem cell22_614397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_614397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614397 prefixEnd_614397 := by exact prefixLift 614397
  have htrace : WordTrace (prefixWord ++ tailWord_614397) baseStart_614397 baseEnd_614397 := by
    simpa [prefixWord, tailWord_614397, baseEnd_614397] using wordTrace_append hprefix tailTrace_614397
  have hstable : (prefixWord ++ tailWord_614397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614397).length < 2 ^ (prefixWord ++ tailWord_614397).sum := by decide
  have hdescent : baseEnd_614397 < baseStart_614397 := by decide
  rcases family_descends (prefixWord ++ tailWord_614397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614420 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_614420 : Nat := 118140960795 + 614420 * 2 ^ 59
def prefixEnd_614420 : Nat := 4983230072969 + 3 ^ 40 * 614420 * 2
def baseEnd_614420 : Nat := 210328522490394208416227

theorem tailTrace_614420 : CollatzResearch.WordTrace tailWord_614420 prefixEnd_614420 210328522490394208416227 := by
  unfold tailWord_614420
  simp only [CollatzResearch.WordTrace]
  refine ⟨11204869217034374713420357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14939825622712499617893809 11204869217034374713420357)
  ·
    refine ⟨2100912978193945258766317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11204869217034374713420357 2100912978193945258766317)
    ·
      refine ⟨787842366822729472037369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2100912978193945258766317 787842366822729472037369)
      ·
        refine ⟨590881775117047104028027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 787842366822729472037369 590881775117047104028027)
        ·
          refine ⟨886322662675570656042041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590881775117047104028027 886322662675570656042041)
          ·
            refine ⟨664741997006677992031531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886322662675570656042041 664741997006677992031531)
            ·
              refine ⟨997112995510016988047297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664741997006677992031531 997112995510016988047297)
              ·
                refine ⟨747834746632512741035473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997112995510016988047297 747834746632512741035473)
                ·
                  refine ⟨560876059974384555776605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 747834746632512741035473 560876059974384555776605)
                  ·
                    refine ⟨210328522490394208416227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560876059974384555776605 210328522490394208416227)
                    ·
                      rfl

theorem cell22_614420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_614420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614420 prefixEnd_614420 := by exact prefixLift 614420
  have htrace : WordTrace (prefixWord ++ tailWord_614420) baseStart_614420 baseEnd_614420 := by
    simpa [prefixWord, tailWord_614420, baseEnd_614420] using wordTrace_append hprefix tailTrace_614420
  have hstable : (prefixWord ++ tailWord_614420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614420).length < 2 ^ (prefixWord ++ tailWord_614420).sum := by decide
  have hdescent : baseEnd_614420 < baseStart_614420 := by decide
  rcases family_descends (prefixWord ++ tailWord_614420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614519 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 2, 4]
def baseStart_614519 : Nat := 118140960795 + 614519 * 2 ^ 59
def prefixEnd_614519 : Nat := 4983230072969 + 3 ^ 40 * 614519 * 2
def baseEnd_614519 : Nat := 210362412213590950190923

theorem tailTrace_614519 : CollatzResearch.WordTrace tailWord_614519 prefixEnd_614519 210362412213590950190923 := by
  unfold tailWord_614519
  simp only [CollatzResearch.WordTrace]
  refine ⟨22413349260710089334694611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14942232840473392889796407 22413349260710089334694611)
  ·
    refine ⟨33620023891065134002041917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22413349260710089334694611 33620023891065134002041917)
    ·
      refine ⟨12607508959149425250765719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33620023891065134002041917 12607508959149425250765719)
      ·
        refine ⟨18911263438724137876148579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12607508959149425250765719 18911263438724137876148579)
        ·
          refine ⟨28366895158086206814222869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18911263438724137876148579 28366895158086206814222869)
          ·
            refine ⟨1329698210535290944416697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28366895158086206814222869 1329698210535290944416697)
            ·
              refine ⟨997273657901468208312523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1329698210535290944416697 997273657901468208312523)
              ·
                refine ⟨1495910486852202312468785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997273657901468208312523 1495910486852202312468785)
                ·
                  refine ⟨1121932865139151734351589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1495910486852202312468785 1121932865139151734351589)
                  ·
                    refine ⟨210362412213590950190923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1121932865139151734351589 210362412213590950190923)
                    ·
                      rfl

theorem cell22_614519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_614519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614519 prefixEnd_614519 := by exact prefixLift 614519
  have htrace : WordTrace (prefixWord ++ tailWord_614519) baseStart_614519 baseEnd_614519 := by
    simpa [prefixWord, tailWord_614519, baseEnd_614519] using wordTrace_append hprefix tailTrace_614519
  have hstable : (prefixWord ++ tailWord_614519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614519).length < 2 ^ (prefixWord ++ tailWord_614519).sum := by decide
  have hdescent : baseEnd_614519 < baseStart_614519 := by decide
  rcases family_descends (prefixWord ++ tailWord_614519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614549 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 3, 3]
def baseStart_614549 : Nat := 118140960795 + 614549 * 2 ^ 59
def prefixEnd_614549 : Nat := 4983230072969 + 3 ^ 40 * 614549 * 2
def baseEnd_614549 : Nat := 210372681826680871940831

theorem tailTrace_614549 : CollatzResearch.WordTrace tailWord_614549 prefixEnd_614549 210372681826680871940831 := by
  unfold tailWord_614549
  simp only [CollatzResearch.WordTrace]
  refine ⟨22414443450601404458286701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14942962300400936305524467 22414443450601404458286701)
  ·
    refine ⟨8405416293975526671857513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22414443450601404458286701 8405416293975526671857513)
    ·
      refine ⟨6304062220481645003893135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8405416293975526671857513 6304062220481645003893135)
      ·
        refine ⟨9456093330722467505839703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6304062220481645003893135 9456093330722467505839703)
        ·
          refine ⟨14184139996083701258759555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9456093330722467505839703 14184139996083701258759555)
          ·
            refine ⟨21276209994125551888139333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14184139996083701258759555 21276209994125551888139333)
            ·
              refine ⟨3989289373898540979026125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21276209994125551888139333 3989289373898540979026125)
              ·
                refine ⟨1495983515211952867134797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3989289373898540979026125 1495983515211952867134797)
                ·
                  refine ⟨560993818204482325175549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1495983515211952867134797 560993818204482325175549)
                  ·
                    refine ⟨210372681826680871940831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 560993818204482325175549 210372681826680871940831)
                    ·
                      rfl

theorem cell22_614549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_614549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614549 prefixEnd_614549 := by exact prefixLift 614549
  have htrace : WordTrace (prefixWord ++ tailWord_614549) baseStart_614549 baseEnd_614549 := by
    simpa [prefixWord, tailWord_614549, baseEnd_614549] using wordTrace_append hprefix tailTrace_614549
  have hstable : (prefixWord ++ tailWord_614549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614549).length < 2 ^ (prefixWord ++ tailWord_614549).sum := by decide
  have hdescent : baseEnd_614549 < baseStart_614549 := by decide
  rcases family_descends (prefixWord ++ tailWord_614549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614551 : List Nat := [1, 1, 3, 3, 5, 1, 1, 7]
def baseStart_614551 : Nat := 118140960795 + 614551 * 2 ^ 59
def prefixEnd_614551 : Nat := 4983230072969 + 3 ^ 40 * 614551 * 2
def baseEnd_614551 : Nat := 23374818496394837043425

theorem tailTrace_614551 : CollatzResearch.WordTrace tailWord_614551 prefixEnd_614551 23374818496394837043425 := by
  unfold tailWord_614551
  simp only [CollatzResearch.WordTrace]
  refine ⟨22414516396594158799859507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14943010931062772533239671 22414516396594158799859507)
  ·
    refine ⟨33621774594891238199789261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22414516396594158799859507 33621774594891238199789261)
    ·
      refine ⟨12608165473084214324920973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33621774594891238199789261 12608165473084214324920973)
      ·
        refine ⟨4728062052406580371845365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12608165473084214324920973 4728062052406580371845365)
        ·
          refine ⟨443255817413116909860503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4728062052406580371845365 443255817413116909860503)
          ·
            refine ⟨664883726119675364790755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443255817413116909860503 664883726119675364790755)
            ·
              refine ⟨997325589179513047186133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664883726119675364790755 997325589179513047186133)
              ·
                refine ⟨23374818496394837043425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 997325589179513047186133 23374818496394837043425)
                ·
                  rfl

theorem cell22_614551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 7].length) (baseStart_614551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614551 prefixEnd_614551 := by exact prefixLift 614551
  have htrace : WordTrace (prefixWord ++ tailWord_614551) baseStart_614551 baseEnd_614551 := by
    simpa [prefixWord, tailWord_614551, baseEnd_614551] using wordTrace_append hprefix tailTrace_614551
  have hstable : (prefixWord ++ tailWord_614551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614551).length < 2 ^ (prefixWord ++ tailWord_614551).sum := by decide
  have hdescent : baseEnd_614551 < baseStart_614551 := by decide
  rcases family_descends (prefixWord ++ tailWord_614551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614570 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 2, 4]
def baseStart_614570 : Nat := 118140960795 + 614570 * 2 ^ 59
def prefixEnd_614570 : Nat := 4983230072969 + 3 ^ 40 * 614570 * 2
def baseEnd_614570 : Nat := 210379870555843817165767

theorem tailTrace_614570 : CollatzResearch.WordTrace tailWord_614570 prefixEnd_614570 210379870555843817165767 := by
  unfold tailWord_614570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5603802345881331261200291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14943472922350216696534109 5603802345881331261200291)
  ·
    refine ⟨8405703518821996891800437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5603802345881331261200291 8405703518821996891800437)
    ·
      refine ⟨788034704889562208606291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8405703518821996891800437 788034704889562208606291)
      ·
        refine ⟨1182052057334343312909437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788034704889562208606291 1182052057334343312909437)
        ·
          refine ⟨443269521500378742341039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1182052057334343312909437 443269521500378742341039)
          ·
            refine ⟨664904282250568113511559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443269521500378742341039 664904282250568113511559)
            ·
              refine ⟨997356423375852170267339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664904282250568113511559 997356423375852170267339)
              ·
                refine ⟨1496034635063778255401009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997356423375852170267339 1496034635063778255401009)
                ·
                  refine ⟨1122025976297833691550757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1496034635063778255401009 1122025976297833691550757)
                  ·
                    refine ⟨210379870555843817165767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1122025976297833691550757 210379870555843817165767)
                    ·
                      rfl

theorem cell22_614570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_614570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614570 prefixEnd_614570 := by exact prefixLift 614570
  have htrace : WordTrace (prefixWord ++ tailWord_614570) baseStart_614570 baseEnd_614570 := by
    simpa [prefixWord, tailWord_614570, baseEnd_614570] using wordTrace_append hprefix tailTrace_614570
  have hstable : (prefixWord ++ tailWord_614570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614570).length < 2 ^ (prefixWord ++ tailWord_614570).sum := by decide
  have hdescent : baseEnd_614570 < baseStart_614570 := by decide
  rcases family_descends (prefixWord ++ tailWord_614570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614583 : List Nat := [1, 1, 3, 1, 4, 3, 2, 3, 1, 3]
def baseStart_614583 : Nat := 118140960795 + 614583 * 2 ^ 59
def prefixEnd_614583 : Nat := 4983230072969 + 3 ^ 40 * 614583 * 2
def baseEnd_614583 : Nat := 210384320721516116590727

theorem tailTrace_614583 : CollatzResearch.WordTrace tailWord_614583 prefixEnd_614583 210384320721516116590727 := by
  unfold tailWord_614583
  simp only [CollatzResearch.WordTrace]
  refine ⟨22415683532478228265024403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14943789021652152176682935 22415683532478228265024403)
  ·
    refine ⟨33623525298717342397536605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22415683532478228265024403 33623525298717342397536605)
    ·
      refine ⟨12608821987019003399076227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33623525298717342397536605 12608821987019003399076227)
      ·
        refine ⟨18913232980528505098614341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12608821987019003399076227 18913232980528505098614341)
        ·
          refine ⟨3546231183849094705990189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18913232980528505098614341 3546231183849094705990189)
          ·
            refine ⟨1329836693943410514746321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3546231183849094705990189 1329836693943410514746321)
            ·
              refine ⟨997377520457557886059741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1329836693943410514746321 997377520457557886059741)
              ·
                refine ⟨374016570171584207272403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 997377520457557886059741 374016570171584207272403)
                ·
                  refine ⟨561024855257376310908605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374016570171584207272403 561024855257376310908605)
                  ·
                    refine ⟨210384320721516116590727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 561024855257376310908605 210384320721516116590727)
                    ·
                      rfl

theorem cell22_614583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_614583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614583 prefixEnd_614583 := by exact prefixLift 614583
  have htrace : WordTrace (prefixWord ++ tailWord_614583) baseStart_614583 baseEnd_614583 := by
    simpa [prefixWord, tailWord_614583, baseEnd_614583] using wordTrace_append hprefix tailTrace_614583
  have hstable : (prefixWord ++ tailWord_614583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614583).length < 2 ^ (prefixWord ++ tailWord_614583).sum := by decide
  have hdescent : baseEnd_614583 < baseStart_614583 := by decide
  rcases family_descends (prefixWord ++ tailWord_614583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614596 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 5]
def baseStart_614596 : Nat := 118140960795 + 614596 * 2 ^ 59
def prefixEnd_614596 : Nat := 4983230072969 + 3 ^ 40 * 614596 * 2
def baseEnd_614596 : Nat := 70129590295729472005229

theorem tailTrace_614596 : CollatzResearch.WordTrace tailWord_614596 prefixEnd_614596 70129590295729472005229 := by
  unfold tailWord_614596
  simp only [CollatzResearch.WordTrace]
  refine ⟨11208078840715565742623821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14944105120954087656831761 11208078840715565742623821)
  ·
    refine ⟨4203029565268337153483933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11208078840715565742623821 4203029565268337153483933)
    ·
      refine ⟨1576136086975626432556475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4203029565268337153483933 1576136086975626432556475)
      ·
        refine ⟨2364204130463439648834713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1576136086975626432556475 2364204130463439648834713)
        ·
          refine ⟨1773153097847579736626035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2364204130463439648834713 1773153097847579736626035)
          ·
            refine ⟨2659729646771369604939053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1773153097847579736626035 2659729646771369604939053)
            ·
              refine ⟨997398617539263601852145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2659729646771369604939053 997398617539263601852145)
              ·
                refine ⟨748048963154447701389109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997398617539263601852145 748048963154447701389109)
                ·
                  refine ⟨70129590295729472005229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 748048963154447701389109 70129590295729472005229)
                  ·
                    rfl

theorem cell22_614596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_614596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614596 prefixEnd_614596 := by exact prefixLift 614596
  have htrace : WordTrace (prefixWord ++ tailWord_614596) baseStart_614596 baseEnd_614596 := by
    simpa [prefixWord, tailWord_614596, baseEnd_614596] using wordTrace_append hprefix tailTrace_614596
  have hstable : (prefixWord ++ tailWord_614596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614596).length < 2 ^ (prefixWord ++ tailWord_614596).sum := by decide
  have hdescent : baseEnd_614596 < baseStart_614596 := by decide
  rcases family_descends (prefixWord ++ tailWord_614596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614613 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 5]
def baseStart_614613 : Nat := 118140960795 + 614613 * 2 ^ 59
def prefixEnd_614613 : Nat := 4983230072969 + 3 ^ 40 * 614613 * 2
def baseEnd_614613 : Nat := 70131530111535346113545

theorem tailTrace_614613 : CollatzResearch.WordTrace tailWord_614613 prefixEnd_614613 70131530111535346113545 := by
  unfold tailWord_614613
  simp only [CollatzResearch.WordTrace]
  refine ⟨22416777722369543388616493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14944518481579695592410995 22416777722369543388616493)
  ·
    refine ⟨8406291645888578770731185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22416777722369543388616493 8406291645888578770731185)
    ·
      refine ⟨6304718734416434078048389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8406291645888578770731185 6304718734416434078048389)
      ·
        refine ⟨1182134762703081389634073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6304718734416434078048389 1182134762703081389634073)
        ·
          refine ⟨886601072027311042225555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1182134762703081389634073 886601072027311042225555)
          ·
            refine ⟨1329901608040966563338333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886601072027311042225555 1329901608040966563338333)
            ·
              refine ⟨498713103015362461251875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1329901608040966563338333 498713103015362461251875)
              ·
                refine ⟨748069654523043691877813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498713103015362461251875 748069654523043691877813)
                ·
                  refine ⟨70131530111535346113545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 748069654523043691877813 70131530111535346113545)
                  ·
                    rfl

theorem cell22_614613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_614613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614613 prefixEnd_614613 := by exact prefixLift 614613
  have htrace : WordTrace (prefixWord ++ tailWord_614613) baseStart_614613 baseEnd_614613 := by
    simpa [prefixWord, tailWord_614613, baseEnd_614613] using wordTrace_append hprefix tailTrace_614613
  have hstable : (prefixWord ++ tailWord_614613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614613).length < 2 ^ (prefixWord ++ tailWord_614613).sum := by decide
  have hdescent : baseEnd_614613 < baseStart_614613 := by decide
  rcases family_descends (prefixWord ++ tailWord_614613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614641 : List Nat := [1, 2, 2, 2, 2, 1, 5, 3, 4]
def baseStart_614641 : Nat := 118140960795 + 614641 * 2 ^ 59
def prefixEnd_614641 : Nat := 4983230072969 + 3 ^ 40 * 614641 * 2
def baseEnd_614641 : Nat := 70134725102274432880183

theorem tailTrace_614641 : CollatzResearch.WordTrace tailWord_614641 prefixEnd_614641 70134725102274432880183 := by
  unfold tailWord_614641
  simp only [CollatzResearch.WordTrace]
  refine ⟨22417798966268104170635777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14945199310845402780423851 22417798966268104170635777)
  ·
    refine ⟨16813349224701078127976833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22417798966268104170635777 16813349224701078127976833)
    ·
      refine ⟨12610011918525808595982625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16813349224701078127976833 12610011918525808595982625)
      ·
        refine ⟨9457508938894356446986969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12610011918525808595982625 9457508938894356446986969)
        ·
          refine ⟨7093131704170767335240227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9457508938894356446986969 7093131704170767335240227)
          ·
            refine ⟨10639697556256151002860341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7093131704170767335240227 10639697556256151002860341)
            ·
              refine ⟨997471645899014156518157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10639697556256151002860341 997471645899014156518157)
              ·
                refine ⟨374051867212130308694309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 997471645899014156518157 374051867212130308694309)
                ·
                  refine ⟨70134725102274432880183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374051867212130308694309 70134725102274432880183)
                  ·
                    rfl

theorem cell22_614641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 4].length) (baseStart_614641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614641 prefixEnd_614641 := by exact prefixLift 614641
  have htrace : WordTrace (prefixWord ++ tailWord_614641) baseStart_614641 baseEnd_614641 := by
    simpa [prefixWord, tailWord_614641, baseEnd_614641] using wordTrace_append hprefix tailTrace_614641
  have hstable : (prefixWord ++ tailWord_614641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614641).length < 2 ^ (prefixWord ++ tailWord_614641).sum := by decide
  have hdescent : baseEnd_614641 < baseStart_614641 := by decide
  rcases family_descends (prefixWord ++ tailWord_614641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614658 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 6]
def baseStart_614658 : Nat := 118140960795 + 614658 * 2 ^ 59
def prefixEnd_614658 : Nat := 4983230072969 + 3 ^ 40 * 614658 * 2
def baseEnd_614658 : Nat := 70136664918080306988499

theorem tailTrace_614658 : CollatzResearch.WordTrace tailWord_614658 prefixEnd_614658 70136664918080306988499 := by
  unfold tailWord_614658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5604604751801629018501157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14945612671471010716003085 5604604751801629018501157)
  ·
    refine ⟨1050863390962805440968967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5604604751801629018501157 1050863390962805440968967)
    ·
      refine ⟨1576295086444208161453451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1050863390962805440968967 1576295086444208161453451)
      ·
        refine ⟨2364442629666312242180177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1576295086444208161453451 2364442629666312242180177)
        ·
          refine ⟨1773331972249734181635133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2364442629666312242180177 1773331972249734181635133)
          ·
            refine ⟨664999489593650318113175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1773331972249734181635133 664999489593650318113175)
            ·
              refine ⟨997499234390475477169763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664999489593650318113175 997499234390475477169763)
              ·
                refine ⟨1496248851585713215754645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997499234390475477169763 1496248851585713215754645)
                ·
                  refine ⟨70136664918080306988499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1496248851585713215754645 70136664918080306988499)
                  ·
                    rfl

theorem cell22_614658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_614658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614658 prefixEnd_614658 := by exact prefixLift 614658
  have htrace : WordTrace (prefixWord ++ tailWord_614658) baseStart_614658 baseEnd_614658 := by
    simpa [prefixWord, tailWord_614658, baseEnd_614658] using wordTrace_append hprefix tailTrace_614658
  have hstable : (prefixWord ++ tailWord_614658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614658).length < 2 ^ (prefixWord ++ tailWord_614658).sum := by decide
  have hdescent : baseEnd_614658 < baseStart_614658 := by decide
  rcases family_descends (prefixWord ++ tailWord_614658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614673 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 2, 3]
def baseStart_614673 : Nat := 118140960795 + 614673 * 2 ^ 59
def prefixEnd_614673 : Nat := 4983230072969 + 3 ^ 40 * 614673 * 2
def baseEnd_614673 : Nat := 210415129560785881840451

theorem tailTrace_614673 : CollatzResearch.WordTrace tailWord_614673 prefixEnd_614673 210415129560785881840451 := by
  unfold tailWord_614673
  simp only [CollatzResearch.WordTrace]
  refine ⟨22418966102152173635800673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14945977401434782423867115 22418966102152173635800673)
  ·
    refine ⟨16814224576614130226850505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22418966102152173635800673 16814224576614130226850505)
    ·
      refine ⟨12610668432460597670137879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16814224576614130226850505 12610668432460597670137879)
      ·
        refine ⟨18916002648690896505206819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12610668432460597670137879 18916002648690896505206819)
        ·
          refine ⟨28374003973036344757810229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18916002648690896505206819 28374003973036344757810229)
          ·
            refine ⟨2660062872472157321044709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28374003973036344757810229 2660062872472157321044709)
            ·
              refine ⟨498761788588529497695883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2660062872472157321044709 498761788588529497695883)
              ·
                refine ⟨748142682882794246543825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498761788588529497695883 748142682882794246543825)
                ·
                  refine ⟨561107012162095684907869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 748142682882794246543825 561107012162095684907869)
                  ·
                    refine ⟨210415129560785881840451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 561107012162095684907869 210415129560785881840451)
                    ·
                      rfl

theorem cell22_614673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_614673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614673 prefixEnd_614673 := by exact prefixLift 614673
  have htrace : WordTrace (prefixWord ++ tailWord_614673) baseStart_614673 baseEnd_614673 := by
    simpa [prefixWord, tailWord_614673, baseEnd_614673] using wordTrace_append hprefix tailTrace_614673
  have hstable : (prefixWord ++ tailWord_614673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614673).length < 2 ^ (prefixWord ++ tailWord_614673).sum := by decide
  have hdescent : baseEnd_614673 < baseStart_614673 := by decide
  rcases family_descends (prefixWord ++ tailWord_614673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614761 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 1, 4]
def baseStart_614761 : Nat := 118140960795 + 614761 * 2 ^ 59
def prefixEnd_614761 : Nat := 4983230072969 + 3 ^ 40 * 614761 * 2
def baseEnd_614761 : Nat := 210445253759182985640181

theorem tailTrace_614761 : CollatzResearch.WordTrace tailWord_614761 prefixEnd_614761 210445253759182985640181 := by
  unfold tailWord_614761
  simp only [CollatzResearch.WordTrace]
  refine ⟨22422175725833364665004137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14948117150555576443336091 22422175725833364665004137)
  ·
    refine ⟨16816631794375023498753103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22422175725833364665004137 16816631794375023498753103)
    ·
      refine ⟨25224947691562535248129655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16816631794375023498753103 25224947691562535248129655)
      ·
        refine ⟨37837421537343802872194483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25224947691562535248129655 37837421537343802872194483)
        ·
          refine ⟨56756132306015704308291725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37837421537343802872194483 56756132306015704308291725)
          ·
            refine ⟨21283549614755889115609397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56756132306015704308291725 21283549614755889115609397)
            ·
              refine ⟨1995332776383364604588381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21283549614755889115609397 1995332776383364604588381)
              ·
                refine ⟨748249791143761726720643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1995332776383364604588381 748249791143761726720643)
                ·
                  refine ⟨1122374686715642590080965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748249791143761726720643 1122374686715642590080965)
                  ·
                    refine ⟨210445253759182985640181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1122374686715642590080965 210445253759182985640181)
                    ·
                      rfl

theorem cell22_614761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_614761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614761 prefixEnd_614761 := by exact prefixLift 614761
  have htrace : WordTrace (prefixWord ++ tailWord_614761) baseStart_614761 baseEnd_614761 := by
    simpa [prefixWord, tailWord_614761, baseEnd_614761] using wordTrace_append hprefix tailTrace_614761
  have hstable : (prefixWord ++ tailWord_614761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614761).length < 2 ^ (prefixWord ++ tailWord_614761).sum := by decide
  have hdescent : baseEnd_614761 < baseStart_614761 := by decide
  rcases family_descends (prefixWord ++ tailWord_614761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614808 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 4, 3]
def baseStart_614808 : Nat := 118140960795 + 614808 * 2 ^ 59
def prefixEnd_614808 : Nat := 4983230072969 + 3 ^ 40 * 614808 * 2
def baseEnd_614808 : Nat := 210461342819690529715037

theorem tailTrace_614808 : CollatzResearch.WordTrace tailWord_614808 prefixEnd_614808 210461342819690529715037 := by
  unfold tailWord_614808
  simp only [CollatzResearch.WordTrace]
  refine ⟨11211944978331545845982539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14949259971108727794643385 11211944978331545845982539)
  ·
    refine ⟨16817917467497318768973809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11211944978331545845982539 16817917467497318768973809)
    ·
      refine ⟨12613438100622989076730357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16817917467497318768973809 12613438100622989076730357)
      ·
        refine ⟨1182509821933405225943471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12613438100622989076730357 1182509821933405225943471)
        ·
          refine ⟨1773764732900107838915207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182509821933405225943471 1773764732900107838915207)
          ·
            refine ⟨2660647099350161758372811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1773764732900107838915207 2660647099350161758372811)
            ·
              refine ⟨3990970649025242637559217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2660647099350161758372811 3990970649025242637559217)
              ·
                refine ⟨2993227986768931978169413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3990970649025242637559217 2993227986768931978169413)
                ·
                  refine ⟨561230247519174745906765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2993227986768931978169413 561230247519174745906765)
                  ·
                    refine ⟨210461342819690529715037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 561230247519174745906765 210461342819690529715037)
                    ·
                      rfl

theorem cell22_614808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_614808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614808 prefixEnd_614808 := by exact prefixLift 614808
  have htrace : WordTrace (prefixWord ++ tailWord_614808) baseStart_614808 baseEnd_614808 := by
    simpa [prefixWord, tailWord_614808, baseEnd_614808] using wordTrace_append hprefix tailTrace_614808
  have hstable : (prefixWord ++ tailWord_614808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614808).length < 2 ^ (prefixWord ++ tailWord_614808).sum := by decide
  have hdescent : baseEnd_614808 < baseStart_614808 := by decide
  rcases family_descends (prefixWord ++ tailWord_614808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614810 : List Nat := [3, 1, 1, 4, 1, 4, 1, 3, 4]
def baseStart_614810 : Nat := 118140960795 + 614810 * 2 ^ 59
def prefixEnd_614810 : Nat := 4983230072969 + 3 ^ 40 * 614810 * 2
def baseEnd_614810 : Nat := 70154009153521063721677

theorem tailTrace_614810 : CollatzResearch.WordTrace tailWord_614810 prefixEnd_614810 70154009153521063721677 := by
  unfold tailWord_614810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5605990725663961508384471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14949308601770564022358589 5605990725663961508384471)
  ·
    refine ⟨8408986088495942262576707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5605990725663961508384471 8408986088495942262576707)
    ·
      refine ⟨12613479132743913393865061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8408986088495942262576707 12613479132743913393865061)
      ·
        refine ⟨2365027337389483761349699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12613479132743913393865061 2365027337389483761349699)
        ·
          refine ⟨3547541006084225642024549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365027337389483761349699 3547541006084225642024549)
          ·
            refine ⟨665163938640792307879603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3547541006084225642024549 665163938640792307879603)
            ·
              refine ⟨997745907961188461819405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665163938640792307879603 997745907961188461819405)
              ·
                refine ⟨374154715485445673182277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 997745907961188461819405 374154715485445673182277)
                ·
                  refine ⟨70154009153521063721677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374154715485445673182277 70154009153521063721677)
                  ·
                    rfl

theorem cell22_614810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_614810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614810 prefixEnd_614810 := by exact prefixLift 614810
  have htrace : WordTrace (prefixWord ++ tailWord_614810) baseStart_614810 baseEnd_614810 := by
    simpa [prefixWord, tailWord_614810, baseEnd_614810] using wordTrace_append hprefix tailTrace_614810
  have hstable : (prefixWord ++ tailWord_614810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614810).length < 2 ^ (prefixWord ++ tailWord_614810).sum := by decide
  have hdescent : baseEnd_614810 < baseStart_614810 := by decide
  rcases family_descends (prefixWord ++ tailWord_614810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614823 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 2, 4]
def baseStart_614823 : Nat := 118140960795 + 614823 * 2 ^ 59
def prefixEnd_614823 : Nat := 4983230072969 + 3 ^ 40 * 614823 * 2
def baseEnd_614823 : Nat := 210466477626235490589991

theorem tailTrace_614823 : CollatzResearch.WordTrace tailWord_614823 prefixEnd_614823 210466477626235490589991 := by
  unfold tailWord_614823
  simp only [CollatzResearch.WordTrace]
  refine ⟨22424437051608749253761123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14949624701072499502507415 22424437051608749253761123)
  ·
    refine ⟨33636655577413123880641685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22424437051608749253761123 33636655577413123880641685)
    ·
      refine ⟨1576718230191240181905079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33636655577413123880641685 1576718230191240181905079)
      ·
        refine ⟨2365077345286860272857619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1576718230191240181905079 2365077345286860272857619)
        ·
          refine ⟨3547616017930290409286429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2365077345286860272857619 3547616017930290409286429)
          ·
            refine ⟨1330356006723858903482411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3547616017930290409286429 1330356006723858903482411)
            ·
              refine ⟨1995534010085788355223617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330356006723858903482411 1995534010085788355223617)
              ·
                refine ⟨1496650507564341266417713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995534010085788355223617 1496650507564341266417713)
                ·
                  refine ⟨1122487880673255949813285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1496650507564341266417713 1122487880673255949813285)
                  ·
                    refine ⟨210466477626235490589991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1122487880673255949813285 210466477626235490589991)
                    ·
                      rfl

theorem cell22_614823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_614823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614823 prefixEnd_614823 := by exact prefixLift 614823
  have htrace : WordTrace (prefixWord ++ tailWord_614823) baseStart_614823 baseEnd_614823 := by
    simpa [prefixWord, tailWord_614823, baseEnd_614823] using wordTrace_append hprefix tailTrace_614823
  have hstable : (prefixWord ++ tailWord_614823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614823).length < 2 ^ (prefixWord ++ tailWord_614823).sum := by decide
  have hdescent : baseEnd_614823 < baseStart_614823 := by decide
  rcases family_descends (prefixWord ++ tailWord_614823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614881 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_614881 : Nat := 118140960795 + 614881 * 2 ^ 59
def prefixEnd_614881 : Nat := 4983230072969 + 3 ^ 40 * 614881 * 2
def baseEnd_614881 : Nat := 210486332211542672639813

theorem tailTrace_614881 : CollatzResearch.WordTrace tailWord_614881 prefixEnd_614881 210486332211542672639813 := by
  unfold tailWord_614881
  simp only [CollatzResearch.WordTrace]
  refine ⟨22426552485398625159372497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14951034990265750106248331 22426552485398625159372497)
  ·
    refine ⟨16819914364048968869529373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22426552485398625159372497 16819914364048968869529373)
    ·
      refine ⟨6307467886518363326073515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16819914364048968869529373 6307467886518363326073515)
      ·
        refine ⟨9461201829777544989110273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6307467886518363326073515 9461201829777544989110273)
        ·
          refine ⟨7095901372333158741832705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9461201829777544989110273 7095901372333158741832705)
          ·
            refine ⟨5321926029249869056374529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7095901372333158741832705 5321926029249869056374529)
            ·
              refine ⟨3991444521937401792280897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5321926029249869056374529 3991444521937401792280897)
              ·
                refine ⟨2993583391453051344210673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3991444521937401792280897 2993583391453051344210673)
                ·
                  refine ⟨2245187543589788508158005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2993583391453051344210673 2245187543589788508158005)
                  ·
                    refine ⟨210486332211542672639813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2245187543589788508158005 210486332211542672639813)
                    ·
                      rfl

theorem cell22_614881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_614881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614881 prefixEnd_614881 := by exact prefixLift 614881
  have htrace : WordTrace (prefixWord ++ tailWord_614881) baseStart_614881 baseEnd_614881 := by
    simpa [prefixWord, tailWord_614881, baseEnd_614881] using wordTrace_append hprefix tailTrace_614881
  have hstable : (prefixWord ++ tailWord_614881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614881).length < 2 ^ (prefixWord ++ tailWord_614881).sum := by decide
  have hdescent : baseEnd_614881 < baseStart_614881 := by decide
  rcases family_descends (prefixWord ++ tailWord_614881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614896 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 5, 4]
def baseStart_614896 : Nat := 118140960795 + 614896 * 2 ^ 59
def prefixEnd_614896 : Nat := 4983230072969 + 3 ^ 40 * 614896 * 2
def baseEnd_614896 : Nat := 210491467018087633514767

theorem tailTrace_614896 : CollatzResearch.WordTrace tailWord_614896 prefixEnd_614896 210491467018087633514767 := by
  unfold tailWord_614896
  simp only [CollatzResearch.WordTrace]
  refine ⟨11213549790172141360584271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14951399720229521814112361 11213549790172141360584271)
  ·
    refine ⟨16820324685258212040876407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11213549790172141360584271 16820324685258212040876407)
    ·
      refine ⟨25230487027887318061314611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16820324685258212040876407 25230487027887318061314611)
      ·
        refine ⟨37845730541830977091971917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25230487027887318061314611 37845730541830977091971917)
        ·
          refine ⟨14192148953186616409489469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37845730541830977091971917 14192148953186616409489469)
          ·
            refine ⟨5322055857444981153558551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14192148953186616409489469 5322055857444981153558551)
            ·
              refine ⟨7983083786167471730337827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5322055857444981153558551 7983083786167471730337827)
              ·
                refine ⟨11974625679251207595506741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7983083786167471730337827 11974625679251207595506741)
                ·
                  refine ⟨1122621157429800712078757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11974625679251207595506741 1122621157429800712078757)
                  ·
                    refine ⟨210491467018087633514767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1122621157429800712078757 210491467018087633514767)
                    ·
                      rfl

theorem cell22_614896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_614896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614896 prefixEnd_614896 := by exact prefixLift 614896
  have htrace : WordTrace (prefixWord ++ tailWord_614896) baseStart_614896 baseEnd_614896 := by
    simpa [prefixWord, tailWord_614896, baseEnd_614896] using wordTrace_append hprefix tailTrace_614896
  have hstable : (prefixWord ++ tailWord_614896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614896).length < 2 ^ (prefixWord ++ tailWord_614896).sum := by decide
  have hdescent : baseEnd_614896 < baseStart_614896 := by decide
  rcases family_descends (prefixWord ++ tailWord_614896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614911 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 6]
def baseStart_614911 : Nat := 118140960795 + 614911 * 2 ^ 59
def prefixEnd_614911 : Nat := 4983230072969 + 3 ^ 40 * 614911 * 2
def baseEnd_614911 : Nat := 70165533941544198129907

theorem tailTrace_614911 : CollatzResearch.WordTrace tailWord_614911 prefixEnd_614911 70165533941544198129907 := by
  unfold tailWord_614911
  simp only [CollatzResearch.WordTrace]
  refine ⟨22427646675289940282964587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14951764450193293521976391 22427646675289940282964587)
  ·
    refine ⟨33641470012934910424446881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22427646675289940282964587 33641470012934910424446881)
    ·
      refine ⟨25231102509701182818335161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33641470012934910424446881 25231102509701182818335161)
      ·
        refine ⟨18923326882275887113751371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25231102509701182818335161 18923326882275887113751371)
        ·
          refine ⟨28384990323413830670627057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18923326882275887113751371 28384990323413830670627057)
          ·
            refine ⟨21288742742560373002970293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28384990323413830670627057 21288742742560373002970293)
            ·
              refine ⟨1995819632115034969028465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21288742742560373002970293 1995819632115034969028465)
              ·
                refine ⟨1496864724086276226771349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1995819632115034969028465 1496864724086276226771349)
                ·
                  refine ⟨70165533941544198129907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1496864724086276226771349 70165533941544198129907)
                  ·
                    rfl

theorem cell22_614911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 6].length) (baseStart_614911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614911 prefixEnd_614911 := by exact prefixLift 614911
  have htrace : WordTrace (prefixWord ++ tailWord_614911) baseStart_614911 baseEnd_614911 := by
    simpa [prefixWord, tailWord_614911, baseEnd_614911] using wordTrace_append hprefix tailTrace_614911
  have hstable : (prefixWord ++ tailWord_614911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614911).length < 2 ^ (prefixWord ++ tailWord_614911).sum := by decide
  have hdescent : baseEnd_614911 < baseStart_614911 := by decide
  rcases family_descends (prefixWord ++ tailWord_614911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614913 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 3, 4]
def baseStart_614913 : Nat := 118140960795 + 614913 * 2 ^ 59
def prefixEnd_614913 : Nat := 4983230072969 + 3 ^ 40 * 614913 * 2
def baseEnd_614913 : Nat := 210497286465505255839715

theorem tailTrace_614913 : CollatzResearch.WordTrace tailWord_614913 prefixEnd_614913 210497286465505255839715 := by
  unfold tailWord_614913
  simp only [CollatzResearch.WordTrace]
  refine ⟨22427719621282694624537393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14951813080855129749691595 22427719621282694624537393)
  ·
    refine ⟨16820789715962020968403045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22427719621282694624537393 16820789715962020968403045)
    ·
      refine ⟨3153898071742878931575571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16820789715962020968403045 3153898071742878931575571)
      ·
        refine ⟨4730847107614318397363357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3153898071742878931575571 4730847107614318397363357)
        ·
          refine ⟨1774067665355369399011259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4730847107614318397363357 1774067665355369399011259)
          ·
            refine ⟨2661101498033054098516889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774067665355369399011259 2661101498033054098516889)
            ·
              refine ⟨1995826123524790573887667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2661101498033054098516889 1995826123524790573887667)
              ·
                refine ⟨2993739185287185860831501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1995826123524790573887667 2993739185287185860831501)
                ·
                  refine ⟨1122652194482694697811813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2993739185287185860831501 1122652194482694697811813)
                  ·
                    refine ⟨210497286465505255839715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1122652194482694697811813 210497286465505255839715)
                    ·
                      rfl

theorem cell22_614913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_614913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614913 prefixEnd_614913 := by exact prefixLift 614913
  have htrace : WordTrace (prefixWord ++ tailWord_614913) baseStart_614913 baseEnd_614913 := by
    simpa [prefixWord, tailWord_614913, baseEnd_614913] using wordTrace_append hprefix tailTrace_614913
  have hstable : (prefixWord ++ tailWord_614913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614913).length < 2 ^ (prefixWord ++ tailWord_614913).sum := by decide
  have hdescent : baseEnd_614913 < baseStart_614913 := by decide
  rcases family_descends (prefixWord ++ tailWord_614913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614964 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_614964 : Nat := 118140960795 + 614964 * 2 ^ 59
def prefixEnd_614964 : Nat := 4983230072969 + 3 ^ 40 * 614964 * 2
def baseEnd_614964 : Nat := 210514744807758122814559

theorem tailTrace_614964 : CollatzResearch.WordTrace tailWord_614964 prefixEnd_614964 210514744807758122814559 := by
  unfold tailWord_614964
  simp only [CollatzResearch.WordTrace]
  refine ⟨11214789872048965167321973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14953053162731953556429297 11214789872048965167321973)
  ·
    refine ⟨1051386550504590484436435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11214789872048965167321973 1051386550504590484436435)
    ·
      refine ⟨1577079825756885726654653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1051386550504590484436435 1577079825756885726654653)
      ·
        refine ⟨591404934658832147495495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1577079825756885726654653 591404934658832147495495)
        ·
          refine ⟨887107401988248221243243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591404934658832147495495 887107401988248221243243)
          ·
            refine ⟨1330661102982372331864865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887107401988248221243243 1330661102982372331864865)
            ·
              refine ⟨997995827236779248898649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1330661102982372331864865 997995827236779248898649)
              ·
                refine ⟨748496870427584436673987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997995827236779248898649 748496870427584436673987)
                ·
                  refine ⟨1122745305641376655010981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748496870427584436673987 1122745305641376655010981)
                  ·
                    refine ⟨210514744807758122814559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1122745305641376655010981 210514744807758122814559)
                    ·
                      rfl

theorem cell22_614964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_614964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614964 prefixEnd_614964 := by exact prefixLift 614964
  have htrace : WordTrace (prefixWord ++ tailWord_614964) baseStart_614964 baseEnd_614964 := by
    simpa [prefixWord, tailWord_614964, baseEnd_614964] using wordTrace_append hprefix tailTrace_614964
  have hstable : (prefixWord ++ tailWord_614964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614964).length < 2 ^ (prefixWord ++ tailWord_614964).sum := by decide
  have hdescent : baseEnd_614964 < baseStart_614964 := by decide
  rcases family_descends (prefixWord ++ tailWord_614964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_614973 : List Nat := [1, 4, 1, 3, 2, 2, 1, 8]
def baseStart_614973 : Nat := 118140960795 + 614973 * 2 ^ 59
def prefixEnd_614973 : Nat := 4983230072969 + 3 ^ 40 * 614973 * 2
def baseEnd_614973 : Nat := 23390869521298344371059

theorem tailTrace_614973 : CollatzResearch.WordTrace tailWord_614973 prefixEnd_614973 23390869521298344371059 := by
  unfold tailWord_614973
  simp only [CollatzResearch.WordTrace]
  refine ⟨22429908001065324871721573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14953272000710216581147715 22429908001065324871721573)
  ·
    refine ⟨4205607750199748413447795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22429908001065324871721573 4205607750199748413447795)
    ·
      refine ⟨6308411625299622620171693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4205607750199748413447795 6308411625299622620171693)
      ·
        refine ⟨2365654359487358482564385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6308411625299622620171693 2365654359487358482564385)
        ·
          refine ⟨1774240769615518861923289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2365654359487358482564385 1774240769615518861923289)
          ·
            refine ⟨1330680577211639146442467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1774240769615518861923289 1330680577211639146442467)
            ·
              refine ⟨1996020865817458719663701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1330680577211639146442467 1996020865817458719663701)
              ·
                refine ⟨23390869521298344371059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1996020865817458719663701 23390869521298344371059)
                ·
                  rfl

theorem cell22_614973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 8].length) (baseStart_614973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_614973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_614973 prefixEnd_614973 := by exact prefixLift 614973
  have htrace : WordTrace (prefixWord ++ tailWord_614973) baseStart_614973 baseEnd_614973 := by
    simpa [prefixWord, tailWord_614973, baseEnd_614973] using wordTrace_append hprefix tailTrace_614973
  have hstable : (prefixWord ++ tailWord_614973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_614973).length < 2 ^ (prefixWord ++ tailWord_614973).sum := by decide
  have hdescent : baseEnd_614973 < baseStart_614973 := by decide
  rcases family_descends (prefixWord ++ tailWord_614973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615063 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 6]
def baseStart_615063 : Nat := 118140960795 + 615063 * 2 ^ 59
def prefixEnd_615063 : Nat := 4983230072969 + 3 ^ 40 * 615063 * 2
def baseEnd_615063 : Nat := 70182878176984954863085

theorem tailTrace_615063 : CollatzResearch.WordTrace tailWord_615063 prefixEnd_615063 70182878176984954863085 := by
  unfold tailWord_615063
  simp only [CollatzResearch.WordTrace]
  refine ⟨22433190570739270242497843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14955460380492846828331895 22433190570739270242497843)
  ·
    refine ⟨33649785856108905363746765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22433190570739270242497843 33649785856108905363746765)
    ·
      refine ⟨12618669696040839511405037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33649785856108905363746765 12618669696040839511405037)
      ·
        refine ⟨4732001136015314816776889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12618669696040839511405037 4732001136015314816776889)
        ·
          refine ⟨3549000852011486112582667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4732001136015314816776889 3549000852011486112582667)
          ·
            refine ⟨5323501278017229168874001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3549000852011486112582667 5323501278017229168874001)
            ·
              refine ⟨3992625958512921876655501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5323501278017229168874001 3992625958512921876655501)
              ·
                refine ⟨1497234734442345703745813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3992625958512921876655501 1497234734442345703745813)
                ·
                  refine ⟨70182878176984954863085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1497234734442345703745813 70182878176984954863085)
                  ·
                    rfl

theorem cell22_615063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 6].length) (baseStart_615063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615063 prefixEnd_615063 := by exact prefixLift 615063
  have htrace : WordTrace (prefixWord ++ tailWord_615063) baseStart_615063 baseEnd_615063 := by
    simpa [prefixWord, tailWord_615063, baseEnd_615063] using wordTrace_append hprefix tailTrace_615063
  have hstable : (prefixWord ++ tailWord_615063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615063).length < 2 ^ (prefixWord ++ tailWord_615063).sum := by decide
  have hdescent : baseEnd_615063 < baseStart_615063 := by decide
  rcases family_descends (prefixWord ++ tailWord_615063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615112 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 2, 3]
def baseStart_615112 : Nat := 118140960795 + 615112 * 2 ^ 59
def prefixEnd_615112 : Nat := 4983230072969 + 3 ^ 40 * 615112 * 2
def baseEnd_615112 : Nat := 210565408232335070114105

theorem tailTrace_615112 : CollatzResearch.WordTrace tailWord_615112 prefixEnd_615112 210565408232335070114105 := by
  unfold tailWord_615112
  simp only [CollatzResearch.WordTrace]
  refine ⟨11217488873780875805515795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14956651831707834407354393 11217488873780875805515795)
  ·
    refine ⟨16826233310671313708273693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11217488873780875805515795 16826233310671313708273693)
    ·
      refine ⟨6309837491501742640602635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16826233310671313708273693 6309837491501742640602635)
      ·
        refine ⟨9464756237252613960903953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6309837491501742640602635 9464756237252613960903953)
        ·
          refine ⟨7098567177939460470677965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9464756237252613960903953 7098567177939460470677965)
          ·
            refine ⟨2661962691727297676504237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7098567177939460470677965 2661962691727297676504237)
            ·
              refine ⟨998236009397736628689089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2661962691727297676504237 998236009397736628689089)
              ·
                refine ⟨748677007048302471516817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998236009397736628689089 748677007048302471516817)
                ·
                  refine ⟨561507755286226853637613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 748677007048302471516817 561507755286226853637613)
                  ·
                    refine ⟨210565408232335070114105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 561507755286226853637613 210565408232335070114105)
                    ·
                      rfl

theorem cell22_615112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_615112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615112 prefixEnd_615112 := by exact prefixLift 615112
  have htrace : WordTrace (prefixWord ++ tailWord_615112) baseStart_615112 baseEnd_615112 := by
    simpa [prefixWord, tailWord_615112, baseEnd_615112] using wordTrace_append hprefix tailTrace_615112
  have hstable : (prefixWord ++ tailWord_615112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615112).length < 2 ^ (prefixWord ++ tailWord_615112).sum := by decide
  have hdescent : baseEnd_615112 < baseStart_615112 := by decide
  rcases family_descends (prefixWord ++ tailWord_615112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615153 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 9]
def baseStart_615153 : Nat := 118140960795 + 615153 * 2 ^ 59
def prefixEnd_615153 : Nat := 4983230072969 + 3 ^ 40 * 615153 * 2
def baseEnd_615153 : Nat := 70193147790074876612993

theorem tailTrace_615153 : CollatzResearch.WordTrace tailWord_615153 prefixEnd_615153 70193147790074876612993 := by
  unfold tailWord_615153
  simp only [CollatzResearch.WordTrace]
  refine ⟨22436473140413215613274113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14957648760275477075516075 22436473140413215613274113)
  ·
    refine ⟨16827354855309911709955585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22436473140413215613274113 16827354855309911709955585)
    ·
      refine ⟨12620516141482433782466689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16827354855309911709955585 12620516141482433782466689)
      ·
        refine ⟨9465387106111825336850017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12620516141482433782466689 9465387106111825336850017)
        ·
          refine ⟨7099040329583869002637513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9465387106111825336850017 7099040329583869002637513)
          ·
            refine ⟨5324280247187901751978135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7099040329583869002637513 5324280247187901751978135)
            ·
              refine ⟨7986420370781852627967203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5324280247187901751978135 7986420370781852627967203)
              ·
                refine ⟨11979630556172778941950805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7986420370781852627967203 11979630556172778941950805)
                ·
                  refine ⟨70193147790074876612993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11979630556172778941950805 70193147790074876612993)
                  ·
                    rfl

theorem cell22_615153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_615153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615153 prefixEnd_615153 := by exact prefixLift 615153
  have htrace : WordTrace (prefixWord ++ tailWord_615153) baseStart_615153 baseEnd_615153 := by
    simpa [prefixWord, tailWord_615153, baseEnd_615153] using wordTrace_append hprefix tailTrace_615153
  have hstable : (prefixWord ++ tailWord_615153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615153).length < 2 ^ (prefixWord ++ tailWord_615153).sum := by decide
  have hdescent : baseEnd_615153 < baseStart_615153 := by decide
  rcases family_descends (prefixWord ++ tailWord_615153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615266 : List Nat := [3, 3, 2, 1, 3, 1, 2, 3, 4]
def baseStart_615266 : Nat := 118140960795 + 615266 * 2 ^ 59
def prefixEnd_615266 : Nat := 4983230072969 + 3 ^ 40 * 615266 * 2
def baseEnd_615266 : Nat := 70206041859843333921211

theorem tailTrace_615266 : CollatzResearch.WordTrace tailWord_615266 prefixEnd_615266 70206041859843333921211 := by
  unfold tailWord_615266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5610148647250958978034413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14960396392669223941425101 5610148647250958978034413)
  ·
    refine ⟨2103805742719109616762905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5610148647250958978034413 2103805742719109616762905)
    ·
      refine ⟨1577854307039332212572179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2103805742719109616762905 1577854307039332212572179)
      ·
        refine ⟨2366781460558998318858269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577854307039332212572179 2366781460558998318858269)
        ·
          refine ⟨887543047709624369571851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2366781460558998318858269 887543047709624369571851)
          ·
            refine ⟨1331314571564436554357777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887543047709624369571851 1331314571564436554357777)
            ·
              refine ⟨998485928673327415768333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1331314571564436554357777 998485928673327415768333)
              ·
                refine ⟨374432223252497780913125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 998485928673327415768333 374432223252497780913125)
                ·
                  refine ⟨70206041859843333921211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374432223252497780913125 70206041859843333921211)
                  ·
                    rfl

theorem cell22_615266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_615266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615266 prefixEnd_615266 := by exact prefixLift 615266
  have htrace : WordTrace (prefixWord ++ tailWord_615266) baseStart_615266 baseEnd_615266 := by
    simpa [prefixWord, tailWord_615266, baseEnd_615266] using wordTrace_append hprefix tailTrace_615266
  have hstable : (prefixWord ++ tailWord_615266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615266).length < 2 ^ (prefixWord ++ tailWord_615266).sum := by decide
  have hdescent : baseEnd_615266 < baseStart_615266 := by decide
  rcases family_descends (prefixWord ++ tailWord_615266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615298 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_615298 : Nat := 118140960795 + 615298 * 2 ^ 59
def prefixEnd_615298 : Nat := 4983230072969 + 3 ^ 40 * 615298 * 2
def baseEnd_615298 : Nat := 210629079833492584963535

theorem tailTrace_615298 : CollatzResearch.WordTrace tailWord_615298 prefixEnd_615298 210629079833492584963535 := by
  unfold tailWord_615298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5610440431221976344325637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14961174483258603584868365 5610440431221976344325637)
  ·
    refine ⟨1051957580854120564561057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5610440431221976344325637 1051957580854120564561057)
    ·
      refine ⟨788968185640590423420793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1051957580854120564561057 788968185640590423420793)
      ·
        refine ⟨591726139230442817565595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 788968185640590423420793 591726139230442817565595)
        ·
          refine ⟨887589208845664226348393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591726139230442817565595 887589208845664226348393)
          ·
            refine ⟨665691906634248169761295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 887589208845664226348393 665691906634248169761295)
            ·
              refine ⟨998537859951372254641943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665691906634248169761295 998537859951372254641943)
              ·
                refine ⟨1497806789927058381962915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998537859951372254641943 1497806789927058381962915)
                ·
                  refine ⟨2246710184890587572944373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1497806789927058381962915 2246710184890587572944373)
                  ·
                    refine ⟨210629079833492584963535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2246710184890587572944373 210629079833492584963535)
                    ·
                      rfl

theorem cell22_615298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_615298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615298 prefixEnd_615298 := by exact prefixLift 615298
  have htrace : WordTrace (prefixWord ++ tailWord_615298) baseStart_615298 baseEnd_615298 := by
    simpa [prefixWord, tailWord_615298, baseEnd_615298] using wordTrace_append hprefix tailTrace_615298
  have hstable : (prefixWord ++ tailWord_615298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615298).length < 2 ^ (prefixWord ++ tailWord_615298).sum := by decide
  have hdescent : baseEnd_615298 < baseStart_615298 := by decide
  rcases family_descends (prefixWord ++ tailWord_615298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615386 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 1, 4]
def baseStart_615386 : Nat := 118140960795 + 615386 * 2 ^ 59
def prefixEnd_615386 : Nat := 4983230072969 + 3 ^ 40 * 615386 * 2
def baseEnd_615386 : Nat := 210659204031889688763265

theorem tailTrace_615386 : CollatzResearch.WordTrace tailWord_615386 prefixEnd_615386 210659204031889688763265 := by
  unfold tailWord_615386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611242837142274101626503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14963314232379397604337341 5611242837142274101626503)
  ·
    refine ⟨8416864255713411152439755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5611242837142274101626503 8416864255713411152439755)
    ·
      refine ⟨12625296383570116728659633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8416864255713411152439755 12625296383570116728659633)
      ·
        refine ⟨9468972287677587546494725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12625296383570116728659633 9468972287677587546494725)
        ·
          refine ⟨1775432303939547664967761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9468972287677587546494725 1775432303939547664967761)
          ·
            refine ⟨1331574227954660748725821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1775432303939547664967761 1331574227954660748725821)
            ·
              refine ⟨499340335482997780772183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1331574227954660748725821 499340335482997780772183)
              ·
                refine ⟨749010503224496671158275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499340335482997780772183 749010503224496671158275)
                ·
                  refine ⟨1123515754836745006737413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749010503224496671158275 1123515754836745006737413)
                  ·
                    refine ⟨210659204031889688763265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1123515754836745006737413 210659204031889688763265)
                    ·
                      rfl

theorem cell22_615386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_615386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615386 prefixEnd_615386 := by exact prefixLift 615386
  have htrace : WordTrace (prefixWord ++ tailWord_615386) baseStart_615386 baseEnd_615386 := by
    simpa [prefixWord, tailWord_615386, baseEnd_615386] using wordTrace_append hprefix tailTrace_615386
  have hstable : (prefixWord ++ tailWord_615386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615386).length < 2 ^ (prefixWord ++ tailWord_615386).sum := by decide
  have hdescent : baseEnd_615386 < baseStart_615386 := by decide
  rcases family_descends (prefixWord ++ tailWord_615386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615461 : List Nat := [1, 3, 1, 2, 2, 2, 1, 6, 1, 3]
def baseStart_615461 : Nat := 118140960795 + 615461 * 2 ^ 59
def prefixEnd_615461 : Nat := 4983230072969 + 3 ^ 40 * 615461 * 2
def baseEnd_615461 : Nat := 210684878064614493138035

theorem tailTrace_615461 : CollatzResearch.WordTrace tailWord_615461 prefixEnd_615461 210684878064614493138035 := by
  unfold tailWord_615461
  simp only [CollatzResearch.WordTrace]
  refine ⟨22447706823297384215486237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14965137882198256143657491 22447706823297384215486237)
  ·
    refine ⟨8417890058736519080807339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22447706823297384215486237 8417890058736519080807339)
    ·
      refine ⟨12626835088104778621211009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8417890058736519080807339 12626835088104778621211009)
      ·
        refine ⟨9470126316078583965908257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12626835088104778621211009 9470126316078583965908257)
        ·
          refine ⟨7102594737058937974431193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9470126316078583965908257 7102594737058937974431193)
          ·
            refine ⟨5326946052794203480823395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7102594737058937974431193 5326946052794203480823395)
            ·
              refine ⟨7990419079191305221235093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5326946052794203480823395 7990419079191305221235093)
              ·
                refine ⟨374550894337092432245395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7990419079191305221235093 374550894337092432245395)
                ·
                  refine ⟨561826341505638648368093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374550894337092432245395 561826341505638648368093)
                  ·
                    refine ⟨210684878064614493138035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 561826341505638648368093 210684878064614493138035)
                    ·
                      rfl

theorem cell22_615461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_615461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615461 prefixEnd_615461 := by exact prefixLift 615461
  have htrace : WordTrace (prefixWord ++ tailWord_615461) baseStart_615461 baseEnd_615461 := by
    simpa [prefixWord, tailWord_615461, baseEnd_615461] using wordTrace_append hprefix tailTrace_615461
  have hstable : (prefixWord ++ tailWord_615461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615461).length < 2 ^ (prefixWord ++ tailWord_615461).sum := by decide
  have hdescent : baseEnd_615461 < baseStart_615461 := by decide
  rcases family_descends (prefixWord ++ tailWord_615461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615472 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_615472 : Nat := 118140960795 + 615472 * 2 ^ 59
def prefixEnd_615472 : Nat := 4983230072969 + 3 ^ 40 * 615472 * 2
def baseEnd_615472 : Nat := 210688643589414131113001

theorem tailTrace_615472 : CollatzResearch.WordTrace tailWord_615472 prefixEnd_615472 210688643589414131113001 := by
  unfold tailWord_615472
  simp only [CollatzResearch.WordTrace]
  refine ⟨11224054013128766547068335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14965405350838355396091113 11224054013128766547068335)
  ·
    refine ⟨16836081019693149820602503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11224054013128766547068335 16836081019693149820602503)
    ·
      refine ⟨25254121529539724730903755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16836081019693149820602503 25254121529539724730903755)
      ·
        refine ⟨37881182294309587096355633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25254121529539724730903755 37881182294309587096355633)
        ·
          refine ⟨28410886720732190322266725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37881182294309587096355633 28410886720732190322266725)
          ·
            refine ⟨5327041260137285685425011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28410886720732190322266725 5327041260137285685425011)
            ·
              refine ⟨7990561890205928528137517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5327041260137285685425011 7990561890205928528137517)
              ·
                refine ⟨2996460708827223198051569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7990561890205928528137517 2996460708827223198051569)
                ·
                  refine ⟨2247345531620417398538677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2996460708827223198051569 2247345531620417398538677)
                  ·
                    refine ⟨210688643589414131113001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2247345531620417398538677 210688643589414131113001)
                    ·
                      rfl

theorem cell22_615472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_615472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615472 prefixEnd_615472 := by exact prefixLift 615472
  have htrace : WordTrace (prefixWord ++ tailWord_615472) baseStart_615472 baseEnd_615472 := by
    simpa [prefixWord, tailWord_615472, baseEnd_615472] using wordTrace_append hprefix tailTrace_615472
  have hstable : (prefixWord ++ tailWord_615472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615472).length < 2 ^ (prefixWord ++ tailWord_615472).sum := by decide
  have hdescent : baseEnd_615472 < baseStart_615472 := by decide
  rcases family_descends (prefixWord ++ tailWord_615472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615566 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_615566 : Nat := 118140960795 + 615566 * 2 ^ 59
def prefixEnd_615566 : Nat := 4983230072969 + 3 ^ 40 * 615566 * 2
def baseEnd_615566 : Nat := 210720821710429219262713

theorem tailTrace_615566 : CollatzResearch.WordTrace tailWord_615566 prefixEnd_615566 210720821710429219262713 := by
  unfold tailWord_615566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2806442060989623393507319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14967690991944658098705701 2806442060989623393507319)
  ·
    refine ⟨4209663091484435090260979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2806442060989623393507319 4209663091484435090260979)
    ·
      refine ⟨6314494637226652635391469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4209663091484435090260979 6314494637226652635391469)
      ·
        refine ⟨2367935488959994738271801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6314494637226652635391469 2367935488959994738271801)
        ·
          refine ⟨1775951616719996053703851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2367935488959994738271801 1775951616719996053703851)
          ·
            refine ⟨2663927425079994080555777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1775951616719996053703851 2663927425079994080555777)
            ·
              refine ⟨1997945568809995560416833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2663927425079994080555777 1997945568809995560416833)
              ·
                refine ⟨1498459176607496670312625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1997945568809995560416833 1498459176607496670312625)
                ·
                  refine ⟨1123844382455622502734469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1498459176607496670312625 1123844382455622502734469)
                  ·
                    refine ⟨210720821710429219262713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1123844382455622502734469 210720821710429219262713)
                    ·
                      rfl

theorem cell22_615566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_615566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615566 prefixEnd_615566 := by exact prefixLift 615566
  have htrace : WordTrace (prefixWord ++ tailWord_615566) baseStart_615566 baseEnd_615566 := by
    simpa [prefixWord, tailWord_615566, baseEnd_615566] using wordTrace_append hprefix tailTrace_615566
  have hstable : (prefixWord ++ tailWord_615566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615566).length < 2 ^ (prefixWord ++ tailWord_615566).sum := by decide
  have hdescent : baseEnd_615566 < baseStart_615566 := by decide
  rcases family_descends (prefixWord ++ tailWord_615566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615570 : List Nat := [3, 2, 3, 1, 1, 4, 2, 2, 4]
def baseStart_615570 : Nat := 118140960795 + 615570 * 2 ^ 59
def prefixEnd_615570 : Nat := 4983230072969 + 3 ^ 40 * 615570 * 2
def baseEnd_615570 : Nat := 70240730330724847387567

theorem tailTrace_615570 : CollatzResearch.WordTrace tailWord_615570 prefixEnd_615570 70240730330724847387567 := by
  unfold tailWord_615570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5612920594975623957801041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14967788253268330554136109 5612920594975623957801041)
  ·
    refine ⟨4209690446231717968350781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5612920594975623957801041 4209690446231717968350781)
    ·
      refine ⟨1578633917336894238131543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4209690446231717968350781 1578633917336894238131543)
      ·
        refine ⟨2367950876005341357197315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578633917336894238131543 2367950876005341357197315)
        ·
          refine ⟨3551926314008012035795973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367950876005341357197315 3551926314008012035795973)
          ·
            refine ⟨665986183876502256711745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3551926314008012035795973 665986183876502256711745)
            ·
              refine ⟨499489637907376692533809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665986183876502256711745 499489637907376692533809)
              ·
                refine ⟨374617228430532519400357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 499489637907376692533809 374617228430532519400357)
                ·
                  refine ⟨70240730330724847387567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374617228430532519400357 70240730330724847387567)
                  ·
                    rfl

theorem cell22_615570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_615570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615570 prefixEnd_615570 := by exact prefixLift 615570
  have htrace : WordTrace (prefixWord ++ tailWord_615570) baseStart_615570 baseEnd_615570 := by
    simpa [prefixWord, tailWord_615570, baseEnd_615570] using wordTrace_append hprefix tailTrace_615570
  have hstable : (prefixWord ++ tailWord_615570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615570).length < 2 ^ (prefixWord ++ tailWord_615570).sum := by decide
  have hdescent : baseEnd_615570 < baseStart_615570 := by decide
  rcases family_descends (prefixWord ++ tailWord_615570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615613 : List Nat := [1, 4, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_615613 : Nat := 118140960795 + 615613 * 2 ^ 59
def prefixEnd_615613 : Nat := 4983230072969 + 3 ^ 40 * 615613 * 2
def baseEnd_615613 : Nat := 210736910770936763337569

theorem tailTrace_615613 : CollatzResearch.WordTrace tailWord_615613 prefixEnd_615613 210736910770936763337569 := by
  unfold tailWord_615613
  simp only [CollatzResearch.WordTrace]
  refine ⟨22453250718746714175019493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14968833812497809450012995 22453250718746714175019493)
  ·
    refine ⟨4209984509765008907816155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22453250718746714175019493 4209984509765008907816155)
    ·
      refine ⟨6314976764647513361724233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4209984509765008907816155 6314976764647513361724233)
      ·
        refine ⟨4736232573485635021293175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6314976764647513361724233 4736232573485635021293175)
        ·
          refine ⟨7104348860228452531939763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4736232573485635021293175 7104348860228452531939763)
          ·
            refine ⟨10656523290342678797909645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104348860228452531939763 10656523290342678797909645)
            ·
              refine ⟨3996196233878504549216117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10656523290342678797909645 3996196233878504549216117)
              ·
                refine ⟨374643396926109801489011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3996196233878504549216117 374643396926109801489011)
                ·
                  refine ⟨561965095389164702233517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374643396926109801489011 561965095389164702233517)
                  ·
                    refine ⟨210736910770936763337569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 561965095389164702233517 210736910770936763337569)
                    ·
                      rfl

theorem cell22_615613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_615613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615613 prefixEnd_615613 := by exact prefixLift 615613
  have htrace : WordTrace (prefixWord ++ tailWord_615613) baseStart_615613 baseEnd_615613 := by
    simpa [prefixWord, tailWord_615613, baseEnd_615613] using wordTrace_append hprefix tailTrace_615613
  have hstable : (prefixWord ++ tailWord_615613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615613).length < 2 ^ (prefixWord ++ tailWord_615613).sum := by decide
  have hdescent : baseEnd_615613 < baseStart_615613 := by decide
  rcases family_descends (prefixWord ++ tailWord_615613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615624 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_615624 : Nat := 118140960795 + 615624 * 2 ^ 59
def prefixEnd_615624 : Nat := 4983230072969 + 3 ^ 40 * 615624 * 2
def baseEnd_615624 : Nat := 210740676295736401312535

theorem tailTrace_615624 : CollatzResearch.WordTrace tailWord_615624 prefixEnd_615624 210740676295736401312535 := by
  unfold tailWord_615624
  simp only [CollatzResearch.WordTrace]
  refine ⟨11226825960853431526834963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14969101281137908702446617 11226825960853431526834963)
  ·
    refine ⟨16840238941280147290252445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11226825960853431526834963 16840238941280147290252445)
    ·
      refine ⟨6315089602980055233844667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16840238941280147290252445 6315089602980055233844667)
      ·
        refine ⟨9472634404470082850767001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6315089602980055233844667 9472634404470082850767001)
        ·
          refine ⟨7104475803352562138075251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9472634404470082850767001 7104475803352562138075251)
          ·
            refine ⟨10656713705028843207112877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7104475803352562138075251 10656713705028843207112877)
            ·
              refine ⟨3996267639385816202667329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10656713705028843207112877 3996267639385816202667329)
              ·
                refine ⟨2997200729539362152000497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3996267639385816202667329 2997200729539362152000497)
                ·
                  refine ⟨2247900547154521614000373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2997200729539362152000497 2247900547154521614000373)
                  ·
                    refine ⟨210740676295736401312535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2247900547154521614000373 210740676295736401312535)
                    ·
                      rfl

theorem cell22_615624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_615624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615624 prefixEnd_615624 := by exact prefixLift 615624
  have htrace : WordTrace (prefixWord ++ tailWord_615624) baseStart_615624 baseEnd_615624 := by
    simpa [prefixWord, tailWord_615624, baseEnd_615624] using wordTrace_append hprefix tailTrace_615624
  have hstable : (prefixWord ++ tailWord_615624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615624).length < 2 ^ (prefixWord ++ tailWord_615624).sum := by decide
  have hdescent : baseEnd_615624 < baseStart_615624 := by decide
  rcases family_descends (prefixWord ++ tailWord_615624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615626 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_615626 : Nat := 118140960795 + 615626 * 2 ^ 59
def prefixEnd_615626 : Nat := 4983230072969 + 3 ^ 40 * 615626 * 2
def baseEnd_615626 : Nat := 70247120312203020920843

theorem tailTrace_615626 : CollatzResearch.WordTrace tailWord_615626 prefixEnd_615626 70247120312203020920843 := by
  unfold tailWord_615626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613431216924904348810683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14969149911799744930161821 5613431216924904348810683)
  ·
    refine ⟨8420146825387356523216025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5613431216924904348810683 8420146825387356523216025)
    ·
      refine ⟨6315110119040517392412019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8420146825387356523216025 6315110119040517392412019)
      ·
        refine ⟨9472665178560776088618029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6315110119040517392412019 9472665178560776088618029)
        ·
          refine ⟨3552249441960291033231761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9472665178560776088618029 3552249441960291033231761)
          ·
            refine ⟨2664187081470218274923821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3552249441960291033231761 2664187081470218274923821)
            ·
              refine ⟨999070155551331853096433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2664187081470218274923821 999070155551331853096433)
              ·
                refine ⟨749302616663498889822325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 999070155551331853096433 749302616663498889822325)
                ·
                  refine ⟨70247120312203020920843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 749302616663498889822325 70247120312203020920843)
                  ·
                    rfl

theorem cell22_615626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_615626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615626 prefixEnd_615626 := by exact prefixLift 615626
  have htrace : WordTrace (prefixWord ++ tailWord_615626) baseStart_615626 baseEnd_615626 := by
    simpa [prefixWord, tailWord_615626, baseEnd_615626] using wordTrace_append hprefix tailTrace_615626
  have hstable : (prefixWord ++ tailWord_615626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615626).length < 2 ^ (prefixWord ++ tailWord_615626).sum := by decide
  have hdescent : baseEnd_615626 < baseStart_615626 := by decide
  rcases family_descends (prefixWord ++ tailWord_615626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615639 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 5, 4]
def baseStart_615639 : Nat := 118140960795 + 615639 * 2 ^ 59
def prefixEnd_615639 : Nat := 4983230072969 + 3 ^ 40 * 615639 * 2
def baseEnd_615639 : Nat := 210745811102281362187489

theorem tailTrace_615639 : CollatzResearch.WordTrace tailWord_615639 prefixEnd_615639 210745811102281362187489 := by
  unfold tailWord_615639
  simp only [CollatzResearch.WordTrace]
  refine ⟨22454199016652520615465971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14969466011101680410310647 22454199016652520615465971)
  ·
    refine ⟨33681298524978780923198957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22454199016652520615465971 33681298524978780923198957)
    ·
      refine ⟨12630486946867042846199609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33681298524978780923198957 12630486946867042846199609)
      ·
        refine ⟨9472865210150282134649707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12630486946867042846199609 9472865210150282134649707)
        ·
          refine ⟨14209297815225423201974561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9472865210150282134649707 14209297815225423201974561)
          ·
            refine ⟨10656973361419067401480921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14209297815225423201974561 10656973361419067401480921)
            ·
              refine ⟨7992730021064300551110691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10656973361419067401480921 7992730021064300551110691)
              ·
                refine ⟨11989095031596450826666037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7992730021064300551110691 11989095031596450826666037)
                ·
                  refine ⟨1123977659212167264999941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11989095031596450826666037 1123977659212167264999941)
                  ·
                    refine ⟨210745811102281362187489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1123977659212167264999941 210745811102281362187489)
                    ·
                      rfl

theorem cell22_615639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_615639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615639 prefixEnd_615639 := by exact prefixLift 615639
  have htrace : WordTrace (prefixWord ++ tailWord_615639) baseStart_615639 baseEnd_615639 := by
    simpa [prefixWord, tailWord_615639, baseEnd_615639] using wordTrace_append hprefix tailTrace_615639
  have hstable : (prefixWord ++ tailWord_615639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615639).length < 2 ^ (prefixWord ++ tailWord_615639).sum := by decide
  have hdescent : baseEnd_615639 < baseStart_615639 := by decide
  rcases family_descends (prefixWord ++ tailWord_615639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615688 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 6]
def baseStart_615688 : Nat := 118140960795 + 615688 * 2 ^ 59
def prefixEnd_615688 : Nat := 4983230072969 + 3 ^ 40 * 615688 * 2
def baseEnd_615688 : Nat := 70254194934553855904113

theorem tailTrace_615688 : CollatzResearch.WordTrace tailWord_615688 prefixEnd_615688 70254194934553855904113 := by
  unfold tailWord_615688
  simp only [CollatzResearch.WordTrace]
  refine ⟨11227993096737500991999859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14970657462316667989333145 11227993096737500991999859)
  ·
    refine ⟨16841989645106251487999789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11227993096737500991999859 16841989645106251487999789)
    ·
      refine ⟨6315746116914844307999921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16841989645106251487999789 6315746116914844307999921)
      ·
        refine ⟨4736809587686133230999941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6315746116914844307999921 4736809587686133230999941)
        ·
          refine ⟨888151797691149980812489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4736809587686133230999941 888151797691149980812489)
          ·
            refine ⟨666113848268362485609367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 888151797691149980812489 666113848268362485609367)
            ·
              refine ⟨999170772402543728414051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666113848268362485609367 999170772402543728414051)
              ·
                refine ⟨1498756158603815592621077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999170772402543728414051 1498756158603815592621077)
                ·
                  refine ⟨70254194934553855904113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1498756158603815592621077 70254194934553855904113)
                  ·
                    rfl

theorem cell22_615688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 6].length) (baseStart_615688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615688 prefixEnd_615688 := by exact prefixLift 615688
  have htrace : WordTrace (prefixWord ++ tailWord_615688) baseStart_615688 baseEnd_615688 := by
    simpa [prefixWord, tailWord_615688, baseEnd_615688] using wordTrace_append hprefix tailTrace_615688
  have hstable : (prefixWord ++ tailWord_615688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615688).length < 2 ^ (prefixWord ++ tailWord_615688).sum := by decide
  have hdescent : baseEnd_615688 < baseStart_615688 := by decide
  rcases family_descends (prefixWord ++ tailWord_615688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615703 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 2, 3]
def baseStart_615703 : Nat := 118140960795 + 615703 * 2 ^ 59
def prefixEnd_615703 : Nat := 4983230072969 + 3 ^ 40 * 615703 * 2
def baseEnd_615703 : Nat := 210767719610206528587293

theorem tailTrace_615703 : CollatzResearch.WordTrace tailWord_615703 prefixEnd_615703 210767719610206528587293 := by
  unfold tailWord_615703
  simp only [CollatzResearch.WordTrace]
  refine ⟨22456533288420659545795763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14971022192280439697197175 22456533288420659545795763)
  ·
    refine ⟨33684799932630989318693645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22456533288420659545795763 33684799932630989318693645)
    ·
      refine ⟨12631799974736620994510117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33684799932630989318693645 12631799974736620994510117)
      ·
        refine ⟨2368462495263116436470647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12631799974736620994510117 2368462495263116436470647)
        ·
          refine ⟨3552693742894674654705971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368462495263116436470647 3552693742894674654705971)
          ·
            refine ⟨5329040614342011982058957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3552693742894674654705971 5329040614342011982058957)
            ·
              refine ⟨1998390230378254493272109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5329040614342011982058957 1998390230378254493272109)
              ·
                refine ⟨749396336391845434977041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1998390230378254493272109 749396336391845434977041)
                ·
                  refine ⟨562047252293884076232781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 749396336391845434977041 562047252293884076232781)
                  ·
                    refine ⟨210767719610206528587293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 562047252293884076232781 210767719610206528587293)
                    ·
                      rfl

theorem cell22_615703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_615703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615703 prefixEnd_615703 := by exact prefixLift 615703
  have htrace : WordTrace (prefixWord ++ tailWord_615703) baseStart_615703 baseEnd_615703 := by
    simpa [prefixWord, tailWord_615703, baseEnd_615703] using wordTrace_append hprefix tailTrace_615703
  have hstable : (prefixWord ++ tailWord_615703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615703).length < 2 ^ (prefixWord ++ tailWord_615703).sum := by decide
  have hdescent : baseEnd_615703 < baseStart_615703 := by decide
  rcases family_descends (prefixWord ++ tailWord_615703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615761 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 5]
def baseStart_615761 : Nat := 118140960795 + 615761 * 2 ^ 59
def prefixEnd_615761 : Nat := 4983230072969 + 3 ^ 40 * 615761 * 2
def baseEnd_615761 : Nat := 70262524731837903545705

theorem tailTrace_615761 : CollatzResearch.WordTrace tailWord_615761 prefixEnd_615761 70262524731837903545705 := by
  unfold tailWord_615761
  simp only [CollatzResearch.WordTrace]
  refine ⟨22458648722210535451407137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14972432481473690300938091 22458648722210535451407137)
  ·
    refine ⟨16843986541657901588555353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22458648722210535451407137 16843986541657901588555353)
    ·
      refine ⟨12632989906243426191416515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16843986541657901588555353 12632989906243426191416515)
      ·
        refine ⟨18949484859365139287124773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12632989906243426191416515 18949484859365139287124773)
        ·
          refine ⟨3553028411130963616335895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18949484859365139287124773 3553028411130963616335895)
          ·
            refine ⟨5329542616696445424503843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3553028411130963616335895 5329542616696445424503843)
            ·
              refine ⟨7994313925044668136755765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5329542616696445424503843 7994313925044668136755765)
              ·
                refine ⟨749466930472937637820853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7994313925044668136755765 749466930472937637820853)
                ·
                  refine ⟨70262524731837903545705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 749466930472937637820853 70262524731837903545705)
                  ·
                    rfl

theorem cell22_615761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_615761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615761 prefixEnd_615761 := by exact prefixLift 615761
  have htrace : WordTrace (prefixWord ++ tailWord_615761) baseStart_615761 baseEnd_615761 := by
    simpa [prefixWord, tailWord_615761, baseEnd_615761] using wordTrace_append hprefix tailTrace_615761
  have hstable : (prefixWord ++ tailWord_615761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615761).length < 2 ^ (prefixWord ++ tailWord_615761).sum := by decide
  have hdescent : baseEnd_615761 < baseStart_615761 := by decide
  rcases family_descends (prefixWord ++ tailWord_615761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615810 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_615810 : Nat := 118140960795 + 615810 * 2 ^ 59
def prefixEnd_615810 : Nat := 4983230072969 + 3 ^ 40 * 615810 * 2
def baseEnd_615810 : Nat := 210804347896893916161965

theorem tailTrace_615810 : CollatzResearch.WordTrace tailWord_615810 prefixEnd_615810 210804347896893916161965 := by
  unfold tailWord_615810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5615108974758254204985221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14973623932688677879960589 5615108974758254204985221)
  ·
    refine ⟨1052832932767172663434729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5615108974758254204985221 1052832932767172663434729)
    ·
      refine ⟨789624699575379497576047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1052832932767172663434729 789624699575379497576047)
      ·
        refine ⟨1184437049363069246364071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789624699575379497576047 1184437049363069246364071)
        ·
          refine ⟨1776655574044603869546107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184437049363069246364071 1776655574044603869546107)
          ·
            refine ⟨2664983361066905804319161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776655574044603869546107 2664983361066905804319161)
            ·
              refine ⟨1998737520800179353239371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2664983361066905804319161 1998737520800179353239371)
              ·
                refine ⟨2998106281200269029859057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1998737520800179353239371 2998106281200269029859057)
                ·
                  refine ⟨2248579710900201772394293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2998106281200269029859057 2248579710900201772394293)
                  ·
                    refine ⟨210804347896893916161965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2248579710900201772394293 210804347896893916161965)
                    ·
                      rfl

theorem cell22_615810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_615810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615810 prefixEnd_615810 := by exact prefixLift 615810
  have htrace : WordTrace (prefixWord ++ tailWord_615810) baseStart_615810 baseEnd_615810 := by
    simpa [prefixWord, tailWord_615810, baseEnd_615810] using wordTrace_append hprefix tailTrace_615810
  have hstable : (prefixWord ++ tailWord_615810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615810).length < 2 ^ (prefixWord ++ tailWord_615810).sum := by decide
  have hdescent : baseEnd_615810 < baseStart_615810 := by decide
  rcases family_descends (prefixWord ++ tailWord_615810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615883 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 3, 3]
def baseStart_615883 : Nat := 118140960795 + 615883 * 2 ^ 59
def prefixEnd_615883 : Nat := 4983230072969 + 3 ^ 40 * 615883 * 2
def baseEnd_615883 : Nat := 210829337288746059086741

theorem tailTrace_615883 : CollatzResearch.WordTrace tailWord_615883 prefixEnd_615883 210829337288746059086741 := by
  unfold tailWord_615883
  simp only [CollatzResearch.WordTrace]
  refine ⟨22463098427768550287348303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14975398951845700191565535 22463098427768550287348303)
  ·
    refine ⟨33694647641652825431022455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22463098427768550287348303 33694647641652825431022455)
    ·
      refine ⟨50541971462479238146533683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33694647641652825431022455 50541971462479238146533683)
      ·
        refine ⟨75812957193718857219800525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50541971462479238146533683 75812957193718857219800525)
        ·
          refine ⟨28429858947644571457425197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75812957193718857219800525 28429858947644571457425197)
          ·
            refine ⟨10661197105366714296534449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28429858947644571457425197 10661197105366714296534449)
            ·
              refine ⟨7995897829025035722400837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10661197105366714296534449 7995897829025035722400837)
              ·
                refine ⟨1499230842942194197950157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7995897829025035722400837 1499230842942194197950157)
                ·
                  refine ⟨562211566103322824231309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1499230842942194197950157 562211566103322824231309)
                  ·
                    refine ⟨210829337288746059086741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 562211566103322824231309 210829337288746059086741)
                    ·
                      rfl

theorem cell22_615883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 3, 3].length) (baseStart_615883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615883 prefixEnd_615883 := by exact prefixLift 615883
  have htrace : WordTrace (prefixWord ++ tailWord_615883) baseStart_615883 baseEnd_615883 := by
    simpa [prefixWord, tailWord_615883, baseEnd_615883] using wordTrace_append hprefix tailTrace_615883
  have hstable : (prefixWord ++ tailWord_615883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615883).length < 2 ^ (prefixWord ++ tailWord_615883).sum := by decide
  have hdescent : baseEnd_615883 < baseStart_615883 := by decide
  rcases family_descends (prefixWord ++ tailWord_615883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615896 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 9]
def baseStart_615896 : Nat := 118140960795 + 615896 * 2 ^ 59
def prefixEnd_615896 : Nat := 4983230072969 + 3 ^ 40 * 615896 * 2
def baseEnd_615896 : Nat := 70277929151472786170567

theorem tailTrace_615896 : CollatzResearch.WordTrace tailWord_615896 prefixEnd_615896 70277929151472786170567 := by
  unfold tailWord_615896
  simp only [CollatzResearch.WordTrace]
  refine ⟨11231786288360726753785771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14975715051147635671714361 11231786288360726753785771)
  ·
    refine ⟨16847679432541090130678657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11231786288360726753785771 16847679432541090130678657)
    ·
      refine ⟨12635759574405817598008993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16847679432541090130678657 12635759574405817598008993)
      ·
        refine ⟨9476819680804363198506745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12635759574405817598008993 9476819680804363198506745)
        ·
          refine ⟨7107614760603272398880059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9476819680804363198506745 7107614760603272398880059)
          ·
            refine ⟨10661422140904908598320089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7107614760603272398880059 10661422140904908598320089)
            ·
              refine ⟨7996066605678681448740067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10661422140904908598320089 7996066605678681448740067)
              ·
                refine ⟨11994099908518022173110101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7996066605678681448740067 11994099908518022173110101)
                ·
                  refine ⟨70277929151472786170567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11994099908518022173110101 70277929151472786170567)
                  ·
                    rfl

theorem cell22_615896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_615896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615896 prefixEnd_615896 := by exact prefixLift 615896
  have htrace : WordTrace (prefixWord ++ tailWord_615896) baseStart_615896 baseEnd_615896 := by
    simpa [prefixWord, tailWord_615896, baseEnd_615896] using wordTrace_append hprefix tailTrace_615896
  have hstable : (prefixWord ++ tailWord_615896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615896).length < 2 ^ (prefixWord ++ tailWord_615896).sum := by decide
  have hdescent : baseEnd_615896 < baseStart_615896 := by decide
  rcases family_descends (prefixWord ++ tailWord_615896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615928 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 2, 5]
def baseStart_615928 : Nat := 118140960795 + 615928 * 2 ^ 59
def prefixEnd_615928 : Nat := 4983230072969 + 3 ^ 40 * 615928 * 2
def baseEnd_615928 : Nat := 210844741708380941711603

theorem tailTrace_615928 : CollatzResearch.WordTrace tailWord_615928 prefixEnd_615928 210844741708380941711603 := by
  unfold tailWord_615928
  simp only [CollatzResearch.WordTrace]
  refine ⟨11232369856302761486368219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14976493141737015315157625 11232369856302761486368219)
  ·
    refine ⟨16848554784454142229552329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11232369856302761486368219 16848554784454142229552329)
    ·
      refine ⟨12636416088340606672164247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16848554784454142229552329 12636416088340606672164247)
      ·
        refine ⟨18954624132510910008246371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12636416088340606672164247 18954624132510910008246371)
        ·
          refine ⟨28431936198766365012369557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18954624132510910008246371 28431936198766365012369557)
          ·
            refine ⟨1332747009317173359954823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28431936198766365012369557 1332747009317173359954823)
            ·
              refine ⟨1999120513975760039932235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332747009317173359954823 1999120513975760039932235)
              ·
                refine ⟨2998680770963640059898353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999120513975760039932235 2998680770963640059898353)
                ·
                  refine ⟨2249010578222730044923765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2998680770963640059898353 2249010578222730044923765)
                  ·
                    refine ⟨210844741708380941711603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2249010578222730044923765 210844741708380941711603)
                    ·
                      rfl

theorem cell22_615928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_615928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615928 prefixEnd_615928 := by exact prefixLift 615928
  have htrace : WordTrace (prefixWord ++ tailWord_615928) baseStart_615928 baseEnd_615928 := by
    simpa [prefixWord, tailWord_615928, baseEnd_615928] using wordTrace_append hprefix tailTrace_615928
  have hstable : (prefixWord ++ tailWord_615928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615928).length < 2 ^ (prefixWord ++ tailWord_615928).sum := by decide
  have hdescent : baseEnd_615928 < baseStart_615928 := by decide
  rcases family_descends (prefixWord ++ tailWord_615928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_615934 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_615934 : Nat := 118140960795 + 615934 * 2 ^ 59
def prefixEnd_615934 : Nat := 4983230072969 + 3 ^ 40 * 615934 * 2
def baseEnd_615934 : Nat := 210846795630998926061585

theorem tailTrace_615934 : CollatzResearch.WordTrace tailWord_615934 prefixEnd_615934 210846795630998926061585 := by
  unfold tailWord_615934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808119818822973249681857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14976639033722523998303237 2808119818822973249681857)
  ·
    refine ⟨2106089864117229937261393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2808119818822973249681857 2106089864117229937261393)
    ·
      refine ⟨1579567398087922452946045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2106089864117229937261393 1579567398087922452946045)
      ·
        refine ⟨592337774282970919854767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1579567398087922452946045 592337774282970919854767)
        ·
          refine ⟨888506661424456379782151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592337774282970919854767 888506661424456379782151)
          ·
            refine ⟨1332759992136684569673227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888506661424456379782151 1332759992136684569673227)
            ·
              refine ⟨1999139988205026854509841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332759992136684569673227 1999139988205026854509841)
              ·
                refine ⟨1499354991153770140882381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999139988205026854509841 1499354991153770140882381)
                ·
                  refine ⟨562258121682663802830893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1499354991153770140882381 562258121682663802830893)
                  ·
                    refine ⟨210846795630998926061585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 562258121682663802830893 210846795630998926061585)
                    ·
                      rfl

theorem cell22_615934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_615934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_615934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_615934 prefixEnd_615934 := by exact prefixLift 615934
  have htrace : WordTrace (prefixWord ++ tailWord_615934) baseStart_615934 baseEnd_615934 := by
    simpa [prefixWord, tailWord_615934, baseEnd_615934] using wordTrace_append hprefix tailTrace_615934
  have hstable : (prefixWord ++ tailWord_615934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_615934).length < 2 ^ (prefixWord ++ tailWord_615934).sum := by decide
  have hdescent : baseEnd_615934 < baseStart_615934 := by decide
  rcases family_descends (prefixWord ++ tailWord_615934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616033 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_616033 : Nat := 118140960795 + 616033 * 2 ^ 59
def prefixEnd_616033 : Nat := 4983230072969 + 3 ^ 40 * 616033 * 2
def baseEnd_616033 : Nat := 210880685354195667836281

theorem tailTrace_616033 : CollatzResearch.WordTrace tailWord_616033 prefixEnd_616033 210880685354195667836281 := by
  unfold tailWord_616033
  simp only [CollatzResearch.WordTrace]
  refine ⟨22468569377225125905308753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14979046251483417270205835 22468569377225125905308753)
  ·
    refine ⟨16851427032918844428981565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22468569377225125905308753 16851427032918844428981565)
    ·
      refine ⟨6319285137344566660868087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16851427032918844428981565 6319285137344566660868087)
      ·
        refine ⟨9478927706016849991302131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6319285137344566660868087 9478927706016849991302131)
        ·
          refine ⟨14218391559025274986953197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9478927706016849991302131 14218391559025274986953197)
          ·
            refine ⟨5331896834634478120107449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14218391559025274986953197 5331896834634478120107449)
            ·
              refine ⟨3998922625975858590080587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5331896834634478120107449 3998922625975858590080587)
              ·
                refine ⟨5998383938963787885120881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3998922625975858590080587 5998383938963787885120881)
                ·
                  refine ⟨4498787954222840913840661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5998383938963787885120881 4498787954222840913840661)
                  ·
                    refine ⟨210880685354195667836281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4498787954222840913840661 210880685354195667836281)
                    ·
                      rfl

theorem cell22_616033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_616033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616033 prefixEnd_616033 := by exact prefixLift 616033
  have htrace : WordTrace (prefixWord ++ tailWord_616033) baseStart_616033 baseEnd_616033 := by
    simpa [prefixWord, tailWord_616033, baseEnd_616033] using wordTrace_append hprefix tailTrace_616033
  have hstable : (prefixWord ++ tailWord_616033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616033).length < 2 ^ (prefixWord ++ tailWord_616033).sum := by decide
  have hdescent : baseEnd_616033 < baseStart_616033 := by decide
  rcases family_descends (prefixWord ++ tailWord_616033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616125 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_616125 : Nat := 118140960795 + 616125 * 2 ^ 59
def prefixEnd_616125 : Nat := 4983230072969 + 3 ^ 40 * 616125 * 2
def baseEnd_616125 : Nat := 210912178834338094535999

theorem tailTrace_616125 : CollatzResearch.WordTrace tailWord_616125 prefixEnd_616125 210912178834338094535999 := by
  unfold tailWord_616125
  simp only [CollatzResearch.WordTrace]
  refine ⟨22471924892891825617657829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14981283261927883745105219 22471924892891825617657829)
  ·
    refine ⟨4213485917417217303310843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22471924892891825617657829 4213485917417217303310843)
    ·
      refine ⟨6320228876125825954966265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4213485917417217303310843 6320228876125825954966265)
      ·
        refine ⟨4740171657094369466224699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6320228876125825954966265 4740171657094369466224699)
        ·
          refine ⟨7110257485641554199337049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740171657094369466224699 7110257485641554199337049)
          ·
            refine ⟨5332693114231165649502787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7110257485641554199337049 5332693114231165649502787)
            ·
              refine ⟨7999039671346748474254181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5332693114231165649502787 7999039671346748474254181)
              ·
                refine ⟨1499819938377515338922659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7999039671346748474254181 1499819938377515338922659)
                ·
                  refine ⟨2249729907566273008383989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1499819938377515338922659 2249729907566273008383989)
                  ·
                    refine ⟨210912178834338094535999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2249729907566273008383989 210912178834338094535999)
                    ·
                      rfl

theorem cell22_616125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_616125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616125 prefixEnd_616125 := by exact prefixLift 616125
  have htrace : WordTrace (prefixWord ++ tailWord_616125) baseStart_616125 baseEnd_616125 := by
    simpa [prefixWord, tailWord_616125, baseEnd_616125] using wordTrace_append hprefix tailTrace_616125
  have hstable : (prefixWord ++ tailWord_616125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616125).length < 2 ^ (prefixWord ++ tailWord_616125).sum := by decide
  have hdescent : baseEnd_616125 < baseStart_616125 := by decide
  rcases family_descends (prefixWord ++ tailWord_616125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616127 : List Nat := [1, 1, 2, 2, 2, 3, 4, 3, 4]
def baseStart_616127 : Nat := 118140960795 + 616127 * 2 ^ 59
def prefixEnd_616127 : Nat := 4983230072969 + 3 ^ 40 * 616127 * 2
def baseEnd_616127 : Nat := 70304287825070251995331

theorem tailTrace_616127 : CollatzResearch.WordTrace tailWord_616127 prefixEnd_616127 70304287825070251995331 := by
  unfold tailWord_616127
  simp only [CollatzResearch.WordTrace]
  refine ⟨22471997838884579959230635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14981331892589719972820423 22471997838884579959230635)
  ·
    refine ⟨33707996758326869938845953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22471997838884579959230635 33707996758326869938845953)
    ·
      refine ⟨25280997568745152454134465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33707996758326869938845953 25280997568745152454134465)
      ·
        refine ⟨18960748176558864340600849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25280997568745152454134465 18960748176558864340600849)
        ·
          refine ⟨14220561132419148255450637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18960748176558864340600849 14220561132419148255450637)
          ·
            refine ⟨5332710424657180595793989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14220561132419148255450637 5332710424657180595793989)
            ·
              refine ⟨999883204623221361711373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5332710424657180595793989 999883204623221361711373)
              ·
                refine ⟨374956201733708010641765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 999883204623221361711373 374956201733708010641765)
                ·
                  refine ⟨70304287825070251995331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374956201733708010641765 70304287825070251995331)
                  ·
                    rfl

theorem cell22_616127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 4].length) (baseStart_616127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616127 prefixEnd_616127 := by exact prefixLift 616127
  have htrace : WordTrace (prefixWord ++ tailWord_616127) baseStart_616127 baseEnd_616127 := by
    simpa [prefixWord, tailWord_616127, baseEnd_616127] using wordTrace_append hprefix tailTrace_616127
  have hstable : (prefixWord ++ tailWord_616127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616127).length < 2 ^ (prefixWord ++ tailWord_616127).sum := by decide
  have hdescent : baseEnd_616127 < baseStart_616127 := by decide
  rcases family_descends (prefixWord ++ tailWord_616127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616142 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_616142 : Nat := 118140960795 + 616142 * 2 ^ 59
def prefixEnd_616142 : Nat := 4983230072969 + 3 ^ 40 * 616142 * 2
def baseEnd_616142 : Nat := 210917998281755716860947

theorem tailTrace_616142 : CollatzResearch.WordTrace tailWord_616142 prefixEnd_616142 210917998281755716860947 := by
  unfold tailWord_616142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2809068116728779690128335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14981696622553491680684453 2809068116728779690128335)
  ·
    refine ⟨4213602175093169535192503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2809068116728779690128335 4213602175093169535192503)
    ·
      refine ⟨6320403262639754302788755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4213602175093169535192503 6320403262639754302788755)
      ·
        refine ⟨9480604893959631454183133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6320403262639754302788755 9480604893959631454183133)
        ·
          refine ⟨3555226835234861795318675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9480604893959631454183133 3555226835234861795318675)
          ·
            refine ⟨5332840252852292692978013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3555226835234861795318675 5332840252852292692978013)
            ·
              refine ⟨1999815094819609759866755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5332840252852292692978013 1999815094819609759866755)
              ·
                refine ⟨2999722642229414639800133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999815094819609759866755 2999722642229414639800133)
                ·
                  refine ⟨562447995418015244962525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2999722642229414639800133 562447995418015244962525)
                  ·
                    refine ⟨210917998281755716860947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 562447995418015244962525 210917998281755716860947)
                    ·
                      rfl

theorem cell22_616142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_616142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616142 prefixEnd_616142 := by exact prefixLift 616142
  have htrace : WordTrace (prefixWord ++ tailWord_616142) baseStart_616142 baseEnd_616142 := by
    simpa [prefixWord, tailWord_616142, baseEnd_616142] using wordTrace_append hprefix tailTrace_616142
  have hstable : (prefixWord ++ tailWord_616142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616142).length < 2 ^ (prefixWord ++ tailWord_616142).sum := by decide
  have hdescent : baseEnd_616142 < baseStart_616142 := by decide
  rcases family_descends (prefixWord ++ tailWord_616142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616159 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 2, 3]
def baseStart_616159 : Nat := 118140960795 + 616159 * 2 ^ 59
def prefixEnd_616159 : Nat := 4983230072969 + 3 ^ 40 * 616159 * 2
def baseEnd_616159 : Nat := 210923817729173339185895

theorem tailTrace_616159 : CollatzResearch.WordTrace tailWord_616159 prefixEnd_616159 210923817729173339185895 := by
  unfold tailWord_616159
  simp only [CollatzResearch.WordTrace]
  refine ⟨22473164974768649424395531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14982109983179099616263687 22473164974768649424395531)
  ·
    refine ⟨33709747462152974136593297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22473164974768649424395531 33709747462152974136593297)
    ·
      refine ⟨25282310596614730602444973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33709747462152974136593297 25282310596614730602444973)
      ·
        refine ⟨9480866473730523975916865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25282310596614730602444973 9480866473730523975916865)
        ·
          refine ⟨7110649855297892981937649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9480866473730523975916865 7110649855297892981937649)
          ·
            refine ⟨5332987391473419736453237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7110649855297892981937649 5332987391473419736453237)
            ·
              refine ⟨499967567950633100292491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5332987391473419736453237 499967567950633100292491)
              ·
                refine ⟨749951351925949650438737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499967567950633100292491 749951351925949650438737)
                ·
                  refine ⟨562463513944462237829053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 749951351925949650438737 562463513944462237829053)
                  ·
                    refine ⟨210923817729173339185895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 562463513944462237829053 210923817729173339185895)
                    ·
                      rfl

theorem cell22_616159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 2, 3].length) (baseStart_616159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616159 prefixEnd_616159 := by exact prefixLift 616159
  have htrace : WordTrace (prefixWord ++ tailWord_616159) baseStart_616159 baseEnd_616159 := by
    simpa [prefixWord, tailWord_616159, baseEnd_616159] using wordTrace_append hprefix tailTrace_616159
  have hstable : (prefixWord ++ tailWord_616159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616159).length < 2 ^ (prefixWord ++ tailWord_616159).sum := by decide
  have hdescent : baseEnd_616159 < baseStart_616159 := by decide
  rcases family_descends (prefixWord ++ tailWord_616159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616200 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 7]
def baseStart_616200 : Nat := 118140960795 + 616200 * 2 ^ 59
def prefixEnd_616200 : Nat := 4983230072969 + 3 ^ 40 * 616200 * 2
def baseEnd_616200 : Nat := 70312617622354299636923

theorem tailTrace_616200 : CollatzResearch.WordTrace tailWord_616200 prefixEnd_616200 70312617622354299636923 := by
  unfold tailWord_616200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11237330183810056713319027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14983106911746742284425369 11237330183810056713319027)
  ·
    refine ⟨16855995275715085069978541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11237330183810056713319027 16855995275715085069978541)
    ·
      refine ⟨6320998228393156901241953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16855995275715085069978541 6320998228393156901241953)
      ·
        refine ⟨4740748671294867675931465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6320998228393156901241953 4740748671294867675931465)
        ·
          refine ⟨3555561503471150756948599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4740748671294867675931465 3555561503471150756948599)
          ·
            refine ⟨5333342255206726135422899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3555561503471150756948599 5333342255206726135422899)
            ·
              refine ⟨8000013382810089203134349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5333342255206726135422899 8000013382810089203134349)
              ·
                refine ⟨3000005018553783451175381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8000013382810089203134349 3000005018553783451175381)
                ·
                  refine ⟨70312617622354299636923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3000005018553783451175381 70312617622354299636923)
                  ·
                    rfl

theorem cell22_616200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_616200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616200 prefixEnd_616200 := by exact prefixLift 616200
  have htrace : WordTrace (prefixWord ++ tailWord_616200) baseStart_616200 baseEnd_616200 := by
    simpa [prefixWord, tailWord_616200, baseEnd_616200] using wordTrace_append hprefix tailTrace_616200
  have hstable : (prefixWord ++ tailWord_616200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616200).length < 2 ^ (prefixWord ++ tailWord_616200).sum := by decide
  have hdescent : baseEnd_616200 < baseStart_616200 := by decide
  rcases family_descends (prefixWord ++ tailWord_616200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616204 : List Nat := [2, 2, 1, 2, 2, 1, 2, 6, 1, 3]
def baseStart_616204 : Nat := 118140960795 + 616204 * 2 ^ 59
def prefixEnd_616204 : Nat := 4983230072969 + 3 ^ 40 * 616204 * 2
def baseEnd_616204 : Nat := 210939222148808221810757

theorem tailTrace_616204 : CollatzResearch.WordTrace tailWord_616204 prefixEnd_616204 210939222148808221810757 := by
  unfold tailWord_616204
  simp only [CollatzResearch.WordTrace]
  refine ⟨11237403129802811054891833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14983204173070414739855777 11237403129802811054891833)
  ·
    refine ⟨8428052347352108291168875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11237403129802811054891833 8428052347352108291168875)
    ·
      refine ⟨12642078521028162436753313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8428052347352108291168875 12642078521028162436753313)
      ·
        refine ⟨9481558890771121827564985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12642078521028162436753313 9481558890771121827564985)
        ·
          refine ⟨7111169168078341370673739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9481558890771121827564985 7111169168078341370673739)
          ·
            refine ⟨10666753752117512056010609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7111169168078341370673739 10666753752117512056010609)
            ·
              refine ⟨8000065314088134042007957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10666753752117512056010609 8000065314088134042007957)
              ·
                refine ⟨375003061597881283219123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8000065314088134042007957 375003061597881283219123)
                ·
                  refine ⟨562504592396821924828685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375003061597881283219123 562504592396821924828685)
                  ·
                    refine ⟨210939222148808221810757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 562504592396821924828685 210939222148808221810757)
                    ·
                      rfl

theorem cell22_616204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_616204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616204 prefixEnd_616204 := by exact prefixLift 616204
  have htrace : WordTrace (prefixWord ++ tailWord_616204) baseStart_616204 baseEnd_616204 := by
    simpa [prefixWord, tailWord_616204, baseEnd_616204] using wordTrace_append hprefix tailTrace_616204
  have hstable : (prefixWord ++ tailWord_616204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616204).length < 2 ^ (prefixWord ++ tailWord_616204).sum := by decide
  have hdescent : baseEnd_616204 < baseStart_616204 := by decide
  rcases family_descends (prefixWord ++ tailWord_616204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616255 : List Nat := [1, 1, 2, 2, 7, 1, 2, 2, 1, 3]
def baseStart_616255 : Nat := 118140960795 + 616255 * 2 ^ 59
def prefixEnd_616255 : Nat := 4983230072969 + 3 ^ 40 * 616255 * 2
def baseEnd_616255 : Nat := 210956680491061088785601

theorem tailTrace_616255 : CollatzResearch.WordTrace tailWord_616255 prefixEnd_616255 210956680491061088785601 := by
  unfold tailWord_616255
  simp only [CollatzResearch.WordTrace]
  refine ⟨22476666382420857819890219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14984444254947238546593479 22476666382420857819890219)
  ·
    refine ⟨33714999573631286729835329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22476666382420857819890219 33714999573631286729835329)
    ·
      refine ⟨25286249680223465047376497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33714999573631286729835329 25286249680223465047376497)
      ·
        refine ⟨18964687260167598785532373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25286249680223465047376497 18964687260167598785532373)
        ·
          refine ⟨444484857660178096535915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 18964687260167598785532373 444484857660178096535915)
          ·
            refine ⟨666727286490267144803873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444484857660178096535915 666727286490267144803873)
            ·
              refine ⟨500045464867700358602905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 666727286490267144803873 500045464867700358602905)
              ·
                refine ⟨375034098650775268952179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500045464867700358602905 375034098650775268952179)
                ·
                  refine ⟨562551147976162903428269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375034098650775268952179 562551147976162903428269)
                  ·
                    refine ⟨210956680491061088785601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 562551147976162903428269 210956680491061088785601)
                    ·
                      rfl

theorem cell22_616255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 1, 3].length) (baseStart_616255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616255 prefixEnd_616255 := by exact prefixLift 616255
  have htrace : WordTrace (prefixWord ++ tailWord_616255) baseStart_616255 baseEnd_616255 := by
    simpa [prefixWord, tailWord_616255, baseEnd_616255] using wordTrace_append hprefix tailTrace_616255
  have hstable : (prefixWord ++ tailWord_616255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616255).length < 2 ^ (prefixWord ++ tailWord_616255).sum := by decide
  have hdescent : baseEnd_616255 < baseStart_616255 := by decide
  rcases family_descends (prefixWord ++ tailWord_616255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616277 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_616277 : Nat := 118140960795 + 616277 * 2 ^ 59
def prefixEnd_616277 : Nat := 4983230072969 + 3 ^ 40 * 616277 * 2
def baseEnd_616277 : Nat := 210964211540660364735533

theorem tailTrace_616277 : CollatzResearch.WordTrace tailWord_616277 prefixEnd_616277 210964211540660364735533 := by
  unfold tailWord_616277
  simp only [CollatzResearch.WordTrace]
  refine ⟨22477468788341155577191085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14984979192227437051460723 22477468788341155577191085)
  ·
    refine ⟨8429050795627933341446657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22477468788341155577191085 8429050795627933341446657)
    ·
      refine ⟨6321788096720950006084993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8429050795627933341446657 6321788096720950006084993)
      ·
        refine ⟨4741341072540712504563745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6321788096720950006084993 4741341072540712504563745)
        ·
          refine ⟨3556005804405534378422809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4741341072540712504563745 3556005804405534378422809)
          ·
            refine ⟨2667004353304150783817107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3556005804405534378422809 2667004353304150783817107)
            ·
              refine ⟨4000506529956226175725661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2667004353304150783817107 4000506529956226175725661)
              ·
                refine ⟨1500189948733584815897123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4000506529956226175725661 1500189948733584815897123)
                ·
                  refine ⟨2250284923100377223845685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500189948733584815897123 2250284923100377223845685)
                  ·
                    refine ⟨210964211540660364735533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2250284923100377223845685 210964211540660364735533)
                    ·
                      rfl

theorem cell22_616277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_616277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616277 prefixEnd_616277 := by exact prefixLift 616277
  have htrace : WordTrace (prefixWord ++ tailWord_616277) baseStart_616277 baseEnd_616277 := by
    simpa [prefixWord, tailWord_616277, baseEnd_616277] using wordTrace_append hprefix tailTrace_616277
  have hstable : (prefixWord ++ tailWord_616277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616277).length < 2 ^ (prefixWord ++ tailWord_616277).sum := by decide
  have hdescent : baseEnd_616277 < baseStart_616277 := by decide
  rcases family_descends (prefixWord ++ tailWord_616277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616328 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 2, 3]
def baseStart_616328 : Nat := 118140960795 + 616328 * 2 ^ 59
def prefixEnd_616328 : Nat := 4983230072969 + 3 ^ 40 * 616328 * 2
def baseEnd_616328 : Nat := 210981669882913231710377

theorem tailTrace_616328 : CollatzResearch.WordTrace tailWord_616328 prefixEnd_616328 210981669882913231710377 := by
  unfold tailWord_616328
  simp only [CollatzResearch.WordTrace]
  refine ⟨11239664455578195643648819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14986219274104260858198425 11239664455578195643648819)
  ·
    refine ⟨16859496683367293465473229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11239664455578195643648819 16859496683367293465473229)
    ·
      refine ⟨6322311256262735049552461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16859496683367293465473229 6322311256262735049552461)
      ·
        refine ⟨2370866721098525643582173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6322311256262735049552461 2370866721098525643582173)
        ·
          refine ⟨889075020411947116343315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2370866721098525643582173 889075020411947116343315)
          ·
            refine ⟨1333612530617920674514973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889075020411947116343315 1333612530617920674514973)
            ·
              refine ⟨500104698981720252943115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1333612530617920674514973 500104698981720252943115)
              ·
                refine ⟨750157048472580379414673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500104698981720252943115 750157048472580379414673)
                ·
                  refine ⟨562617786354435284561005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 750157048472580379414673 562617786354435284561005)
                  ·
                    refine ⟨210981669882913231710377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 562617786354435284561005 210981669882913231710377)
                    ·
                      rfl

theorem cell22_616328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_616328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616328 prefixEnd_616328 := by exact prefixLift 616328
  have htrace : WordTrace (prefixWord ++ tailWord_616328) baseStart_616328 baseEnd_616328 := by
    simpa [prefixWord, tailWord_616328, baseEnd_616328] using wordTrace_append hprefix tailTrace_616328
  have hstable : (prefixWord ++ tailWord_616328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616328).length < 2 ^ (prefixWord ++ tailWord_616328).sum := by decide
  have hdescent : baseEnd_616328 < baseStart_616328 := by decide
  rcases family_descends (prefixWord ++ tailWord_616328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616446 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_616446 : Nat := 118140960795 + 616446 * 2 ^ 59
def prefixEnd_616446 : Nat := 4983230072969 + 3 ^ 40 * 616446 * 2
def baseEnd_616446 : Nat := 211022063694400257260015

theorem tailTrace_616446 : CollatzResearch.WordTrace tailWord_616446 prefixEnd_616446 211022063694400257260015 := by
  unfold tailWord_616446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2810454090591112180011649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14989088483152598293395461 2810454090591112180011649)
  ·
    refine ⟨2107840567943334135008737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2810454090591112180011649 2107840567943334135008737)
    ·
      refine ⟨1580880425957500601256553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2107840567943334135008737 1580880425957500601256553)
      ·
        refine ⟨1185660319468125450942415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1580880425957500601256553 1185660319468125450942415)
        ·
          refine ⟨1778490479202188176413623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1185660319468125450942415 1778490479202188176413623)
          ·
            refine ⟨2667735718803282264620435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778490479202188176413623 2667735718803282264620435)
            ·
              refine ⟨4001603578204923396930653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2667735718803282264620435 4001603578204923396930653)
              ·
                refine ⟨1500601341826846273848995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4001603578204923396930653 1500601341826846273848995)
                ·
                  refine ⟨2250902012740269410773493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500601341826846273848995 2250902012740269410773493)
                  ·
                    refine ⟨211022063694400257260015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2250902012740269410773493 211022063694400257260015)
                    ·
                      rfl

theorem cell22_616446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_616446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616446 prefixEnd_616446 := by exact prefixLift 616446
  have htrace : WordTrace (prefixWord ++ tailWord_616446) baseStart_616446 baseEnd_616446 := by
    simpa [prefixWord, tailWord_616446, baseEnd_616446] using wordTrace_append hprefix tailTrace_616446
  have hstable : (prefixWord ++ tailWord_616446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616446).length < 2 ^ (prefixWord ++ tailWord_616446).sum := by decide
  have hdescent : baseEnd_616446 < baseStart_616446 := by decide
  rcases family_descends (prefixWord ++ tailWord_616446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616459 : List Nat := [1, 1, 1, 1, 6, 1, 5, 6]
def baseStart_616459 : Nat := 118140960795 + 616459 * 2 ^ 59
def prefixEnd_616459 : Nat := 4983230072969 + 3 ^ 40 * 616459 * 2
def baseEnd_616459 : Nat := 23447390428896950742775

theorem tailTrace_616459 : CollatzResearch.WordTrace tailWord_616459 prefixEnd_616459 23447390428896950742775 := by
  unfold tailWord_616459
  simp only [CollatzResearch.WordTrace]
  refine ⟨22484106873681800660316431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14989404582454533773544287 22484106873681800660316431)
  ·
    refine ⟨33726160310522700990474647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22484106873681800660316431 33726160310522700990474647)
    ·
      refine ⟨50589240465784051485711971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33726160310522700990474647 50589240465784051485711971)
      ·
        refine ⟨75883860698676077228567957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50589240465784051485711971 75883860698676077228567957)
        ·
          refine ⟨3557055970250441120089123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75883860698676077228567957 3557055970250441120089123)
          ·
            refine ⟨5335583955375661680133685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3557055970250441120089123 5335583955375661680133685)
            ·
              refine ⟨500210995816468282512533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5335583955375661680133685 500210995816468282512533)
              ·
                refine ⟨23447390428896950742775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 500210995816468282512533 23447390428896950742775)
                ·
                  rfl

theorem cell22_616459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 6].length) (baseStart_616459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616459 prefixEnd_616459 := by exact prefixLift 616459
  have htrace : WordTrace (prefixWord ++ tailWord_616459) baseStart_616459 baseEnd_616459 := by
    simpa [prefixWord, tailWord_616459, baseEnd_616459] using wordTrace_append hprefix tailTrace_616459
  have hstable : (prefixWord ++ tailWord_616459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616459).length < 2 ^ (prefixWord ++ tailWord_616459).sum := by decide
  have hdescent : baseEnd_616459 < baseStart_616459 := by decide
  rcases family_descends (prefixWord ++ tailWord_616459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616510 : List Nat := [4, 2, 1, 3, 3, 1, 2, 6]
def baseStart_616510 : Nat := 118140960795 + 616510 * 2 ^ 59
def prefixEnd_616510 : Nat := 4983230072969 + 3 ^ 40 * 616510 * 2
def baseEnd_616510 : Nat := 23449330244702824851091

theorem tailTrace_616510 : CollatzResearch.WordTrace tailWord_616510 prefixEnd_616510 23449330244702824851091 := by
  unfold tailWord_616510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2810745874562129546302873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14990644664331357580281989 2810745874562129546302873)
  ·
    refine ⟨2108059405921597159727155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2810745874562129546302873 2108059405921597159727155)
    ·
      refine ⟨3162089108882395739590733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2108059405921597159727155 3162089108882395739590733)
      ·
        refine ⟨1185783415830898402346525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3162089108882395739590733 1185783415830898402346525)
        ·
          refine ⟨444668780936586900879947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1185783415830898402346525 444668780936586900879947)
          ·
            refine ⟨667003171404880351319921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444668780936586900879947 667003171404880351319921)
            ·
              refine ⟨500252378553660263489941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667003171404880351319921 500252378553660263489941)
              ·
                refine ⟨23449330244702824851091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 500252378553660263489941 23449330244702824851091)
                ·
                  rfl

theorem cell22_616510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_616510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616510 prefixEnd_616510 := by exact prefixLift 616510
  have htrace : WordTrace (prefixWord ++ tailWord_616510) baseStart_616510 baseEnd_616510 := by
    simpa [prefixWord, tailWord_616510, baseEnd_616510] using wordTrace_append hprefix tailTrace_616510
  have hstable : (prefixWord ++ tailWord_616510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616510).length < 2 ^ (prefixWord ++ tailWord_616510).sum := by decide
  have hdescent : baseEnd_616510 < baseStart_616510 := by decide
  rcases family_descends (prefixWord ++ tailWord_616510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616581 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_616581 : Nat := 118140960795 + 616581 * 2 ^ 59
def prefixEnd_616581 : Nat := 4983230072969 + 3 ^ 40 * 616581 * 2
def baseEnd_616581 : Nat := 211068276953304905134601

theorem tailTrace_616581 : CollatzResearch.WordTrace tailWord_616581 prefixEnd_616581 211068276953304905134601 := by
  unfold tailWord_616581
  simp only [CollatzResearch.WordTrace]
  refine ⟨22488556579239815496257597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14992371052826543664171731 22488556579239815496257597)
  ·
    refine ⟨8433208717214930811096599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22488556579239815496257597 8433208717214930811096599)
    ·
      refine ⟨12649813075822396216644899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8433208717214930811096599 12649813075822396216644899)
      ·
        refine ⟨18974719613733594324967349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12649813075822396216644899 18974719613733594324967349)
        ·
          refine ⟨1778879963787524467965689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18974719613733594324967349 1778879963787524467965689)
          ·
            refine ⟨1334159972840643350974267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1778879963787524467965689 1334159972840643350974267)
            ·
              refine ⟨2001239959260965026461401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1334159972840643350974267 2001239959260965026461401)
              ·
                refine ⟨1500929969445723769846051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2001239959260965026461401 1500929969445723769846051)
                ·
                  refine ⟨2251394954168585654769077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500929969445723769846051 2251394954168585654769077)
                  ·
                    refine ⟨211068276953304905134601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2251394954168585654769077 211068276953304905134601)
                    ·
                      rfl

theorem cell22_616581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_616581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616581 prefixEnd_616581 := by exact prefixLift 616581
  have htrace : WordTrace (prefixWord ++ tailWord_616581) baseStart_616581 baseEnd_616581 := by
    simpa [prefixWord, tailWord_616581, baseEnd_616581] using wordTrace_append hprefix tailTrace_616581
  have hstable : (prefixWord ++ tailWord_616581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616581).length < 2 ^ (prefixWord ++ tailWord_616581).sum := by decide
  have hdescent : baseEnd_616581 < baseStart_616581 := by decide
  rcases family_descends (prefixWord ++ tailWord_616581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616639 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 7]
def baseStart_616639 : Nat := 118140960795 + 616639 * 2 ^ 59
def prefixEnd_616639 : Nat := 4983230072969 + 3 ^ 40 * 616639 * 2
def baseEnd_616639 : Nat := 70362710512870695728141

theorem tailTrace_616639 : CollatzResearch.WordTrace tailWord_616639 prefixEnd_616639 70362710512870695728141 := by
  unfold tailWord_616639
  simp only [CollatzResearch.WordTrace]
  refine ⟨22490672013029691401868971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14993781342019794267912647 22490672013029691401868971)
  ·
    refine ⟨33736008019544537102803457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22490672013029691401868971 33736008019544537102803457)
    ·
      refine ⟨25302006014658402827102593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33736008019544537102803457 25302006014658402827102593)
      ·
        refine ⟨18976504510993802120326945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25302006014658402827102593 18976504510993802120326945)
        ·
          refine ⟨14232378383245351590245209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18976504510993802120326945 14232378383245351590245209)
          ·
            refine ⟨10674283787434013692683907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14232378383245351590245209 10674283787434013692683907)
            ·
              refine ⟨16011425681151020539025861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10674283787434013692683907 16011425681151020539025861)
              ·
                refine ⟨3002142315215816351067349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16011425681151020539025861 3002142315215816351067349)
                ·
                  refine ⟨70362710512870695728141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3002142315215816351067349 70362710512870695728141)
                  ·
                    rfl

theorem cell22_616639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 7].length) (baseStart_616639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616639 prefixEnd_616639 := by exact prefixLift 616639
  have htrace : WordTrace (prefixWord ++ tailWord_616639) baseStart_616639 baseEnd_616639 := by
    simpa [prefixWord, tailWord_616639, baseEnd_616639] using wordTrace_append hprefix tailTrace_616639
  have hstable : (prefixWord ++ tailWord_616639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616639).length < 2 ^ (prefixWord ++ tailWord_616639).sum := by decide
  have hdescent : baseEnd_616639 < baseStart_616639 := by decide
  rcases family_descends (prefixWord ++ tailWord_616639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616673 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 5]
def baseStart_616673 : Nat := 118140960795 + 616673 * 2 ^ 59
def prefixEnd_616673 : Nat := 4983230072969 + 3 ^ 40 * 616673 * 2
def baseEnd_616673 : Nat := 70366590144482443944773

theorem tailTrace_616673 : CollatzResearch.WordTrace tailWord_616673 prefixEnd_616673 70366590144482443944773 := by
  unfold tailWord_616673
  simp only [CollatzResearch.WordTrace]
  refine ⟨22491912094906515208606673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14994608063271010139071115 22491912094906515208606673)
  ·
    refine ⟨16868934071179886406455005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22491912094906515208606673 16868934071179886406455005)
    ·
      refine ⟨6325850276692457402420627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16868934071179886406455005 6325850276692457402420627)
      ·
        refine ⟨9488775415038686103630941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6325850276692457402420627 9488775415038686103630941)
        ·
          refine ⟨3558290780639507288861603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9488775415038686103630941 3558290780639507288861603)
          ·
            refine ⟨5337436170959260933292405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3558290780639507288861603 5337436170959260933292405)
            ·
              refine ⟨500384641027430712496163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5337436170959260933292405 500384641027430712496163)
              ·
                refine ⟨750576961541146068744245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500384641027430712496163 750576961541146068744245)
                ·
                  refine ⟨70366590144482443944773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 750576961541146068744245 70366590144482443944773)
                  ·
                    rfl

theorem cell22_616673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 5].length) (baseStart_616673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616673 prefixEnd_616673 := by exact prefixLift 616673
  have htrace : WordTrace (prefixWord ++ tailWord_616673) baseStart_616673 baseEnd_616673 := by
    simpa [prefixWord, tailWord_616673, baseEnd_616673] using wordTrace_append hprefix tailTrace_616673
  have hstable : (prefixWord ++ tailWord_616673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616673).length < 2 ^ (prefixWord ++ tailWord_616673).sum := by decide
  have hdescent : baseEnd_616673 < baseStart_616673 := by decide
  rcases family_descends (prefixWord ++ tailWord_616673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616769 : List Nat := [1, 2, 5, 2, 2, 2, 2, 2, 4]
def baseStart_616769 : Nat := 118140960795 + 616769 * 2 ^ 59
def prefixEnd_616769 : Nat := 4983230072969 + 3 ^ 40 * 616769 * 2
def baseEnd_616769 : Nat := 70377544398445027144675

theorem tailTrace_616769 : CollatzResearch.WordTrace tailWord_616769 prefixEnd_616769 70377544398445027144675 := by
  unfold tailWord_616769
  simp only [CollatzResearch.WordTrace]
  refine ⟨22495413502558723604101361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14996942335039149069400907 22495413502558723604101361)
  ·
    refine ⟨16871560126919042703076021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22495413502558723604101361 16871560126919042703076021)
    ·
      refine ⟨1581708761898660253413377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16871560126919042703076021 1581708761898660253413377)
      ·
        refine ⟨1186281571423995190060033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1581708761898660253413377 1186281571423995190060033)
        ·
          refine ⟨889711178567996392545025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1186281571423995190060033 889711178567996392545025)
          ·
            refine ⟨667283383925997294408769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 889711178567996392545025 667283383925997294408769)
            ·
              refine ⟨500462537944497970806577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667283383925997294408769 500462537944497970806577)
              ·
                refine ⟨375346903458373478104933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500462537944497970806577 375346903458373478104933)
                ·
                  refine ⟨70377544398445027144675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 375346903458373478104933 70377544398445027144675)
                  ·
                    rfl

theorem cell22_616769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 4].length) (baseStart_616769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616769 prefixEnd_616769 := by exact prefixLift 616769
  have htrace : WordTrace (prefixWord ++ tailWord_616769) baseStart_616769 baseEnd_616769 := by
    simpa [prefixWord, tailWord_616769, baseEnd_616769] using wordTrace_append hprefix tailTrace_616769
  have hstable : (prefixWord ++ tailWord_616769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616769).length < 2 ^ (prefixWord ++ tailWord_616769).sum := by decide
  have hdescent : baseEnd_616769 < baseStart_616769 := by decide
  rcases family_descends (prefixWord ++ tailWord_616769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616776 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_616776 : Nat := 118140960795 + 616776 * 2 ^ 59
def prefixEnd_616776 : Nat := 4983230072969 + 3 ^ 40 * 616776 * 2
def baseEnd_616776 : Nat := 211135029438389396509003

theorem tailTrace_616776 : CollatzResearch.WordTrace tailWord_616776 prefixEnd_616776 211135029438389396509003 := by
  unfold tailWord_616776
  simp only [CollatzResearch.WordTrace]
  refine ⟨11247834406766681899803091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14997112542355575866404121 11247834406766681899803091)
  ·
    refine ⟨16871751610150022849704637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11247834406766681899803091 16871751610150022849704637)
    ·
      refine ⟨6326906853806258568639239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16871751610150022849704637 6326906853806258568639239)
      ·
        refine ⟨9490360280709387852958859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6326906853806258568639239 9490360280709387852958859)
        ·
          refine ⟨14235540421064081779438289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9490360280709387852958859 14235540421064081779438289)
          ·
            refine ⟨10676655315798061334578717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14235540421064081779438289 10676655315798061334578717)
            ·
              refine ⟨4003745743424273000467019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10676655315798061334578717 4003745743424273000467019)
              ·
                refine ⟨6005618615136409500700529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4003745743424273000467019 6005618615136409500700529)
                ·
                  refine ⟨4504213961352307125525397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6005618615136409500700529 4504213961352307125525397)
                  ·
                    refine ⟨211135029438389396509003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4504213961352307125525397 211135029438389396509003)
                    ·
                      rfl

theorem cell22_616776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_616776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616776 prefixEnd_616776 := by exact prefixLift 616776
  have htrace : WordTrace (prefixWord ++ tailWord_616776) baseStart_616776 baseEnd_616776 := by
    simpa [prefixWord, tailWord_616776, baseEnd_616776] using wordTrace_append hprefix tailTrace_616776
  have hstable : (prefixWord ++ tailWord_616776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616776).length < 2 ^ (prefixWord ++ tailWord_616776).sum := by decide
  have hdescent : baseEnd_616776 < baseStart_616776 := by decide
  rcases family_descends (prefixWord ++ tailWord_616776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616868 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 1, 5]
def baseStart_616868 : Nat := 118140960795 + 616868 * 2 ^ 59
def prefixEnd_616868 : Nat := 4983230072969 + 3 ^ 40 * 616868 * 2
def baseEnd_616868 : Nat := 211166522918531823208721

theorem tailTrace_616868 : CollatzResearch.WordTrace tailWord_616868 prefixEnd_616868 211166522918531823208721 := by
  unfold tailWord_616868
  simp only [CollatzResearch.WordTrace]
  refine ⟨11249512164600031755977629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14999349552800042341303505 11249512164600031755977629)
  ·
    refine ⟨4218567061725011908491611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11249512164600031755977629 4218567061725011908491611)
    ·
      refine ⟨6327850592587517862737417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4218567061725011908491611 6327850592587517862737417)
      ·
        refine ⟨4745887944440638397053063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6327850592587517862737417 4745887944440638397053063)
        ·
          refine ⟨7118831916660957595579595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4745887944440638397053063 7118831916660957595579595)
          ·
            refine ⟨10678247874991436393369393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7118831916660957595579595 10678247874991436393369393)
            ·
              refine ⟨8008685906243577295027045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10678247874991436393369393 8008685906243577295027045)
              ·
                refine ⟨1501628607420670742817571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8008685906243577295027045 1501628607420670742817571)
                ·
                  refine ⟨2252442911131006114226357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1501628607420670742817571 2252442911131006114226357)
                  ·
                    refine ⟨211166522918531823208721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2252442911131006114226357 211166522918531823208721)
                    ·
                      rfl

theorem cell22_616868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_616868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616868 prefixEnd_616868 := by exact prefixLift 616868
  have htrace : WordTrace (prefixWord ++ tailWord_616868) baseStart_616868 baseEnd_616868 := by
    simpa [prefixWord, tailWord_616868, baseEnd_616868] using wordTrace_append hprefix tailTrace_616868
  have hstable : (prefixWord ++ tailWord_616868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616868).length < 2 ^ (prefixWord ++ tailWord_616868).sum := by decide
  have hdescent : baseEnd_616868 < baseStart_616868 := by decide
  rcases family_descends (prefixWord ++ tailWord_616868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616872 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 1, 4]
def baseStart_616872 : Nat := 118140960795 + 616872 * 2 ^ 59
def prefixEnd_616872 : Nat := 4983230072969 + 3 ^ 40 * 616872 * 2
def baseEnd_616872 : Nat := 211167892200277146108709

theorem tailTrace_616872 : CollatzResearch.WordTrace tailWord_616872 prefixEnd_616872 211167892200277146108709 := by
  unfold tailWord_616872
  simp only [CollatzResearch.WordTrace]
  refine ⟨11249585110592786097550435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14999446814123714796733913 11249585110592786097550435)
  ·
    refine ⟨16874377665889179146325653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11249585110592786097550435 16874377665889179146325653)
    ·
      refine ⟨790986453088555272484015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16874377665889179146325653 790986453088555272484015)
      ·
        refine ⟨1186479679632832908726023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790986453088555272484015 1186479679632832908726023)
        ·
          refine ⟨1779719519449249363089035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186479679632832908726023 1779719519449249363089035)
          ·
            refine ⟨2669579279173874044633553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1779719519449249363089035 2669579279173874044633553)
            ·
              refine ⟨2002184459380405533475165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2669579279173874044633553 2002184459380405533475165)
              ·
                refine ⟨750819172267652075053187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2002184459380405533475165 750819172267652075053187)
                ·
                  refine ⟨1126228758401478112579781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750819172267652075053187 1126228758401478112579781)
                  ·
                    refine ⟨211167892200277146108709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1126228758401478112579781 211167892200277146108709)
                    ·
                      rfl

theorem cell22_616872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_616872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616872 prefixEnd_616872 := by exact prefixLift 616872
  have htrace : WordTrace (prefixWord ++ tailWord_616872) baseStart_616872 baseEnd_616872 := by
    simpa [prefixWord, tailWord_616872, baseEnd_616872] using wordTrace_append hprefix tailTrace_616872
  have hstable : (prefixWord ++ tailWord_616872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616872).length < 2 ^ (prefixWord ++ tailWord_616872).sum := by decide
  have hdescent : baseEnd_616872 < baseStart_616872 := by decide
  rcases family_descends (prefixWord ++ tailWord_616872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616887 : List Nat := [1, 1, 3, 1, 3, 4, 3, 2, 4]
def baseStart_616887 : Nat := 118140960795 + 616887 * 2 ^ 59
def prefixEnd_616887 : Nat := 4983230072969 + 3 ^ 40 * 616887 * 2
def baseEnd_616887 : Nat := 70391009002274035661221

theorem tailTrace_616887 : CollatzResearch.WordTrace tailWord_616887 prefixEnd_616887 70391009002274035661221 := by
  unfold tailWord_616887
  simp only [CollatzResearch.WordTrace]
  refine ⟨22499717316131229756896915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14999811544087486504597943 22499717316131229756896915)
  ·
    refine ⟨33749575974196844635345373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22499717316131229756896915 33749575974196844635345373)
    ·
      refine ⟨12656090990323816738254515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33749575974196844635345373 12656090990323816738254515)
      ·
        refine ⟨18984136485485725107381773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12656090990323816738254515 18984136485485725107381773)
        ·
          refine ⟨7119051182057146915268165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18984136485485725107381773 7119051182057146915268165)
          ·
            refine ⟨1334822096635715046612781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7119051182057146915268165 1334822096635715046612781)
            ·
              refine ⟨500558286238393142479793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1334822096635715046612781 500558286238393142479793)
              ·
                refine ⟨375418714678794856859845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500558286238393142479793 375418714678794856859845)
                ·
                  refine ⟨70391009002274035661221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 375418714678794856859845 70391009002274035661221)
                  ·
                    rfl

theorem cell22_616887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 4].length) (baseStart_616887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616887 prefixEnd_616887 := by exact prefixLift 616887
  have htrace : WordTrace (prefixWord ++ tailWord_616887) baseStart_616887 baseEnd_616887 := by
    simpa [prefixWord, tailWord_616887, baseEnd_616887] using wordTrace_append hprefix tailTrace_616887
  have hstable : (prefixWord ++ tailWord_616887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616887).length < 2 ^ (prefixWord ++ tailWord_616887).sum := by decide
  have hdescent : baseEnd_616887 < baseStart_616887 := by decide
  rcases family_descends (prefixWord ++ tailWord_616887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616947 : List Nat := [1, 1, 1, 2, 2, 2, 5, 4, 1, 3]
def baseStart_616947 : Nat := 118140960795 + 616947 * 2 ^ 59
def prefixEnd_616947 : Nat := 4983230072969 + 3 ^ 40 * 616947 * 2
def baseEnd_616947 : Nat := 211193566233001950483479

theorem tailTrace_616947 : CollatzResearch.WordTrace tailWord_616947 prefixEnd_616947 211193566233001950483479 := by
  unfold tailWord_616947
  simp only [CollatzResearch.WordTrace]
  refine ⟨22501905695913860004081095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15001270463942573336054063 22501905695913860004081095)
  ·
    refine ⟨33752858543870790006121643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22501905695913860004081095 33752858543870790006121643)
    ·
      refine ⟨50629287815806185009182465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33752858543870790006121643 50629287815806185009182465)
      ·
        refine ⟨37971965861854638756886849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50629287815806185009182465 37971965861854638756886849)
        ·
          refine ⟨28478974396390979067665137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37971965861854638756886849 28478974396390979067665137)
          ·
            refine ⟨21359230797293234300748853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28478974396390979067665137 21359230797293234300748853)
            ·
              refine ⟨2002427887246240715695205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21359230797293234300748853 2002427887246240715695205)
              ·
                refine ⟨375455228858670134192851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2002427887246240715695205 375455228858670134192851)
                ·
                  refine ⟨563182843288005201289277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375455228858670134192851 563182843288005201289277)
                  ·
                    refine ⟨211193566233001950483479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 563182843288005201289277 211193566233001950483479)
                    ·
                      rfl

theorem cell22_616947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 1, 3].length) (baseStart_616947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616947 prefixEnd_616947 := by exact prefixLift 616947
  have htrace : WordTrace (prefixWord ++ tailWord_616947) baseStart_616947 baseEnd_616947 := by
    simpa [prefixWord, tailWord_616947, baseEnd_616947] using wordTrace_append hprefix tailTrace_616947
  have hstable : (prefixWord ++ tailWord_616947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616947).length < 2 ^ (prefixWord ++ tailWord_616947).sum := by decide
  have hdescent : baseEnd_616947 < baseStart_616947 := by decide
  rcases family_descends (prefixWord ++ tailWord_616947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616949 : List Nat := [1, 3, 5, 1, 3, 1, 1, 7]
def baseStart_616949 : Nat := 118140960795 + 616949 * 2 ^ 59
def prefixEnd_616949 : Nat := 4983230072969 + 3 ^ 40 * 616949 * 2
def baseEnd_616949 : Nat := 23466027874874956881497

theorem tailTrace_616949 : CollatzResearch.WordTrace tailWord_616949 prefixEnd_616949 23466027874874956881497 := by
  unfold tailWord_616949
  simp only [CollatzResearch.WordTrace]
  refine ⟨22501978641906614345653901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15001319094604409563769267 22501978641906614345653901)
  ·
    refine ⟨8438241990714980379620213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22501978641906614345653901 8438241990714980379620213)
    ·
      refine ⟨791085186629529410589395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8438241990714980379620213 791085186629529410589395)
      ·
        refine ⟨1186627779944294115884093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791085186629529410589395 1186627779944294115884093)
        ·
          refine ⟨444985417479110293456535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1186627779944294115884093 444985417479110293456535)
          ·
            refine ⟨667478126218665440184803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444985417479110293456535 667478126218665440184803)
            ·
              refine ⟨1001217189327998160277205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667478126218665440184803 1001217189327998160277205)
              ·
                refine ⟨23466027874874956881497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1001217189327998160277205 23466027874874956881497)
                ·
                  rfl

theorem cell22_616949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 7].length) (baseStart_616949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616949 prefixEnd_616949 := by exact prefixLift 616949
  have htrace : WordTrace (prefixWord ++ tailWord_616949) baseStart_616949 baseEnd_616949 := by
    simpa [prefixWord, tailWord_616949, baseEnd_616949] using wordTrace_append hprefix tailTrace_616949
  have hstable : (prefixWord ++ tailWord_616949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616949).length < 2 ^ (prefixWord ++ tailWord_616949).sum := by decide
  have hdescent : baseEnd_616949 < baseStart_616949 := by decide
  rcases family_descends (prefixWord ++ tailWord_616949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_616966 : List Nat := [6, 2, 1, 1, 1, 2, 3, 6]
def baseStart_616966 : Nat := 118140960795 + 616966 * 2 ^ 59
def prefixEnd_616966 : Nat := 4983230072969 + 3 ^ 40 * 616966 * 2
def baseEnd_616966 : Nat := 23466674480143581584269

theorem tailTrace_616966 : CollatzResearch.WordTrace tailWord_616966 prefixEnd_616966 23466674480143581584269 := by
  unfold tailWord_616966
  simp only [CollatzResearch.WordTrace]
  refine ⟨703206208838907070281961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15001732455230017499348501 703206208838907070281961)
  ·
    refine ⟨527404656629180302711471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 703206208838907070281961 527404656629180302711471)
    ·
      refine ⟨791106984943770454067207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527404656629180302711471 791106984943770454067207)
      ·
        refine ⟨1186660477415655681100811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791106984943770454067207 1186660477415655681100811)
        ·
          refine ⟨1779990716123483521651217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186660477415655681100811 1779990716123483521651217)
          ·
            refine ⟨1334993037092612641238413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1779990716123483521651217 1334993037092612641238413)
            ·
              refine ⟨500622388909729740464405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1334993037092612641238413 500622388909729740464405)
              ·
                refine ⟨23466674480143581584269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 500622388909729740464405 23466674480143581584269)
                ·
                  rfl

theorem cell22_616966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_616966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_616966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_616966 prefixEnd_616966 := by exact prefixLift 616966
  have htrace : WordTrace (prefixWord ++ tailWord_616966) baseStart_616966 baseEnd_616966 := by
    simpa [prefixWord, tailWord_616966, baseEnd_616966] using wordTrace_append hprefix tailTrace_616966
  have hstable : (prefixWord ++ tailWord_616966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_616966).length < 2 ^ (prefixWord ++ tailWord_616966).sum := by decide
  have hdescent : baseEnd_616966 < baseStart_616966 := by decide
  rcases family_descends (prefixWord ++ tailWord_616966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617003 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 3, 5]
def baseStart_617003 : Nat := 118140960795 + 617003 * 2 ^ 59
def prefixEnd_617003 : Nat := 4983230072969 + 3 ^ 40 * 617003 * 2
def baseEnd_617003 : Nat := 211212736177436471083307

theorem tailTrace_617003 : CollatzResearch.WordTrace tailWord_617003 prefixEnd_617003 211212736177436471083307 := by
  unfold tailWord_617003
  simp only [CollatzResearch.WordTrace]
  refine ⟨22503948183710981568119663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15002632122473987712079775 22503948183710981568119663)
  ·
    refine ⟨33755922275566472352179495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22503948183710981568119663 33755922275566472352179495)
    ·
      refine ⟨50633883413349708528269243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33755922275566472352179495 50633883413349708528269243)
      ·
        refine ⟨75950825120024562792403865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50633883413349708528269243 75950825120024562792403865)
        ·
          refine ⟨56963118840018422094302899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75950825120024562792403865 56963118840018422094302899)
          ·
            refine ⟨85444678260027633141454349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56963118840018422094302899 85444678260027633141454349)
            ·
              refine ⟨32041754347510362428045381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85444678260027633141454349 32041754347510362428045381)
              ·
                refine ⟨6007828940158192955258509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32041754347510362428045381 6007828940158192955258509)
                ·
                  refine ⟨2252935852559322358221941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6007828940158192955258509 2252935852559322358221941)
                  ·
                    refine ⟨211212736177436471083307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2252935852559322358221941 211212736177436471083307)
                    ·
                      rfl

theorem cell22_617003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_617003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617003 prefixEnd_617003 := by exact prefixLift 617003
  have htrace : WordTrace (prefixWord ++ tailWord_617003) baseStart_617003 baseEnd_617003 := by
    simpa [prefixWord, tailWord_617003, baseEnd_617003] using wordTrace_append hprefix tailTrace_617003
  have hstable : (prefixWord ++ tailWord_617003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617003).length < 2 ^ (prefixWord ++ tailWord_617003).sum := by decide
  have hdescent : baseEnd_617003 < baseStart_617003 := by decide
  rcases family_descends (prefixWord ++ tailWord_617003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617112 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 5]
def baseStart_617112 : Nat := 118140960795 + 617112 * 2 ^ 59
def prefixEnd_617112 : Nat := 4983230072969 + 3 ^ 40 * 617112 * 2
def baseEnd_617112 : Nat := 70416683034998840035991

theorem tailTrace_617112 : CollatzResearch.WordTrace tailWord_617112 prefixEnd_617112 70416683034998840035991 := by
  unfold tailWord_617112
  simp only [CollatzResearch.WordTrace]
  refine ⟨11253961870158046591918795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15005282493544062122558393 11253961870158046591918795)
  ·
    refine ⟨16880942805237069887878193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11253961870158046591918795 16880942805237069887878193)
    ·
      refine ⟨12660707103927802415908645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16880942805237069887878193 12660707103927802415908645)
      ·
        refine ⟨2373882581986462952982871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12660707103927802415908645 2373882581986462952982871)
        ·
          refine ⟨3560823872979694429474307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373882581986462952982871 3560823872979694429474307)
          ·
            refine ⟨5341235809469541644211461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560823872979694429474307 5341235809469541644211461)
            ·
              refine ⟨1001481714275539058289649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5341235809469541644211461 1001481714275539058289649)
              ·
                refine ⟨751111285706654293717237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001481714275539058289649 751111285706654293717237)
                ·
                  refine ⟨70416683034998840035991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 751111285706654293717237 70416683034998840035991)
                  ·
                    rfl

theorem cell22_617112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_617112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617112 prefixEnd_617112 := by exact prefixLift 617112
  have htrace : WordTrace (prefixWord ++ tailWord_617112) baseStart_617112 baseEnd_617112 := by
    simpa [prefixWord, tailWord_617112, baseEnd_617112] using wordTrace_append hprefix tailTrace_617112
  have hstable : (prefixWord ++ tailWord_617112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617112).length < 2 ^ (prefixWord ++ tailWord_617112).sum := by decide
  have hdescent : baseEnd_617112 < baseStart_617112 := by decide
  rcases family_descends (prefixWord ++ tailWord_617112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617116 : List Nat := [2, 2, 3, 2, 2, 2, 1, 4, 1, 3]
def baseStart_617116 : Nat := 118140960795 + 617116 * 2 ^ 59
def prefixEnd_617116 : Nat := 4983230072969 + 3 ^ 40 * 617116 * 2
def baseEnd_617116 : Nat := 211251418386741843007961

theorem tailTrace_617116 : CollatzResearch.WordTrace tailWord_617116 prefixEnd_617116 211251418386741843007961 := by
  unfold tailWord_617116
  simp only [CollatzResearch.WordTrace]
  refine ⟨11254034816150800933491601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15005379754867734577988801 11254034816150800933491601)
  ·
    refine ⟨8440526112113100700118701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11254034816150800933491601 8440526112113100700118701)
    ·
      refine ⟨3165197292042412762544513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8440526112113100700118701 3165197292042412762544513)
      ·
        refine ⟨2373897969031809571908385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3165197292042412762544513 2373897969031809571908385)
        ·
          refine ⟨1780423476773857178931289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2373897969031809571908385 1780423476773857178931289)
          ·
            refine ⟨1335317607580392884198467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1780423476773857178931289 1335317607580392884198467)
            ·
              refine ⟨2002976411370589326297701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335317607580392884198467 2002976411370589326297701)
              ·
                refine ⟨375558077131985498680819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2002976411370589326297701 375558077131985498680819)
                ·
                  refine ⟨563337115697978248021229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375558077131985498680819 563337115697978248021229)
                  ·
                    refine ⟨211251418386741843007961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 563337115697978248021229 211251418386741843007961)
                    ·
                      rfl

theorem cell22_617116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_617116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617116 prefixEnd_617116 := by exact prefixLift 617116
  have htrace : WordTrace (prefixWord ++ tailWord_617116) baseStart_617116 baseEnd_617116 := by
    simpa [prefixWord, tailWord_617116, baseEnd_617116] using wordTrace_append hprefix tailTrace_617116
  have hstable : (prefixWord ++ tailWord_617116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617116).length < 2 ^ (prefixWord ++ tailWord_617116).sum := by decide
  have hdescent : baseEnd_617116 < baseStart_617116 := by decide
  rcases family_descends (prefixWord ++ tailWord_617116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617187 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 1, 6]
def baseStart_617187 : Nat := 118140960795 + 617187 * 2 ^ 59
def prefixEnd_617187 : Nat := 4983230072969 + 3 ^ 40 * 617187 * 2
def baseEnd_617187 : Nat := 211275723137721324482743

theorem tailTrace_617187 : CollatzResearch.WordTrace tailWord_617187 prefixEnd_617187 211275723137721324482743 := by
  unfold tailWord_617187
  simp only [CollatzResearch.WordTrace]
  refine ⟨22510659215044380992817815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15007106143362920661878543 22510659215044380992817815)
  ·
    refine ⟨33765988822566571489226723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22510659215044380992817815 33765988822566571489226723)
    ·
      refine ⟨50648983233849857233840085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33765988822566571489226723 50648983233849857233840085)
      ·
        refine ⟨1187085544543356028918127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 50648983233849857233840085 1187085544543356028918127)
        ·
          refine ⟨1780628316815034043377191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187085544543356028918127 1780628316815034043377191)
          ·
            refine ⟨2670942475222551065065787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780628316815034043377191 2670942475222551065065787)
            ·
              refine ⟨4006413712833826597598681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670942475222551065065787 4006413712833826597598681)
              ·
                refine ⟨3004810284625369948199011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4006413712833826597598681 3004810284625369948199011)
                ·
                  refine ⟨4507215426938054922298517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3004810284625369948199011 4507215426938054922298517)
                  ·
                    refine ⟨211275723137721324482743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4507215426938054922298517 211275723137721324482743)
                    ·
                      rfl

theorem cell22_617187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 6].length) (baseStart_617187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617187 prefixEnd_617187 := by exact prefixLift 617187
  have htrace : WordTrace (prefixWord ++ tailWord_617187) baseStart_617187 baseEnd_617187 := by
    simpa [prefixWord, tailWord_617187, baseEnd_617187] using wordTrace_append hprefix tailTrace_617187
  have hstable : (prefixWord ++ tailWord_617187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617187).length < 2 ^ (prefixWord ++ tailWord_617187).sum := by decide
  have hdescent : baseEnd_617187 < baseStart_617187 := by decide
  rcases family_descends (prefixWord ++ tailWord_617187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617189 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 1, 5]
def baseStart_617189 : Nat := 118140960795 + 617189 * 2 ^ 59
def prefixEnd_617189 : Nat := 4983230072969 + 3 ^ 40 * 617189 * 2
def baseEnd_617189 : Nat := 211276407778593985932737

theorem tailTrace_617189 : CollatzResearch.WordTrace tailWord_617189 prefixEnd_617189 211276407778593985932737 := by
  unfold tailWord_617189
  simp only [CollatzResearch.WordTrace]
  refine ⟨22510732161037135334390621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15007154774024756889593747 22510732161037135334390621)
  ·
    refine ⟨8441524560388925750396483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22510732161037135334390621 8441524560388925750396483)
    ·
      refine ⟨12662286840583388625594725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8441524560388925750396483 12662286840583388625594725)
      ·
        refine ⟨2374178782609385367299011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12662286840583388625594725 2374178782609385367299011)
        ·
          refine ⟨3561268173914078050948517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374178782609385367299011 3561268173914078050948517)
          ·
            refine ⟨667737782608889634552847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3561268173914078050948517 667737782608889634552847)
            ·
              refine ⟨1001606673913334451829271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667737782608889634552847 1001606673913334451829271)
              ·
                refine ⟨1502410010870001677743907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1001606673913334451829271 1502410010870001677743907)
                ·
                  refine ⟨2253615016305002516615861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1502410010870001677743907 2253615016305002516615861)
                  ·
                    refine ⟨211276407778593985932737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2253615016305002516615861 211276407778593985932737)
                    ·
                      rfl

theorem cell22_617189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_617189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617189 prefixEnd_617189 := by exact prefixLift 617189
  have htrace : WordTrace (prefixWord ++ tailWord_617189) baseStart_617189 baseEnd_617189 := by
    simpa [prefixWord, tailWord_617189, baseEnd_617189] using wordTrace_append hprefix tailTrace_617189
  have hstable : (prefixWord ++ tailWord_617189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617189).length < 2 ^ (prefixWord ++ tailWord_617189).sum := by decide
  have hdescent : baseEnd_617189 < baseStart_617189 := by decide
  rcases family_descends (prefixWord ++ tailWord_617189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617200 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_617200 : Nat := 118140960795 + 617200 * 2 ^ 59
def prefixEnd_617200 : Nat := 4983230072969 + 3 ^ 40 * 617200 * 2
def baseEnd_617200 : Nat := 211280173303393623907703

theorem tailTrace_617200 : CollatzResearch.WordTrace tailWord_617200 prefixEnd_617200 211280173303393623907703 := by
  unfold tailWord_617200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255566681998642106520527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15007422242664856142027369 11255566681998642106520527)
  ·
    refine ⟨16883350022997963159780791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11255566681998642106520527 16883350022997963159780791)
    ·
      refine ⟨25325025034496944739671187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16883350022997963159780791 25325025034496944739671187)
      ·
        refine ⟨37987537551745417109506781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25325025034496944739671187 37987537551745417109506781)
        ·
          refine ⟨14245326581904531416065043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37987537551745417109506781 14245326581904531416065043)
          ·
            refine ⟨21367989872856797124097565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14245326581904531416065043 21367989872856797124097565)
            ·
              refine ⟨8012996202321298921536587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21367989872856797124097565 8012996202321298921536587)
              ·
                refine ⟨12019494303481948382304881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8012996202321298921536587 12019494303481948382304881)
                ·
                  refine ⟨9014620727611461286728661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12019494303481948382304881 9014620727611461286728661)
                  ·
                    refine ⟨211280173303393623907703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9014620727611461286728661 211280173303393623907703)
                    ·
                      rfl

theorem cell22_617200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_617200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617200 prefixEnd_617200 := by exact prefixLift 617200
  have htrace : WordTrace (prefixWord ++ tailWord_617200) baseStart_617200 baseEnd_617200 := by
    simpa [prefixWord, tailWord_617200, baseEnd_617200] using wordTrace_append hprefix tailTrace_617200
  have hstable : (prefixWord ++ tailWord_617200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617200).length < 2 ^ (prefixWord ++ tailWord_617200).sum := by decide
  have hdescent : baseEnd_617200 < baseStart_617200 := by decide
  rcases family_descends (prefixWord ++ tailWord_617200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617202 : List Nat := [3, 2, 1, 3, 1, 3, 1, 8]
def baseStart_617202 : Nat := 118140960795 + 617202 * 2 ^ 59
def prefixEnd_617202 : Nat := 4983230072969 + 3 ^ 40 * 617202 * 2
def baseEnd_617202 : Nat := 23475650882696253928633

theorem tailTrace_617202 : CollatzResearch.WordTrace tailWord_617202 prefixEnd_617202 23475650882696253928633 := by
  unfold tailWord_617202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627801577497509638653465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15007470873326692369742573 5627801577497509638653465)
  ·
    refine ⟨4220851183123132228990099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5627801577497509638653465 4220851183123132228990099)
    ·
      refine ⟨6331276774684698343485149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4220851183123132228990099 6331276774684698343485149)
      ·
        refine ⟨2374228790506761878806931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6331276774684698343485149 2374228790506761878806931)
        ·
          refine ⟨3561343185760142818210397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374228790506761878806931 3561343185760142818210397)
          ·
            refine ⟨1335503694660053556828899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3561343185760142818210397 1335503694660053556828899)
            ·
              refine ⟨2003255541990080335243349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335503694660053556828899 2003255541990080335243349)
              ·
                refine ⟨23475650882696253928633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2003255541990080335243349 23475650882696253928633)
                ·
                  rfl

theorem cell22_617202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_617202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617202 prefixEnd_617202 := by exact prefixLift 617202
  have htrace : WordTrace (prefixWord ++ tailWord_617202) baseStart_617202 baseEnd_617202 := by
    simpa [prefixWord, tailWord_617202, baseEnd_617202] using wordTrace_append hprefix tailTrace_617202
  have hstable : (prefixWord ++ tailWord_617202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617202).length < 2 ^ (prefixWord ++ tailWord_617202).sum := by decide
  have hdescent : baseEnd_617202 < baseStart_617202 := by decide
  rcases family_descends (prefixWord ++ tailWord_617202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617215 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 1, 8]
def baseStart_617215 : Nat := 118140960795 + 617215 * 2 ^ 59
def prefixEnd_617215 : Nat := 4983230072969 + 3 ^ 40 * 617215 * 2
def baseEnd_617215 : Nat := 211285308109938584782657

theorem tailTrace_617215 : CollatzResearch.WordTrace tailWord_617215 prefixEnd_617215 211285308109938584782657 := by
  unfold tailWord_617215
  simp only [CollatzResearch.WordTrace]
  refine ⟨22511680458942941774837099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15007786972628627849891399 22511680458942941774837099)
  ·
    refine ⟨33767520688414412662255649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22511680458942941774837099 33767520688414412662255649)
    ·
      refine ⟨25325640516310809496691737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33767520688414412662255649 25325640516310809496691737)
      ·
        refine ⟨18994230387233107122518803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25325640516310809496691737 18994230387233107122518803)
        ·
          refine ⟨28491345580849660683778205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18994230387233107122518803 28491345580849660683778205)
          ·
            refine ⟨10684254592818622756416827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28491345580849660683778205 10684254592818622756416827)
            ·
              refine ⟨16026381889227934134625241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10684254592818622756416827 16026381889227934134625241)
              ·
                refine ⟨12019786416920950600968931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16026381889227934134625241 12019786416920950600968931)
                ·
                  refine ⟨18029679625381425901453397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12019786416920950600968931 18029679625381425901453397)
                  ·
                    refine ⟨211285308109938584782657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18029679625381425901453397 211285308109938584782657)
                    ·
                      rfl

theorem cell22_617215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_617215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617215 prefixEnd_617215 := by exact prefixLift 617215
  have htrace : WordTrace (prefixWord ++ tailWord_617215) baseStart_617215 baseEnd_617215 := by
    simpa [prefixWord, tailWord_617215, baseEnd_617215] using wordTrace_append hprefix tailTrace_617215
  have hstable : (prefixWord ++ tailWord_617215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617215).length < 2 ^ (prefixWord ++ tailWord_617215).sum := by decide
  have hdescent : baseEnd_617215 < baseStart_617215 := by decide
  rcases family_descends (prefixWord ++ tailWord_617215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617324 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 4, 3]
def baseStart_617324 : Nat := 118140960795 + 617324 * 2 ^ 59
def prefixEnd_617324 : Nat := 4983230072969 + 3 ^ 40 * 617324 * 2
def baseEnd_617324 : Nat := 211322621037498633807323

theorem tailTrace_617324 : CollatzResearch.WordTrace tailWord_617324 prefixEnd_617324 211322621037498633807323 := by
  unfold tailWord_617324
  simp only [CollatzResearch.WordTrace]
  refine ⟨11257828007774026695277513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15010437343698702260370017 11257828007774026695277513)
  ·
    refine ⟨8443371005830520021458135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11257828007774026695277513 8443371005830520021458135)
    ·
      refine ⟨12665056508745780032187203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8443371005830520021458135 12665056508745780032187203)
      ·
        refine ⟨18997584763118670048280805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12665056508745780032187203 18997584763118670048280805)
        ·
          refine ⟨3562047143084750634052651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18997584763118670048280805 3562047143084750634052651)
          ·
            refine ⟨5343070714627125951078977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3562047143084750634052651 5343070714627125951078977)
            ·
              refine ⟨4007303035970344463309233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5343070714627125951078977 4007303035970344463309233)
              ·
                refine ⟨3005477276977758347481925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4007303035970344463309233 3005477276977758347481925)
                ·
                  refine ⟨563526989433329690152861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3005477276977758347481925 563526989433329690152861)
                  ·
                    refine ⟨211322621037498633807323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 563526989433329690152861 211322621037498633807323)
                    ·
                      rfl

theorem cell22_617324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_617324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617324 prefixEnd_617324 := by exact prefixLift 617324
  have htrace : WordTrace (prefixWord ++ tailWord_617324) baseStart_617324 baseEnd_617324 := by
    simpa [prefixWord, tailWord_617324, baseEnd_617324] using wordTrace_append hprefix tailTrace_617324
  have hstable : (prefixWord ++ tailWord_617324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617324).length < 2 ^ (prefixWord ++ tailWord_617324).sum := by decide
  have hdescent : baseEnd_617324 < baseStart_617324 := by decide
  rcases family_descends (prefixWord ++ tailWord_617324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617337 : List Nat := [1, 2, 1, 3, 2, 4, 9]
def baseStart_617337 : Nat := 118140960795 + 617337 * 2 ^ 59
def prefixEnd_617337 : Nat := 4983230072969 + 3 ^ 40 * 617337 * 2
def baseEnd_617337 : Nat := 7826928563080404934529

theorem tailTrace_617337 : CollatzResearch.WordTrace tailWord_617337 prefixEnd_617337 7826928563080404934529 := by
  unfold tailWord_617337
  simp only [CollatzResearch.WordTrace]
  refine ⟨22516130164500956610778265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15010753443000637740518843 22516130164500956610778265)
  ·
    refine ⟨16887097623375717458083699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22516130164500956610778265 16887097623375717458083699)
    ·
      refine ⟨25330646435063576187125549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16887097623375717458083699 25330646435063576187125549)
      ·
        refine ⟨9498992413148841070172081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25330646435063576187125549 9498992413148841070172081)
        ·
          refine ⟨7124244309861630802629061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9498992413148841070172081 7124244309861630802629061)
          ·
            refine ⟨1335795808099055775492949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7124244309861630802629061 1335795808099055775492949)
            ·
              refine ⟨7826928563080404934529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1335795808099055775492949 7826928563080404934529)
              ·
                rfl

theorem cell22_617337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 9].length) (baseStart_617337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617337 prefixEnd_617337 := by exact prefixLift 617337
  have htrace : WordTrace (prefixWord ++ tailWord_617337) baseStart_617337 baseEnd_617337 := by
    simpa [prefixWord, tailWord_617337, baseEnd_617337] using wordTrace_append hprefix tailTrace_617337
  have hstable : (prefixWord ++ tailWord_617337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617337).length < 2 ^ (prefixWord ++ tailWord_617337).sum := by decide
  have hdescent : baseEnd_617337 < baseStart_617337 := by decide
  rcases family_descends (prefixWord ++ tailWord_617337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617341 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_617341 : Nat := 118140960795 + 617341 * 2 ^ 59
def prefixEnd_617341 : Nat := 4983230072969 + 3 ^ 40 * 617341 * 2
def baseEnd_617341 : Nat := 211328440484916256132271

theorem tailTrace_617341 : CollatzResearch.WordTrace tailWord_617341 prefixEnd_617341 211328440484916256132271 := by
  unfold tailWord_617341
  simp only [CollatzResearch.WordTrace]
  refine ⟨22516276056486465293923877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15010850704324310195949251 22516276056486465293923877)
  ·
    refine ⟨4221801760591212242610727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22516276056486465293923877 4221801760591212242610727)
    ·
      refine ⟨6332702640886818363916091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4221801760591212242610727 6332702640886818363916091)
      ·
        refine ⟨9499053961330227545874137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6332702640886818363916091 9499053961330227545874137)
        ·
          refine ⟨7124290470997670659405603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9499053961330227545874137 7124290470997670659405603)
          ·
            refine ⟨10686435706496505989108405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7124290470997670659405603 10686435706496505989108405)
            ·
              refine ⟨1001853347484047436478913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10686435706496505989108405 1001853347484047436478913)
              ·
                refine ⟨751390010613035577359185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001853347484047436478913 751390010613035577359185)
                ·
                  refine ⟨563542507959776683019389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 751390010613035577359185 563542507959776683019389)
                  ·
                    refine ⟨211328440484916256132271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 563542507959776683019389 211328440484916256132271)
                    ·
                      rfl

theorem cell22_617341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_617341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617341 prefixEnd_617341 := by exact prefixLift 617341
  have htrace : WordTrace (prefixWord ++ tailWord_617341) baseStart_617341 baseEnd_617341 := by
    simpa [prefixWord, tailWord_617341, baseEnd_617341] using wordTrace_append hprefix tailTrace_617341
  have hstable : (prefixWord ++ tailWord_617341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617341).length < 2 ^ (prefixWord ++ tailWord_617341).sum := by decide
  have hdescent : baseEnd_617341 < baseStart_617341 := by decide
  rcases family_descends (prefixWord ++ tailWord_617341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617416 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 5]
def baseStart_617416 : Nat := 118140960795 + 617416 * 2 ^ 59
def prefixEnd_617416 : Nat := 4983230072969 + 3 ^ 40 * 617416 * 2
def baseEnd_617416 : Nat := 70451371505880353502347

theorem tailTrace_617416 : CollatzResearch.WordTrace tailWord_617416 prefixEnd_617416 70451371505880353502347 := by
  unfold tailWord_617416
  simp only [CollatzResearch.WordTrace]
  refine ⟨11259505765607376551452051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15012674354143168735269401 11259505765607376551452051)
  ·
    refine ⟨16889258648411064827178077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11259505765607376551452051 16889258648411064827178077)
    ·
      refine ⟨6333471993154149310191779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16889258648411064827178077 6333471993154149310191779)
      ·
        refine ⟨9500207989731223965287669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6333471993154149310191779 9500207989731223965287669)
        ·
          refine ⟨890644499037302246745719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9500207989731223965287669 890644499037302246745719)
          ·
            refine ⟨1335966748555953370118579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890644499037302246745719 1335966748555953370118579)
            ·
              refine ⟨2003950122833930055177869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335966748555953370118579 2003950122833930055177869)
              ·
                refine ⟨751481296062723770691701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2003950122833930055177869 751481296062723770691701)
                ·
                  refine ⟨70451371505880353502347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 751481296062723770691701 70451371505880353502347)
                  ·
                    rfl

theorem cell22_617416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_617416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617416 prefixEnd_617416 := by exact prefixLift 617416
  have htrace : WordTrace (prefixWord ++ tailWord_617416) baseStart_617416 baseEnd_617416 := by
    simpa [prefixWord, tailWord_617416, baseEnd_617416] using wordTrace_append hprefix tailTrace_617416
  have hstable : (prefixWord ++ tailWord_617416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617416).length < 2 ^ (prefixWord ++ tailWord_617416).sum := by decide
  have hdescent : baseEnd_617416 < baseStart_617416 := by decide
  rcases family_descends (prefixWord ++ tailWord_617416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617454 : List Nat := [4, 1, 2, 1, 5, 1, 2, 2, 1, 3]
def baseStart_617454 : Nat := 118140960795 + 617454 * 2 ^ 59
def prefixEnd_617454 : Nat := 4983230072969 + 3 ^ 40 * 617454 * 2
def baseEnd_617454 : Nat := 211367122694221628056925

theorem tailTrace_617454 : CollatzResearch.WordTrace tailWord_617454 prefixEnd_617454 211367122694221628056925 := by
  unfold tailWord_617454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2815049688134635699098427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15013598336718057061858277 2815049688134635699098427)
  ·
    refine ⟨4222574532201953548647641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2815049688134635699098427 4222574532201953548647641)
    ·
      refine ⟨3166930899151465161485731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4222574532201953548647641 3166930899151465161485731)
      ·
        refine ⟨4750396348727197742228597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3166930899151465161485731 4750396348727197742228597)
        ·
          refine ⟨445349657693174788333931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4750396348727197742228597 445349657693174788333931)
          ·
            refine ⟨668024486539762182500897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445349657693174788333931 668024486539762182500897)
            ·
              refine ⟨501018364904821636875673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668024486539762182500897 501018364904821636875673)
              ·
                refine ⟨375763773678616227656755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501018364904821636875673 375763773678616227656755)
                ·
                  refine ⟨563645660517924341485133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375763773678616227656755 563645660517924341485133)
                  ·
                    refine ⟨211367122694221628056925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 563645660517924341485133 211367122694221628056925)
                    ·
                      rfl

theorem cell22_617454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_617454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617454 prefixEnd_617454 := by exact prefixLift 617454
  have htrace : WordTrace (prefixWord ++ tailWord_617454) baseStart_617454 baseEnd_617454 := by
    simpa [prefixWord, tailWord_617454, baseEnd_617454] using wordTrace_append hprefix tailTrace_617454
  have hstable : (prefixWord ++ tailWord_617454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617454).length < 2 ^ (prefixWord ++ tailWord_617454).sum := by decide
  have hdescent : baseEnd_617454 < baseStart_617454 := by decide
  rcases family_descends (prefixWord ++ tailWord_617454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617611 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 6, 3]
def baseStart_617611 : Nat := 118140960795 + 617611 * 2 ^ 59
def prefixEnd_617611 : Nat := 4983230072969 + 3 ^ 40 * 617611 * 2
def baseEnd_617611 : Nat := 211420867002725551881443

theorem tailTrace_617611 : CollatzResearch.WordTrace tailWord_617611 prefixEnd_617611 211420867002725551881443 := by
  unfold tailWord_617611
  simp only [CollatzResearch.WordTrace]
  refine ⟨22526123765508301406252687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15017415843672200937501791 22526123765508301406252687)
  ·
    refine ⟨33789185648262452109379031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22526123765508301406252687 33789185648262452109379031)
    ·
      refine ⟨50683778472393678164068547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33789185648262452109379031 50683778472393678164068547)
      ·
        refine ⟨76025667708590517246102821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50683778472393678164068547 76025667708590517246102821)
        ·
          refine ⟨14254812695360721983644279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76025667708590517246102821 14254812695360721983644279)
          ·
            refine ⟨21382219043041082975466419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14254812695360721983644279 21382219043041082975466419)
            ·
              refine ⟨32073328564561624463199629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21382219043041082975466419 32073328564561624463199629)
              ·
                refine ⟨12027498211710609173699861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32073328564561624463199629 12027498211710609173699861)
                ·
                  refine ⟨563788978673934805017181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12027498211710609173699861 563788978673934805017181)
                  ·
                    refine ⟨211420867002725551881443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 563788978673934805017181 211420867002725551881443)
                    ·
                      rfl

theorem cell22_617611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 3].length) (baseStart_617611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617611 prefixEnd_617611 := by exact prefixLift 617611
  have htrace : WordTrace (prefixWord ++ tailWord_617611) baseStart_617611 baseEnd_617611 := by
    simpa [prefixWord, tailWord_617611, baseEnd_617611] using wordTrace_append hprefix tailTrace_617611
  have hstable : (prefixWord ++ tailWord_617611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617611).length < 2 ^ (prefixWord ++ tailWord_617611).sum := by decide
  have hdescent : baseEnd_617611 < baseStart_617611 := by decide
  rcases family_descends (prefixWord ++ tailWord_617611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617645 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_617645 : Nat := 118140960795 + 617645 * 2 ^ 59
def prefixEnd_617645 : Nat := 4983230072969 + 3 ^ 40 * 617645 * 2
def baseEnd_617645 : Nat := 211432505897560796531339

theorem tailTrace_617645 : CollatzResearch.WordTrace tailWord_617645 prefixEnd_617645 211432505897560796531339 := by
  unfold tailWord_617645
  simp only [CollatzResearch.WordTrace]
  refine ⟨22527363847385125212990389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15018242564923416808660259 22527363847385125212990389)
  ·
    refine ⟨2111940360692355488717849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22527363847385125212990389 2111940360692355488717849)
    ·
      refine ⟨1583955270519266616538387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2111940360692355488717849 1583955270519266616538387)
      ·
        refine ⟨2375932905778899924807581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1583955270519266616538387 2375932905778899924807581)
        ·
          refine ⟨890974839667087471802843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2375932905778899924807581 890974839667087471802843)
          ·
            refine ⟨1336462259500631207704265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890974839667087471802843 1336462259500631207704265)
            ·
              refine ⟨1002346694625473405778199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1336462259500631207704265 1002346694625473405778199)
              ·
                refine ⟨1503520041938210108667299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002346694625473405778199 1503520041938210108667299)
                ·
                  refine ⟨2255280062907315163000949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1503520041938210108667299 2255280062907315163000949)
                  ·
                    refine ⟨211432505897560796531339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2255280062907315163000949 211432505897560796531339)
                    ·
                      rfl

theorem cell22_617645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_617645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617645 prefixEnd_617645 := by exact prefixLift 617645
  have htrace : WordTrace (prefixWord ++ tailWord_617645) baseStart_617645 baseEnd_617645 := by
    simpa [prefixWord, tailWord_617645, baseEnd_617645] using wordTrace_append hprefix tailTrace_617645
  have hstable : (prefixWord ++ tailWord_617645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617645).length < 2 ^ (prefixWord ++ tailWord_617645).sum := by decide
  have hdescent : baseEnd_617645 < baseStart_617645 := by decide
  rcases family_descends (prefixWord ++ tailWord_617645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617660 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 2, 4]
def baseStart_617660 : Nat := 118140960795 + 617660 * 2 ^ 59
def prefixEnd_617660 : Nat := 4983230072969 + 3 ^ 40 * 617660 * 2
def baseEnd_617660 : Nat := 211437640704105757406293

theorem tailTrace_617660 : CollatzResearch.WordTrace tailWord_617660 prefixEnd_617660 211437640704105757406293 := by
  unfold tailWord_617660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11263955471165391387393217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15018607294887188516524289 11263955471165391387393217)
  ·
    refine ⟨8447966603374043540544913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11263955471165391387393217 8447966603374043540544913)
    ·
      refine ⟨6335974952530532655408685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8447966603374043540544913 6335974952530532655408685)
      ·
        refine ⟨2375990607198949745778257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6335974952530532655408685 2375990607198949745778257)
        ·
          refine ⟨1781992955399212309333693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2375990607198949745778257 1781992955399212309333693)
          ·
            refine ⟨668247358274704616000135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1781992955399212309333693 668247358274704616000135)
            ·
              refine ⟨1002371037412056924000203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668247358274704616000135 1002371037412056924000203)
              ·
                refine ⟨1503556556118085386000305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002371037412056924000203 1503556556118085386000305)
                ·
                  refine ⟨1127667417088564039500229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1503556556118085386000305 1127667417088564039500229)
                  ·
                    refine ⟨211437640704105757406293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1127667417088564039500229 211437640704105757406293)
                    ·
                      rfl

theorem cell22_617660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_617660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617660 prefixEnd_617660 := by exact prefixLift 617660
  have htrace : WordTrace (prefixWord ++ tailWord_617660) baseStart_617660 baseEnd_617660 := by
    simpa [prefixWord, tailWord_617660, baseEnd_617660] using wordTrace_append hprefix tailTrace_617660
  have hstable : (prefixWord ++ tailWord_617660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617660).length < 2 ^ (prefixWord ++ tailWord_617660).sum := by decide
  have hdescent : baseEnd_617660 < baseStart_617660 := by decide
  rcases family_descends (prefixWord ++ tailWord_617660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617666 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_617666 : Nat := 118140960795 + 617666 * 2 ^ 59
def prefixEnd_617666 : Nat := 4983230072969 + 3 ^ 40 * 617666 * 2
def baseEnd_617666 : Nat := 211439694626723741756275

theorem tailTrace_617666 : CollatzResearch.WordTrace tailWord_617666 prefixEnd_617666 211439694626723741756275 := by
  unfold tailWord_617666
  simp only [CollatzResearch.WordTrace]
  refine ⟨5632032445077261449876213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15018753186872697199669901 5632032445077261449876213)
  ·
    refine ⟨528003041725993260925895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5632032445077261449876213 528003041725993260925895)
    ·
      refine ⟨792004562588989891388843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 528003041725993260925895 792004562588989891388843)
      ·
        refine ⟨1188006843883484837083265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792004562588989891388843 1188006843883484837083265)
        ·
          refine ⟨891005132912613627812449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1188006843883484837083265 891005132912613627812449)
          ·
            refine ⟨668253849684460220859337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 891005132912613627812449 668253849684460220859337)
            ·
              refine ⟨501190387263345165644503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668253849684460220859337 501190387263345165644503)
              ·
                refine ⟨751785580895017748466755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501190387263345165644503 751785580895017748466755)
                ·
                  refine ⟨1127678371342526622700133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751785580895017748466755 1127678371342526622700133)
                  ·
                    refine ⟨211439694626723741756275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1127678371342526622700133 211439694626723741756275)
                    ·
                      rfl

theorem cell22_617666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_617666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617666 prefixEnd_617666 := by exact prefixLift 617666
  have htrace : WordTrace (prefixWord ++ tailWord_617666) baseStart_617666 baseEnd_617666 := by
    simpa [prefixWord, tailWord_617666, baseEnd_617666] using wordTrace_append hprefix tailTrace_617666
  have hstable : (prefixWord ++ tailWord_617666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617666).length < 2 ^ (prefixWord ++ tailWord_617666).sum := by decide
  have hdescent : baseEnd_617666 < baseStart_617666 := by decide
  rcases family_descends (prefixWord ++ tailWord_617666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617724 : List Nat := [2, 2, 2, 1, 5, 2, 1, 3, 1, 3]
def baseStart_617724 : Nat := 118140960795 + 617724 * 2 ^ 59
def prefixEnd_617724 : Nat := 4983230072969 + 3 ^ 40 * 617724 * 2
def baseEnd_617724 : Nat := 211459549212030923806097

theorem tailTrace_617724 : CollatzResearch.WordTrace tailWord_617724 prefixEnd_617724 211459549212030923806097 := by
  unfold tailWord_617724
  simp only [CollatzResearch.WordTrace]
  refine ⟨11265122607049460852558113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15020163476065947803410817 11265122607049460852558113)
  ·
    refine ⟨8448841955287095639418585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11265122607049460852558113 8448841955287095639418585)
    ·
      refine ⟨6336631466465321729563939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8448841955287095639418585 6336631466465321729563939)
      ·
        refine ⟨9504947199697982594345909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6336631466465321729563939 9504947199697982594345909)
        ·
          refine ⟨891088799971685868219929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9504947199697982594345909 891088799971685868219929)
          ·
            refine ⟨668316599978764401164947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 891088799971685868219929 668316599978764401164947)
            ·
              refine ⟨1002474899968146601747421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668316599978764401164947 1002474899968146601747421)
              ·
                refine ⟨375928087488054975655283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1002474899968146601747421 375928087488054975655283)
                ·
                  refine ⟨563892131232082463482925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375928087488054975655283 563892131232082463482925)
                  ·
                    refine ⟨211459549212030923806097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 563892131232082463482925 211459549212030923806097)
                    ·
                      rfl

theorem cell22_617724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_617724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617724 prefixEnd_617724 := by exact prefixLift 617724
  have htrace : WordTrace (prefixWord ++ tailWord_617724) baseStart_617724 baseEnd_617724 := by
    simpa [prefixWord, tailWord_617724, baseEnd_617724] using wordTrace_append hprefix tailTrace_617724
  have hstable : (prefixWord ++ tailWord_617724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617724).length < 2 ^ (prefixWord ++ tailWord_617724).sum := by decide
  have hdescent : baseEnd_617724 < baseStart_617724 := by decide
  rcases family_descends (prefixWord ++ tailWord_617724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617733 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 1, 4]
def baseStart_617733 : Nat := 118140960795 + 617733 * 2 ^ 59
def prefixEnd_617733 : Nat := 4983230072969 + 3 ^ 40 * 617733 * 2
def baseEnd_617733 : Nat := 211462630095957900331069

theorem tailTrace_617733 : CollatzResearch.WordTrace tailWord_617733 prefixEnd_617733 211462630095957900331069 := by
  unfold tailWord_617733
  simp only [CollatzResearch.WordTrace]
  refine ⟨22530573471066316242193853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15020382314044210828129235 22530573471066316242193853)
  ·
    refine ⟨8448965051649868590822695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22530573471066316242193853 8448965051649868590822695)
    ·
      refine ⟨12673447577474802886234043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8448965051649868590822695 12673447577474802886234043)
      ·
        refine ⟨19010171366212204329351065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12673447577474802886234043 19010171366212204329351065)
        ·
          refine ⟨14257628524659153247013299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19010171366212204329351065 14257628524659153247013299)
          ·
            refine ⟨21386442786988729870519949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14257628524659153247013299 21386442786988729870519949)
            ·
              refine ⟨8019916045120773701444981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21386442786988729870519949 8019916045120773701444981)
              ·
                refine ⟨751867129230072534510467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8019916045120773701444981 751867129230072534510467)
                ·
                  refine ⟨1127800693845108801765701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 751867129230072534510467 1127800693845108801765701)
                  ·
                    refine ⟨211462630095957900331069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1127800693845108801765701 211462630095957900331069)
                    ·
                      rfl

theorem cell22_617733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_617733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617733 prefixEnd_617733 := by exact prefixLift 617733
  have htrace : WordTrace (prefixWord ++ tailWord_617733) baseStart_617733 baseEnd_617733 := by
    simpa [prefixWord, tailWord_617733, baseEnd_617733] using wordTrace_append hprefix tailTrace_617733
  have hstable : (prefixWord ++ tailWord_617733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617733).length < 2 ^ (prefixWord ++ tailWord_617733).sum := by decide
  have hdescent : baseEnd_617733 < baseStart_617733 := by decide
  rcases family_descends (prefixWord ++ tailWord_617733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617776 : List Nat := [2, 1, 1, 1, 2, 2, 3, 10]
def baseStart_617776 : Nat := 118140960795 + 617776 * 2 ^ 59
def prefixEnd_617776 : Nat := 4983230072969 + 3 ^ 40 * 617776 * 2
def baseEnd_617776 : Nat := 23497483319413346833993

theorem tailTrace_617776 : CollatzResearch.WordTrace tailWord_617776 prefixEnd_617776 23497483319413346833993 := by
  unfold tailWord_617776
  simp only [CollatzResearch.WordTrace]
  refine ⟨11266070904955267293004591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15021427873273689724006121 11266070904955267293004591)
  ·
    refine ⟨16899106357432900939506887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11266070904955267293004591 16899106357432900939506887)
    ·
      refine ⟨25348659536149351409260331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16899106357432900939506887 25348659536149351409260331)
      ·
        refine ⟨38022989304224027113890497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25348659536149351409260331 38022989304224027113890497)
        ·
          refine ⟨28517241978168020335417873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38022989304224027113890497 28517241978168020335417873)
          ·
            refine ⟨21387931483626015251563405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28517241978168020335417873 21387931483626015251563405)
            ·
              refine ⟨8020474306359755719336277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21387931483626015251563405 8020474306359755719336277)
              ·
                refine ⟨23497483319413346833993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8020474306359755719336277 23497483319413346833993)
                ·
                  rfl

theorem cell22_617776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 10].length) (baseStart_617776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617776 prefixEnd_617776 := by exact prefixLift 617776
  have htrace : WordTrace (prefixWord ++ tailWord_617776) baseStart_617776 baseEnd_617776 := by
    simpa [prefixWord, tailWord_617776, baseEnd_617776] using wordTrace_append hprefix tailTrace_617776
  have hstable : (prefixWord ++ tailWord_617776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617776).length < 2 ^ (prefixWord ++ tailWord_617776).sum := by decide
  have hdescent : baseEnd_617776 < baseStart_617776 := by decide
  rcases family_descends (prefixWord ++ tailWord_617776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617780 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_617780 : Nat := 118140960795 + 617780 * 2 ^ 59
def prefixEnd_617780 : Nat := 4983230072969 + 3 ^ 40 * 617780 * 2
def baseEnd_617780 : Nat := 211478719156465444405925

theorem tailTrace_617780 : CollatzResearch.WordTrace tailWord_617780 prefixEnd_617780 211478719156465444405925 := by
  unfold tailWord_617780
  simp only [CollatzResearch.WordTrace]
  refine ⟨11266143850948021634577397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15021525134597362179436529 11266143850948021634577397)
  ·
    refine ⟨1056200986026377028241631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11266143850948021634577397 1056200986026377028241631)
    ·
      refine ⟨1584301479039565542362447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1056200986026377028241631 1584301479039565542362447)
      ·
        refine ⟨2376452218559348313543671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1584301479039565542362447 2376452218559348313543671)
        ·
          refine ⟨3564678327839022470315507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2376452218559348313543671 3564678327839022470315507)
          ·
            refine ⟨5347017491758533705473261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3564678327839022470315507 5347017491758533705473261)
            ·
              refine ⟨2005131559409450139552473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5347017491758533705473261 2005131559409450139552473)
              ·
                refine ⟨1503848669557087604664355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2005131559409450139552473 1503848669557087604664355)
                ·
                  refine ⟨2255773004335631406996533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1503848669557087604664355 2255773004335631406996533)
                  ·
                    refine ⟨211478719156465444405925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2255773004335631406996533 211478719156465444405925)
                    ·
                      rfl

theorem cell22_617780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_617780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617780 prefixEnd_617780 := by exact prefixLift 617780
  have htrace : WordTrace (prefixWord ++ tailWord_617780) baseStart_617780 baseEnd_617780 := by
    simpa [prefixWord, tailWord_617780, baseEnd_617780] using wordTrace_append hprefix tailTrace_617780
  have hstable : (prefixWord ++ tailWord_617780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617780).length < 2 ^ (prefixWord ++ tailWord_617780).sum := by decide
  have hdescent : baseEnd_617780 < baseStart_617780 := by decide
  rcases family_descends (prefixWord ++ tailWord_617780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617793 : List Nat := [1, 2, 5, 2, 1, 11]
def baseStart_617793 : Nat := 118140960795 + 617793 * 2 ^ 59
def prefixEnd_617793 : Nat := 4983230072969 + 3 ^ 40 * 617793 * 2
def baseEnd_617793 : Nat := 2610903324964663504085

theorem tailTrace_617793 : CollatzResearch.WordTrace tailWord_617793 prefixEnd_617793 2610903324964663504085 := by
  unfold tailWord_617793
  simp only [CollatzResearch.WordTrace]
  refine ⟨22532761850848946489378033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15021841233899297659585355 22532761850848946489378033)
  ·
    refine ⟨16899571388136709867033525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22532761850848946489378033 16899571388136709867033525)
    ·
      refine ⟨1584334817637816550034393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16899571388136709867033525 1584334817637816550034393)
      ·
        refine ⟨1188251113228362412525795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1584334817637816550034393 1188251113228362412525795)
        ·
          refine ⟨1782376669842543618788693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188251113228362412525795 1782376669842543618788693)
          ·
            refine ⟨2610903324964663504085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1782376669842543618788693 2610903324964663504085)
            ·
              rfl

theorem cell22_617793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 11].length) (baseStart_617793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617793 prefixEnd_617793 := by exact prefixLift 617793
  have htrace : WordTrace (prefixWord ++ tailWord_617793) baseStart_617793 baseEnd_617793 := by
    simpa [prefixWord, tailWord_617793, baseEnd_617793] using wordTrace_append hprefix tailTrace_617793
  have hstable : (prefixWord ++ tailWord_617793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617793).length < 2 ^ (prefixWord ++ tailWord_617793).sum := by decide
  have hdescent : baseEnd_617793 < baseStart_617793 := by decide
  rcases family_descends (prefixWord ++ tailWord_617793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617853 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_617853 : Nat := 118140960795 + 617853 * 2 ^ 59
def prefixEnd_617853 : Nat := 4983230072969 + 3 ^ 40 * 617853 * 2
def baseEnd_617853 : Nat := 211503708548317587330701

theorem tailTrace_617853 : CollatzResearch.WordTrace tailWord_617853 prefixEnd_617853 211503708548317587330701 := by
  unfold tailWord_617853
  simp only [CollatzResearch.WordTrace]
  refine ⟨22534950230631576736562213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15023300153754384491041475 22534950230631576736562213)
  ·
    refine ⟨4225303168243420638105415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22534950230631576736562213 4225303168243420638105415)
    ·
      refine ⟨6337954752365130957158123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4225303168243420638105415 6337954752365130957158123)
      ·
        refine ⟨9506932128547696435737185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6337954752365130957158123 9506932128547696435737185)
        ·
          refine ⟨7130199096410772326802889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9506932128547696435737185 7130199096410772326802889)
          ·
            refine ⟨5347649322308079245102167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7130199096410772326802889 5347649322308079245102167)
            ·
              refine ⟨8021473983462118867653251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5347649322308079245102167 8021473983462118867653251)
              ·
                refine ⟨12032210975193178301479877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8021473983462118867653251 12032210975193178301479877)
                ·
                  refine ⟨2256039557848720931527477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12032210975193178301479877 2256039557848720931527477)
                  ·
                    refine ⟨211503708548317587330701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2256039557848720931527477 211503708548317587330701)
                    ·
                      rfl

theorem cell22_617853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_617853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617853 prefixEnd_617853 := by exact prefixLift 617853
  have htrace : WordTrace (prefixWord ++ tailWord_617853) baseStart_617853 baseEnd_617853 := by
    simpa [prefixWord, tailWord_617853, baseEnd_617853] using wordTrace_append hprefix tailTrace_617853
  have hstable : (prefixWord ++ tailWord_617853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617853).length < 2 ^ (prefixWord ++ tailWord_617853).sum := by decide
  have hdescent : baseEnd_617853 < baseStart_617853 := by decide
  rcases family_descends (prefixWord ++ tailWord_617853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_617943 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 2, 7]
def baseStart_617943 : Nat := 118140960795 + 617943 * 2 ^ 59
def prefixEnd_617943 : Nat := 4983230072969 + 3 ^ 40 * 617943 * 2
def baseEnd_617943 : Nat := 211534517387587352580425

theorem tailTrace_617943 : CollatzResearch.WordTrace tailWord_617943 prefixEnd_617943 211534517387587352580425 := by
  unfold tailWord_617943
  simp only [CollatzResearch.WordTrace]
  refine ⟨22538232800305522107338483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15025488533537014738225655 22538232800305522107338483)
  ·
    refine ⟨33807349200458283161007725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22538232800305522107338483 33807349200458283161007725)
    ·
      refine ⟨12677755950171856185377897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33807349200458283161007725 12677755950171856185377897)
      ·
        refine ⟨9508316962628892139033423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12677755950171856185377897 9508316962628892139033423)
        ·
          refine ⟨14262475443943338208550135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9508316962628892139033423 14262475443943338208550135)
          ·
            refine ⟨21393713165915007312825203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14262475443943338208550135 21393713165915007312825203)
            ·
              refine ⟨32090569748872510969237805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21393713165915007312825203 32090569748872510969237805)
              ·
                refine ⟨12033963655827191613464177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32090569748872510969237805 12033963655827191613464177)
                ·
                  refine ⟨9025472741870393710098133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12033963655827191613464177 9025472741870393710098133)
                  ·
                    refine ⟨211534517387587352580425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9025472741870393710098133 211534517387587352580425)
                    ·
                      rfl

theorem cell22_617943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_617943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_617943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_617943 prefixEnd_617943 := by exact prefixLift 617943
  have htrace : WordTrace (prefixWord ++ tailWord_617943) baseStart_617943 baseEnd_617943 := by
    simpa [prefixWord, tailWord_617943, baseEnd_617943] using wordTrace_append hprefix tailTrace_617943
  have hstable : (prefixWord ++ tailWord_617943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_617943).length < 2 ^ (prefixWord ++ tailWord_617943).sum := by decide
  have hdescent : baseEnd_617943 < baseStart_617943 := by decide
  rcases family_descends (prefixWord ++ tailWord_617943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618035 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 6]
def baseStart_618035 : Nat := 118140960795 + 618035 * 2 ^ 59
def prefixEnd_618035 : Nat := 4983230072969 + 3 ^ 40 * 618035 * 2
def baseEnd_618035 : Nat := 70522003622576593093381

theorem tailTrace_618035 : CollatzResearch.WordTrace tailWord_618035 prefixEnd_618035 70522003622576593093381 := by
  unfold tailWord_618035
  simp only [CollatzResearch.WordTrace]
  refine ⟨22541588315972221819687559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15027725543981481213125039 22541588315972221819687559)
  ·
    refine ⟨33812382473958332729531339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22541588315972221819687559 33812382473958332729531339)
    ·
      refine ⟨50718573710937499094297009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33812382473958332729531339 50718573710937499094297009)
      ·
        refine ⟨38038930283203124320722757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50718573710937499094297009 38038930283203124320722757)
        ·
          refine ⟨7132299428100585810135517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38038930283203124320722757 7132299428100585810135517)
          ·
            refine ⟨2674612285537719678800819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7132299428100585810135517 2674612285537719678800819)
            ·
              refine ⟨4011918428306579518201229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2674612285537719678800819 4011918428306579518201229)
              ·
                refine ⟨1504469410614967319325461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4011918428306579518201229 1504469410614967319325461)
                ·
                  refine ⟨70522003622576593093381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1504469410614967319325461 70522003622576593093381)
                  ·
                    rfl

theorem cell22_618035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 6].length) (baseStart_618035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618035 prefixEnd_618035 := by exact prefixLift 618035
  have htrace : WordTrace (prefixWord ++ tailWord_618035) baseStart_618035 baseEnd_618035 := by
    simpa [prefixWord, tailWord_618035, baseEnd_618035] using wordTrace_append hprefix tailTrace_618035
  have hstable : (prefixWord ++ tailWord_618035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618035).length < 2 ^ (prefixWord ++ tailWord_618035).sum := by decide
  have hdescent : baseEnd_618035 < baseStart_618035 := by decide
  rcases family_descends (prefixWord ++ tailWord_618035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618065 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_618065 : Nat := 118140960795 + 618065 * 2 ^ 59
def prefixEnd_618065 : Nat := 4983230072969 + 3 ^ 40 * 618065 * 2
def baseEnd_618065 : Nat := 211576280480819701030051

theorem tailTrace_618065 : CollatzResearch.WordTrace tailWord_618065 prefixEnd_618065 211576280480819701030051 := by
  unfold tailWord_618065
  simp only [CollatzResearch.WordTrace]
  refine ⟨22542682505863536943279649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15028455003909024628853099 22542682505863536943279649)
  ·
    refine ⟨16907011879397652707459737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22542682505863536943279649 16907011879397652707459737)
    ·
      refine ⟨12680258909548239530594803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16907011879397652707459737 12680258909548239530594803)
      ·
        refine ⟨19020388364322359295892205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12680258909548239530594803 19020388364322359295892205)
        ·
          refine ⟨7132645636620884735959577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19020388364322359295892205 7132645636620884735959577)
          ·
            refine ⟨5349484227465663551969683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7132645636620884735959577 5349484227465663551969683)
            ·
              refine ⟨8024226341198495327954525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5349484227465663551969683 8024226341198495327954525)
              ·
                refine ⟨3009084877949435747982947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8024226341198495327954525 3009084877949435747982947)
                ·
                  refine ⟨4513627316924153621974421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3009084877949435747982947 4513627316924153621974421)
                  ·
                    refine ⟨211576280480819701030051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4513627316924153621974421 211576280480819701030051)
                    ·
                      rfl

theorem cell22_618065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_618065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618065 prefixEnd_618065 := by exact prefixLift 618065
  have htrace : WordTrace (prefixWord ++ tailWord_618065) baseStart_618065 baseEnd_618065 := by
    simpa [prefixWord, tailWord_618065, baseEnd_618065] using wordTrace_append hprefix tailTrace_618065
  have hstable : (prefixWord ++ tailWord_618065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618065).length < 2 ^ (prefixWord ++ tailWord_618065).sum := by decide
  have hdescent : baseEnd_618065 < baseStart_618065 := by decide
  rcases family_descends (prefixWord ++ tailWord_618065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618101 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 2, 3]
def baseStart_618101 : Nat := 118140960795 + 618101 * 2 ^ 59
def prefixEnd_618101 : Nat := 4983230072969 + 3 ^ 40 * 618101 * 2
def baseEnd_618101 : Nat := 211588604016527607129941

theorem tailTrace_618101 : CollatzResearch.WordTrace tailWord_618101 prefixEnd_618101 211588604016527607129941 := by
  unfold tailWord_618101
  simp only [CollatzResearch.WordTrace]
  refine ⟨22543995533733115091590157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15029330355822076727726771 22543995533733115091590157)
  ·
    refine ⟨8453998325149918159346309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22543995533733115091590157 8453998325149918159346309)
    ·
      refine ⟨1585124685965609654877433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8453998325149918159346309 1585124685965609654877433)
      ·
        refine ⟨1188843514474207241158075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1585124685965609654877433 1188843514474207241158075)
        ·
          refine ⟨1783265271711310861737113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188843514474207241158075 1783265271711310861737113)
          ·
            refine ⟨1337448953783483146302835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1783265271711310861737113 1337448953783483146302835)
            ·
              refine ⟨2006173430675224719454253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337448953783483146302835 2006173430675224719454253)
              ·
                refine ⟨752315036503209269795345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2006173430675224719454253 752315036503209269795345)
                ·
                  refine ⟨564236277377406952346509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 752315036503209269795345 564236277377406952346509)
                  ·
                    refine ⟨211588604016527607129941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 564236277377406952346509 211588604016527607129941)
                    ·
                      rfl

theorem cell22_618101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_618101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618101 prefixEnd_618101 := by exact prefixLift 618101
  have htrace : WordTrace (prefixWord ++ tailWord_618101) baseStart_618101 baseEnd_618101 := by
    simpa [prefixWord, tailWord_618101, baseEnd_618101] using wordTrace_append hprefix tailTrace_618101
  have hstable : (prefixWord ++ tailWord_618101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618101).length < 2 ^ (prefixWord ++ tailWord_618101).sum := by decide
  have hdescent : baseEnd_618101 < baseStart_618101 := by decide
  rcases family_descends (prefixWord ++ tailWord_618101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618112 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 5, 3]
def baseStart_618112 : Nat := 118140960795 + 618112 * 2 ^ 59
def prefixEnd_618112 : Nat := 4983230072969 + 3 ^ 40 * 618112 * 2
def baseEnd_618112 : Nat := 211592369541327245104907

theorem tailTrace_618112 : CollatzResearch.WordTrace tailWord_618112 prefixEnd_618112 211592369541327245104907 := by
  unfold tailWord_618112
  simp only [CollatzResearch.WordTrace]
  refine ⟨11272198368346631985120295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15029597824462175980160393 11272198368346631985120295)
  ·
    refine ⟨16908297552519947977680443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11272198368346631985120295 16908297552519947977680443)
    ·
      refine ⟨25362446328779921966520665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16908297552519947977680443 25362446328779921966520665)
      ·
        refine ⟨19021834746584941474890499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25362446328779921966520665 19021834746584941474890499)
        ·
          refine ⟨28532752119877412212335749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19021834746584941474890499 28532752119877412212335749)
          ·
            refine ⟨5349891022477014789812953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28532752119877412212335749 5349891022477014789812953)
            ·
              refine ⟨4012418266857761092359715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5349891022477014789812953 4012418266857761092359715)
              ·
                refine ⟨6018627400286641638539573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4012418266857761092359715 6018627400286641638539573)
                ·
                  refine ⟨564246318776872653613085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6018627400286641638539573 564246318776872653613085)
                  ·
                    refine ⟨211592369541327245104907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 564246318776872653613085 211592369541327245104907)
                    ·
                      rfl

theorem cell22_618112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5, 3].length) (baseStart_618112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618112 prefixEnd_618112 := by exact prefixLift 618112
  have htrace : WordTrace (prefixWord ++ tailWord_618112) baseStart_618112 baseEnd_618112 := by
    simpa [prefixWord, tailWord_618112, baseEnd_618112] using wordTrace_append hprefix tailTrace_618112
  have hstable : (prefixWord ++ tailWord_618112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618112).length < 2 ^ (prefixWord ++ tailWord_618112).sum := by decide
  have hdescent : baseEnd_618112 < baseStart_618112 := by decide
  rcases family_descends (prefixWord ++ tailWord_618112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618219 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 2, 3]
def baseStart_618219 : Nat := 118140960795 + 618219 * 2 ^ 59
def prefixEnd_618219 : Nat := 4983230072969 + 3 ^ 40 * 618219 * 2
def baseEnd_618219 : Nat := 211628997828014632679579

theorem tailTrace_618219 : CollatzResearch.WordTrace tailWord_618219 prefixEnd_618219 211628997828014632679579 := by
  unfold tailWord_618219
  simp only [CollatzResearch.WordTrace]
  refine ⟨22548299347305621244385711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15032199564870414162923807 22548299347305621244385711)
  ·
    refine ⟨33822449020958431866578567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22548299347305621244385711 33822449020958431866578567)
    ·
      refine ⟨50733673531437647799867851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33822449020958431866578567 50733673531437647799867851)
      ·
        refine ⟨76100510297156471699801777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50733673531437647799867851 76100510297156471699801777)
        ·
          refine ⟨57075382722867353774851333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76100510297156471699801777 57075382722867353774851333)
          ·
            refine ⟨10701634260537628832784625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57075382722867353774851333 10701634260537628832784625)
            ·
              refine ⟨8026225695403221624588469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10701634260537628832784625 8026225695403221624588469)
              ·
                refine ⟨752458658944052027305169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8026225695403221624588469 752458658944052027305169)
                ·
                  refine ⟨564343994208039020478877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 752458658944052027305169 564343994208039020478877)
                  ·
                    refine ⟨211628997828014632679579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 564343994208039020478877 211628997828014632679579)
                    ·
                      rfl

theorem cell22_618219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 3].length) (baseStart_618219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618219 prefixEnd_618219 := by exact prefixLift 618219
  have htrace : WordTrace (prefixWord ++ tailWord_618219) baseStart_618219 baseEnd_618219 := by
    simpa [prefixWord, tailWord_618219, baseEnd_618219] using wordTrace_append hprefix tailTrace_618219
  have hstable : (prefixWord ++ tailWord_618219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618219).length < 2 ^ (prefixWord ++ tailWord_618219).sum := by decide
  have hdescent : baseEnd_618219 < baseStart_618219 := by decide
  rcases family_descends (prefixWord ++ tailWord_618219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618371 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 4, 3]
def baseStart_618371 : Nat := 118140960795 + 618371 * 2 ^ 59
def prefixEnd_618371 : Nat := 4983230072969 + 3 ^ 40 * 618371 * 2
def baseEnd_618371 : Nat := 211681030534336902879113

theorem tailTrace_618371 : CollatzResearch.WordTrace tailWord_618371 prefixEnd_618371 211681030534336902879113 := by
  unfold tailWord_618371
  simp only [CollatzResearch.WordTrace]
  refine ⟨22553843242754951203918967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15035895495169967469279311 22553843242754951203918967)
  ·
    refine ⟨33830764864132426805878451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22553843242754951203918967 33830764864132426805878451)
    ·
      refine ⟨50746147296198640208817677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33830764864132426805878451 50746147296198640208817677)
      ·
        refine ⟨19029805236074490078306629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50746147296198640208817677 19029805236074490078306629)
        ·
          refine ⟨3568088481763966889682493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19029805236074490078306629 3568088481763966889682493)
          ·
            refine ⟨1338033180661487583630935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3568088481763966889682493 1338033180661487583630935)
            ·
              refine ⟨2007049770992231375446403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338033180661487583630935 2007049770992231375446403)
              ·
                refine ⟨3010574656488347063169605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007049770992231375446403 3010574656488347063169605)
                ·
                  refine ⟨564482748091565074344301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3010574656488347063169605 564482748091565074344301)
                  ·
                    refine ⟨211681030534336902879113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 564482748091565074344301 211681030534336902879113)
                    ·
                      rfl

theorem cell22_618371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 3].length) (baseStart_618371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618371 prefixEnd_618371 := by exact prefixLift 618371
  have htrace : WordTrace (prefixWord ++ tailWord_618371) baseStart_618371 baseEnd_618371 := by
    simpa [prefixWord, tailWord_618371, baseEnd_618371] using wordTrace_append hprefix tailTrace_618371
  have hstable : (prefixWord ++ tailWord_618371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618371).length < 2 ^ (prefixWord ++ tailWord_618371).sum := by decide
  have hdescent : baseEnd_618371 < baseStart_618371 := by decide
  rcases family_descends (prefixWord ++ tailWord_618371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618386 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_618386 : Nat := 118140960795 + 618386 * 2 ^ 59
def prefixEnd_618386 : Nat := 4983230072969 + 3 ^ 40 * 618386 * 2
def baseEnd_618386 : Nat := 211686165340881863754067

theorem tailTrace_618386 : CollatzResearch.WordTrace tailWord_618386 prefixEnd_618386 211686165340881863754067 := by
  unfold tailWord_618386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5638597584425152191428753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15036260225133739177143341 5638597584425152191428753)
  ·
    refine ⟨4228948188318864143571565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5638597584425152191428753 4228948188318864143571565)
    ·
      refine ⟨1585855570619574053839337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4228948188318864143571565 1585855570619574053839337)
      ·
        refine ⟨1189391677964680540379503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1585855570619574053839337 1189391677964680540379503)
        ·
          refine ⟨1784087516947020810569255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1189391677964680540379503 1784087516947020810569255)
          ·
            refine ⟨2676131275420531215853883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784087516947020810569255 2676131275420531215853883)
            ·
              refine ⟨4014196913130796823780825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2676131275420531215853883 4014196913130796823780825)
              ·
                refine ⟨3010647684848097617835619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4014196913130796823780825 3010647684848097617835619)
                ·
                  refine ⟨4515971527272146426753429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010647684848097617835619 4515971527272146426753429)
                  ·
                    refine ⟨211686165340881863754067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4515971527272146426753429 211686165340881863754067)
                    ·
                      rfl

theorem cell22_618386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_618386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618386 prefixEnd_618386 := by exact prefixLift 618386
  have htrace : WordTrace (prefixWord ++ tailWord_618386) baseStart_618386 baseEnd_618386 := by
    simpa [prefixWord, tailWord_618386, baseEnd_618386] using wordTrace_append hprefix tailTrace_618386
  have hstable : (prefixWord ++ tailWord_618386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618386).length < 2 ^ (prefixWord ++ tailWord_618386).sum := by decide
  have hdescent : baseEnd_618386 < baseStart_618386 := by decide
  rcases family_descends (prefixWord ++ tailWord_618386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618388 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_618388 : Nat := 118140960795 + 618388 * 2 ^ 59
def prefixEnd_618388 : Nat := 4983230072969 + 3 ^ 40 * 618388 * 2
def baseEnd_618388 : Nat := 211686849981754525204061

theorem tailTrace_618388 : CollatzResearch.WordTrace tailWord_618388 prefixEnd_618388 211686849981754525204061 := by
  unfold tailWord_618388
  simp only [CollatzResearch.WordTrace]
  refine ⟨11277231641846681553643909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15036308855795575404858545 11277231641846681553643909)
  ·
    refine ⟨2114480932846252791308233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11277231641846681553643909 2114480932846252791308233)
    ·
      refine ⟨1585860699634689593481175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2114480932846252791308233 1585860699634689593481175)
      ·
        refine ⟨2378791049452034390221763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1585860699634689593481175 2378791049452034390221763)
        ·
          refine ⟨3568186574178051585332645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378791049452034390221763 3568186574178051585332645)
          ·
            refine ⟨669034982658384672249871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3568186574178051585332645 669034982658384672249871)
            ·
              refine ⟨1003552473987577008374807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669034982658384672249871 1003552473987577008374807)
              ·
                refine ⟨1505328710981365512562211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003552473987577008374807 1505328710981365512562211)
                ·
                  refine ⟨2257993066472048268843317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1505328710981365512562211 2257993066472048268843317)
                  ·
                    refine ⟨211686849981754525204061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2257993066472048268843317 211686849981754525204061)
                    ·
                      rfl

theorem cell22_618388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_618388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618388 prefixEnd_618388 := by exact prefixLift 618388
  have htrace : WordTrace (prefixWord ++ tailWord_618388) baseStart_618388 baseEnd_618388 := by
    simpa [prefixWord, tailWord_618388, baseEnd_618388] using wordTrace_append hprefix tailTrace_618388
  have hstable : (prefixWord ++ tailWord_618388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618388).length < 2 ^ (prefixWord ++ tailWord_618388).sum := by decide
  have hdescent : baseEnd_618388 < baseStart_618388 := by decide
  rcases family_descends (prefixWord ++ tailWord_618388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618401 : List Nat := [1, 2, 3, 4, 2, 1, 1, 8]
def baseStart_618401 : Nat := 118140960795 + 618401 * 2 ^ 59
def prefixEnd_618401 : Nat := 4983230072969 + 3 ^ 40 * 618401 * 2
def baseEnd_618401 : Nat := 23521255571936313847669

theorem tailTrace_618401 : CollatzResearch.WordTrace tailWord_618401 prefixEnd_618401 23521255571936313847669 := by
  unfold tailWord_618401
  simp only [CollatzResearch.WordTrace]
  refine ⟨22554937432646266327511057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15036624955097510885007371 22554937432646266327511057)
  ·
    refine ⟨16916203074484699745633293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22554937432646266327511057 16916203074484699745633293)
    ·
      refine ⟨6343576152931762404612485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16916203074484699745633293 6343576152931762404612485)
      ·
        refine ⟨1189420528674705450864841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6343576152931762404612485 1189420528674705450864841)
        ·
          refine ⟨892065396506029088148631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1189420528674705450864841 892065396506029088148631)
          ·
            refine ⟨1338098094759043632222947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892065396506029088148631 1338098094759043632222947)
            ·
              refine ⟨2007147142138565448334421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338098094759043632222947 2007147142138565448334421)
              ·
                refine ⟨23521255571936313847669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2007147142138565448334421 23521255571936313847669)
                ·
                  rfl

theorem cell22_618401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 8].length) (baseStart_618401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618401 prefixEnd_618401 := by exact prefixLift 618401
  have htrace : WordTrace (prefixWord ++ tailWord_618401) baseStart_618401 baseEnd_618401 := by
    simpa [prefixWord, tailWord_618401, baseEnd_618401] using wordTrace_append hprefix tailTrace_618401
  have hstable : (prefixWord ++ tailWord_618401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618401).length < 2 ^ (prefixWord ++ tailWord_618401).sum := by decide
  have hdescent : baseEnd_618401 < baseStart_618401 := by decide
  rcases family_descends (prefixWord ++ tailWord_618401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618420 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_618420 : Nat := 118140960795 + 618420 * 2 ^ 59
def prefixEnd_618420 : Nat := 4983230072969 + 3 ^ 40 * 618420 * 2
def baseEnd_618420 : Nat := 211697804235717108403963

theorem tailTrace_618420 : CollatzResearch.WordTrace tailWord_618420 prefixEnd_618420 211697804235717108403963 := by
  unfold tailWord_618420
  simp only [CollatzResearch.WordTrace]
  refine ⟨11277815209788716286226357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15037086946384955048301809 11277815209788716286226357)
  ·
    refine ⟨1057295175917692151833721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11277815209788716286226357 1057295175917692151833721)
    ·
      refine ⟨792971381938269113875291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1057295175917692151833721 792971381938269113875291)
      ·
        refine ⟨1189457072907403670812937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792971381938269113875291 1189457072907403670812937)
        ·
          refine ⟨892092804680552753109703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1189457072907403670812937 892092804680552753109703)
          ·
            refine ⟨1338139207020829129664555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892092804680552753109703 1338139207020829129664555)
            ·
              refine ⟨2007208810531243694496833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338139207020829129664555 2007208810531243694496833)
              ·
                refine ⟨1505406607898432770872625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2007208810531243694496833 1505406607898432770872625)
                ·
                  refine ⟨1129054955923824578154469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1505406607898432770872625 1129054955923824578154469)
                  ·
                    refine ⟨211697804235717108403963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1129054955923824578154469 211697804235717108403963)
                    ·
                      rfl

theorem cell22_618420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_618420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618420 prefixEnd_618420 := by exact prefixLift 618420
  have htrace : WordTrace (prefixWord ++ tailWord_618420) baseStart_618420 baseEnd_618420 := by
    simpa [prefixWord, tailWord_618420, baseEnd_618420] using wordTrace_append hprefix tailTrace_618420
  have hstable : (prefixWord ++ tailWord_618420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618420).length < 2 ^ (prefixWord ++ tailWord_618420).sum := by decide
  have hdescent : baseEnd_618420 < baseStart_618420 := by decide
  rcases family_descends (prefixWord ++ tailWord_618420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618446 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_618446 : Nat := 118140960795 + 618446 * 2 ^ 59
def prefixEnd_618446 : Nat := 4983230072969 + 3 ^ 40 * 618446 * 2
def baseEnd_618446 : Nat := 70568901522353902417961

theorem tailTrace_618446 : CollatzResearch.WordTrace tailWord_618446 prefixEnd_618446 70568901522353902417961 := by
  unfold tailWord_618446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2819572339685404876612399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15037719144988826008599461 2819572339685404876612399)
  ·
    refine ⟨4229358509528107314918599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2819572339685404876612399 4229358509528107314918599)
    ·
      refine ⟨6344037764292160972377899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4229358509528107314918599 6344037764292160972377899)
      ·
        refine ⟨9516056646438241458566849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6344037764292160972377899 9516056646438241458566849)
        ·
          refine ⟨7137042484828681093925137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9516056646438241458566849 7137042484828681093925137)
          ·
            refine ⟨5352781863621510820443853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7137042484828681093925137 5352781863621510820443853)
            ·
              refine ⟨2007293198858066557666445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5352781863621510820443853 2007293198858066557666445)
              ·
                refine ⟨752734949571774959124917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2007293198858066557666445 752734949571774959124917)
                ·
                  refine ⟨70568901522353902417961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 752734949571774959124917 70568901522353902417961)
                  ·
                    rfl

theorem cell22_618446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_618446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618446 prefixEnd_618446 := by exact prefixLift 618446
  have htrace : WordTrace (prefixWord ++ tailWord_618446) baseStart_618446 baseEnd_618446 := by
    simpa [prefixWord, tailWord_618446, baseEnd_618446] using wordTrace_append hprefix tailTrace_618446
  have hstable : (prefixWord ++ tailWord_618446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618446).length < 2 ^ (prefixWord ++ tailWord_618446).sum := by decide
  have hdescent : baseEnd_618446 < baseStart_618446 := by decide
  rcases family_descends (prefixWord ++ tailWord_618446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618476 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_618476 : Nat := 118140960795 + 618476 * 2 ^ 59
def prefixEnd_618476 : Nat := 4983230072969 + 3 ^ 40 * 618476 * 2
def baseEnd_618476 : Nat := 211716974180151629003791

theorem tailTrace_618476 : CollatzResearch.WordTrace tailWord_618476 prefixEnd_618476 211716974180151629003791 := by
  unfold tailWord_618476
  simp only [CollatzResearch.WordTrace]
  refine ⟨11278836453687277068245641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15038448604916369424327521 11278836453687277068245641)
  ·
    refine ⟨8459127340265457801184231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11278836453687277068245641 8459127340265457801184231)
    ·
      refine ⟨12688691010398186701776347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8459127340265457801184231 12688691010398186701776347)
      ·
        refine ⟨19033036515597280052664521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12688691010398186701776347 19033036515597280052664521)
        ·
          refine ⟨14274777386697960039498391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19033036515597280052664521 14274777386697960039498391)
          ·
            refine ⟨21412166080046940059247587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14274777386697960039498391 21412166080046940059247587)
            ·
              refine ⟨32118249120070410088871381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21412166080046940059247587 32118249120070410088871381)
              ·
                refine ⟨752771463751650236457923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32118249120070410088871381 752771463751650236457923)
                ·
                  refine ⟨1129157195627475354686885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752771463751650236457923 1129157195627475354686885)
                  ·
                    refine ⟨211716974180151629003791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1129157195627475354686885 211716974180151629003791)
                    ·
                      rfl

theorem cell22_618476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_618476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618476 prefixEnd_618476 := by exact prefixLift 618476
  have htrace : WordTrace (prefixWord ++ tailWord_618476) baseStart_618476 baseEnd_618476 := by
    simpa [prefixWord, tailWord_618476, baseEnd_618476] using wordTrace_append hprefix tailTrace_618476
  have hstable : (prefixWord ++ tailWord_618476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618476).length < 2 ^ (prefixWord ++ tailWord_618476).sum := by decide
  have hdescent : baseEnd_618476 < baseStart_618476 := by decide
  rcases family_descends (prefixWord ++ tailWord_618476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618525 : List Nat := [1, 4, 2, 2, 2, 2, 2, 3, 4]
def baseStart_618525 : Nat := 118140960795 + 618525 * 2 ^ 59
def prefixEnd_618525 : Nat := 4983230072969 + 3 ^ 40 * 618525 * 2
def baseEnd_618525 : Nat := 70577915960510611509547

theorem tailTrace_618525 : CollatzResearch.WordTrace tailWord_618525 prefixEnd_618525 70577915960510611509547 := by
  unfold tailWord_618525
  simp only [CollatzResearch.WordTrace]
  refine ⟨22559460084197035505025029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15039640056131357003350019 22559460084197035505025029)
  ·
    refine ⟨4229898765786944157192193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22559460084197035505025029 4229898765786944157192193)
    ·
      refine ⟨3172424074340208117894145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4229898765786944157192193 3172424074340208117894145)
      ·
        refine ⟨2379318055755156088420609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3172424074340208117894145 2379318055755156088420609)
        ·
          refine ⟨1784488541816367066315457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2379318055755156088420609 1784488541816367066315457)
          ·
            refine ⟨1338366406362275299736593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1784488541816367066315457 1338366406362275299736593)
            ·
              refine ⟨1003774804771706474802445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338366406362275299736593 1003774804771706474802445)
              ·
                refine ⟨376415551789389928050917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1003774804771706474802445 376415551789389928050917)
                ·
                  refine ⟨70577915960510611509547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 376415551789389928050917 70577915960510611509547)
                  ·
                    rfl

theorem cell22_618525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_618525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618525 prefixEnd_618525 := by exact prefixLift 618525
  have htrace : WordTrace (prefixWord ++ tailWord_618525) baseStart_618525 baseEnd_618525 := by
    simpa [prefixWord, tailWord_618525, baseEnd_618525] using wordTrace_append hprefix tailTrace_618525
  have hstable : (prefixWord ++ tailWord_618525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618525).length < 2 ^ (prefixWord ++ tailWord_618525).sum := by decide
  have hdescent : baseEnd_618525 < baseStart_618525 := by decide
  rcases family_descends (prefixWord ++ tailWord_618525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618581 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 7]
def baseStart_618581 : Nat := 118140960795 + 618581 * 2 ^ 59
def prefixEnd_618581 : Nat := 4983230072969 + 3 ^ 40 * 618581 * 2
def baseEnd_618581 : Nat := 70584305941988785042823

theorem tailTrace_618581 : CollatzResearch.WordTrace tailWord_618581 prefixEnd_618581 70584305941988785042823 := by
  unfold tailWord_618581
  simp only [CollatzResearch.WordTrace]
  refine ⟨22561502571994157069063597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15041001714662771379375731 22561502571994157069063597)
  ·
    refine ⟨8460563464497808900898849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22561502571994157069063597 8460563464497808900898849)
    ·
      refine ⟨6345422598373356675674137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8460563464497808900898849 6345422598373356675674137)
      ·
        refine ⟨4759066948780017506755603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6345422598373356675674137 4759066948780017506755603)
        ·
          refine ⟨7138600423170026260133405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4759066948780017506755603 7138600423170026260133405)
          ·
            refine ⟨2676975158688759847550027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7138600423170026260133405 2676975158688759847550027)
            ·
              refine ⟨4015462738033139771325041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2676975158688759847550027 4015462738033139771325041)
              ·
                refine ⟨3011597053524854828493781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4015462738033139771325041 3011597053524854828493781)
                ·
                  refine ⟨70584305941988785042823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3011597053524854828493781 70584305941988785042823)
                  ·
                    rfl

theorem cell22_618581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_618581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618581 prefixEnd_618581 := by exact prefixLift 618581
  have htrace : WordTrace (prefixWord ++ tailWord_618581) baseStart_618581 baseEnd_618581 := by
    simpa [prefixWord, tailWord_618581, baseEnd_618581] using wordTrace_append hprefix tailTrace_618581
  have hstable : (prefixWord ++ tailWord_618581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618581).length < 2 ^ (prefixWord ++ tailWord_618581).sum := by decide
  have hdescent : baseEnd_618581 < baseStart_618581 := by decide
  rcases family_descends (prefixWord ++ tailWord_618581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618596 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_618596 : Nat := 118140960795 + 618596 * 2 ^ 59
def prefixEnd_618596 : Nat := 4983230072969 + 3 ^ 40 * 618596 * 2
def baseEnd_618596 : Nat := 211758052632511316003423

theorem tailTrace_618596 : CollatzResearch.WordTrace tailWord_618596 prefixEnd_618596 211758052632511316003423 := by
  unfold tailWord_618596
  simp only [CollatzResearch.WordTrace]
  refine ⟨11281024833469907315429821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15041366444626543087239761 11281024833469907315429821)
  ·
    refine ⟨4230384312551215243286183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11281024833469907315429821 4230384312551215243286183)
    ·
      refine ⟨6345576468826822864929275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4230384312551215243286183 6345576468826822864929275)
      ·
        refine ⟨9518364703240234297393913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6345576468826822864929275 9518364703240234297393913)
        ·
          refine ⟨7138773527430175723045435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9518364703240234297393913 7138773527430175723045435)
          ·
            refine ⟨10708160291145263584568153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7138773527430175723045435 10708160291145263584568153)
            ·
              refine ⟨8031120218358947688426115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10708160291145263584568153 8031120218358947688426115)
              ·
                refine ⟨12046680327538421532639173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8031120218358947688426115 12046680327538421532639173)
                ·
                  refine ⟨2258752561413454037369845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12046680327538421532639173 2258752561413454037369845)
                  ·
                    refine ⟨211758052632511316003423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2258752561413454037369845 211758052632511316003423)
                    ·
                      rfl

theorem cell22_618596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_618596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618596 prefixEnd_618596 := by exact prefixLift 618596
  have htrace : WordTrace (prefixWord ++ tailWord_618596) baseStart_618596 baseEnd_618596 := by
    simpa [prefixWord, tailWord_618596, baseEnd_618596] using wordTrace_append hprefix tailTrace_618596
  have hstable : (prefixWord ++ tailWord_618596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618596).length < 2 ^ (prefixWord ++ tailWord_618596).sum := by decide
  have hdescent : baseEnd_618596 < baseStart_618596 := by decide
  rcases family_descends (prefixWord ++ tailWord_618596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618602 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 3, 3]
def baseStart_618602 : Nat := 118140960795 + 618602 * 2 ^ 59
def prefixEnd_618602 : Nat := 4983230072969 + 3 ^ 40 * 618602 * 2
def baseEnd_618602 : Nat := 211760106555129300353405

theorem tailTrace_618602 : CollatzResearch.WordTrace tailWord_618602 prefixEnd_618602 211760106555129300353405 := by
  unfold tailWord_618602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5640567126229519413894515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15041512336612051770385373 5640567126229519413894515)
  ·
    refine ⟨8460850689344279120841773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5640567126229519413894515 8460850689344279120841773)
    ·
      refine ⟨3172819008504104670315665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8460850689344279120841773 3172819008504104670315665)
      ·
        refine ⟨2379614256378078502736749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3172819008504104670315665 2379614256378078502736749)
        ·
          refine ⟨892355346141779438526281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2379614256378078502736749 892355346141779438526281)
          ·
            refine ⟨669266509606334578894711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 892355346141779438526281 669266509606334578894711)
            ·
              refine ⟨1003899764409501868342067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669266509606334578894711 1003899764409501868342067)
              ·
                refine ⟨1505849646614252802513101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003899764409501868342067 1505849646614252802513101)
                ·
                  refine ⟨564693617480344800942413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1505849646614252802513101 564693617480344800942413)
                  ·
                    refine ⟨211760106555129300353405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 564693617480344800942413 211760106555129300353405)
                    ·
                      rfl

theorem cell22_618602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_618602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618602 prefixEnd_618602 := by exact prefixLift 618602
  have htrace : WordTrace (prefixWord ++ tailWord_618602) baseStart_618602 baseEnd_618602 := by
    simpa [prefixWord, tailWord_618602, baseEnd_618602] using wordTrace_append hprefix tailTrace_618602
  have hstable : (prefixWord ++ tailWord_618602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618602).length < 2 ^ (prefixWord ++ tailWord_618602).sum := by decide
  have hdescent : baseEnd_618602 < baseStart_618602 := by decide
  rcases family_descends (prefixWord ++ tailWord_618602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618615 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 5]
def baseStart_618615 : Nat := 118140960795 + 618615 * 2 ^ 59
def prefixEnd_618615 : Nat := 4983230072969 + 3 ^ 40 * 618615 * 2
def baseEnd_618615 : Nat := 70588185573600533259455

theorem tailTrace_618615 : CollatzResearch.WordTrace tailWord_618615 prefixEnd_618615 70588185573600533259455 := by
  unfold tailWord_618615
  simp only [CollatzResearch.WordTrace]
  refine ⟨22562742653870980875801299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15041828435913987250534199 22562742653870980875801299)
  ·
    refine ⟨33844113980806471313701949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22562742653870980875801299 33844113980806471313701949)
    ·
      refine ⟨12691542742802426742638231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33844113980806471313701949 12691542742802426742638231)
      ·
        refine ⟨19037314114203640113957347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12691542742802426742638231 19037314114203640113957347)
        ·
          refine ⟨28555971171305460170936021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19037314114203640113957347 28555971171305460170936021)
          ·
            refine ⟨669280574327471722756313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28555971171305460170936021 669280574327471722756313)
            ·
              refine ⟨501960430745603792067235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669280574327471722756313 501960430745603792067235)
              ·
                refine ⟨752940646118405688100853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501960430745603792067235 752940646118405688100853)
                ·
                  refine ⟨70588185573600533259455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 752940646118405688100853 70588185573600533259455)
                  ·
                    rfl

theorem cell22_618615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 5].length) (baseStart_618615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618615 prefixEnd_618615 := by exact prefixLift 618615
  have htrace : WordTrace (prefixWord ++ tailWord_618615) baseStart_618615 baseEnd_618615 := by
    simpa [prefixWord, tailWord_618615, baseEnd_618615] using wordTrace_append hprefix tailTrace_618615
  have hstable : (prefixWord ++ tailWord_618615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618615).length < 2 ^ (prefixWord ++ tailWord_618615).sum := by decide
  have hdescent : baseEnd_618615 < baseStart_618615 := by decide
  rcases family_descends (prefixWord ++ tailWord_618615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618628 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_618628 : Nat := 118140960795 + 618628 * 2 ^ 59
def prefixEnd_618628 : Nat := 4983230072969 + 3 ^ 40 * 618628 * 2
def baseEnd_618628 : Nat := 211769006886473899203325

theorem tailTrace_618628 : CollatzResearch.WordTrace tailWord_618628 prefixEnd_618628 211769006886473899203325 := by
  unfold tailWord_618628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11281608401411942048012269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15042144535215922730683025 11281608401411942048012269)
  ·
    refine ⟨4230603150529478268004601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11281608401411942048012269 4230603150529478268004601)
    ·
      refine ⟨3172952362897108701003451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4230603150529478268004601 3172952362897108701003451)
      ·
        refine ⟨4759428544345663051505177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3172952362897108701003451 4759428544345663051505177)
        ·
          refine ⟨3569571408259247288628883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4759428544345663051505177 3569571408259247288628883)
          ·
            refine ⟨5354357112388870932943325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3569571408259247288628883 5354357112388870932943325)
            ·
              refine ⟨2007883917145826599853747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5354357112388870932943325 2007883917145826599853747)
              ·
                refine ⟨3011825875718739899780621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2007883917145826599853747 3011825875718739899780621)
                ·
                  refine ⟨1129434703394527462417733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3011825875718739899780621 1129434703394527462417733)
                  ·
                    refine ⟨211769006886473899203325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1129434703394527462417733 211769006886473899203325)
                    ·
                      rfl

theorem cell22_618628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_618628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618628 prefixEnd_618628 := by exact prefixLift 618628
  have htrace : WordTrace (prefixWord ++ tailWord_618628) baseStart_618628 baseEnd_618628 := by
    simpa [prefixWord, tailWord_618628, baseEnd_618628] using wordTrace_append hprefix tailTrace_618628
  have hstable : (prefixWord ++ tailWord_618628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618628).length < 2 ^ (prefixWord ++ tailWord_618628).sum := by decide
  have hdescent : baseEnd_618628 < baseStart_618628 := by decide
  rcases family_descends (prefixWord ++ tailWord_618628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618643 : List Nat := [1, 1, 1, 2, 1, 2, 3, 7, 4]
def baseStart_618643 : Nat := 118140960795 + 618643 * 2 ^ 59
def prefixEnd_618643 : Nat := 4983230072969 + 3 ^ 40 * 618643 * 2
def baseEnd_618643 : Nat := 70591380564339620026093

theorem tailTrace_618643 : CollatzResearch.WordTrace tailWord_618643 prefixEnd_618643 70591380564339620026093 := by
  unfold tailWord_618643
  simp only [CollatzResearch.WordTrace]
  refine ⟨22563763897769541657820583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15042509265179694438547055 22563763897769541657820583)
  ·
    refine ⟨33845645846654312486730875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22563763897769541657820583 33845645846654312486730875)
    ·
      refine ⟨50768468769981468730096313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33845645846654312486730875 50768468769981468730096313)
      ·
        refine ⟨38076351577486101547572235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50768468769981468730096313 38076351577486101547572235)
        ·
          refine ⟨57114527366229152321358353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38076351577486101547572235 57114527366229152321358353)
          ·
            refine ⟨42835895524671864241018765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57114527366229152321358353 42835895524671864241018765)
            ·
              refine ⟨16063460821751949090382037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42835895524671864241018765 16063460821751949090382037)
              ·
                refine ⟨376487363009811306805829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16063460821751949090382037 376487363009811306805829)
                ·
                  refine ⟨70591380564339620026093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 376487363009811306805829 70591380564339620026093)
                  ·
                    rfl

theorem cell22_618643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 4].length) (baseStart_618643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618643 prefixEnd_618643 := by exact prefixLift 618643
  have htrace : WordTrace (prefixWord ++ tailWord_618643) baseStart_618643 baseEnd_618643 := by
    simpa [prefixWord, tailWord_618643, baseEnd_618643] using wordTrace_append hprefix tailTrace_618643
  have hstable : (prefixWord ++ tailWord_618643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618643).length < 2 ^ (prefixWord ++ tailWord_618643).sum := by decide
  have hdescent : baseEnd_618643 < baseStart_618643 := by decide
  rcases family_descends (prefixWord ++ tailWord_618643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618645 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 1, 4]
def baseStart_618645 : Nat := 118140960795 + 618645 * 2 ^ 59
def prefixEnd_618645 : Nat := 4983230072969 + 3 ^ 40 * 618645 * 2
def baseEnd_618645 : Nat := 211774826333891521528273

theorem tailTrace_618645 : CollatzResearch.WordTrace tailWord_618645 prefixEnd_618645 211774826333891521528273 := by
  unfold tailWord_618645
  simp only [CollatzResearch.WordTrace]
  refine ⟨22563836843762295999393389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15042557895841530666262259 22563836843762295999393389)
  ·
    refine ⟨8461438816410860999772521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22563836843762295999393389 8461438816410860999772521)
    ·
      refine ⟨6346079112308145749829391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8461438816410860999772521 6346079112308145749829391)
      ·
        refine ⟨9519118668462218624744087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6346079112308145749829391 9519118668462218624744087)
        ·
          refine ⟨14278678002693327937116131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9519118668462218624744087 14278678002693327937116131)
          ·
            refine ⟨21418017004039991905674197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14278678002693327937116131 21418017004039991905674197)
            ·
              refine ⟨501984773532187310289239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21418017004039991905674197 501984773532187310289239)
              ·
                refine ⟨752977160298280965433859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501984773532187310289239 752977160298280965433859)
                ·
                  refine ⟨1129465740447421448150789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 752977160298280965433859 1129465740447421448150789)
                  ·
                    refine ⟨211774826333891521528273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1129465740447421448150789 211774826333891521528273)
                    ·
                      rfl

theorem cell22_618645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_618645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618645 prefixEnd_618645 := by exact prefixLift 618645
  have htrace : WordTrace (prefixWord ++ tailWord_618645) baseStart_618645 baseEnd_618645 := by
    simpa [prefixWord, tailWord_618645, baseEnd_618645] using wordTrace_append hprefix tailTrace_618645
  have hstable : (prefixWord ++ tailWord_618645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618645).length < 2 ^ (prefixWord ++ tailWord_618645).sum := by decide
  have hdescent : baseEnd_618645 < baseStart_618645 := by decide
  rcases family_descends (prefixWord ++ tailWord_618645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618703 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 5, 3]
def baseStart_618703 : Nat := 118140960795 + 618703 * 2 ^ 59
def prefixEnd_618703 : Nat := 4983230072969 + 3 ^ 40 * 618703 * 2
def baseEnd_618703 : Nat := 211794680919198703578095

theorem tailTrace_618703 : CollatzResearch.WordTrace tailWord_618703 prefixEnd_618703 211794680919198703578095 := by
  unfold tailWord_618703
  simp only [CollatzResearch.WordTrace]
  refine ⟨22565952277552171905004763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15043968185034781270003175 22565952277552171905004763)
  ·
    refine ⟨33848928416328257857507145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22565952277552171905004763 33848928416328257857507145)
    ·
      refine ⟨25386696312246193393130359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33848928416328257857507145 25386696312246193393130359)
      ·
        refine ⟨38080044468369290089695539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25386696312246193393130359 38080044468369290089695539)
        ·
          refine ⟨57120066702553935134543309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38080044468369290089695539 57120066702553935134543309)
          ·
            refine ⟨21420025013457725675453741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57120066702553935134543309 21420025013457725675453741)
            ·
              refine ⟨8032509380046647128295153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21420025013457725675453741 8032509380046647128295153)
              ·
                refine ⟨6024382035034985346221365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8032509380046647128295153 6024382035034985346221365)
                ·
                  refine ⟨564785815784529876208253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6024382035034985346221365 564785815784529876208253)
                  ·
                    refine ⟨211794680919198703578095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 564785815784529876208253 211794680919198703578095)
                    ·
                      rfl

theorem cell22_618703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 3].length) (baseStart_618703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618703 prefixEnd_618703 := by exact prefixLift 618703
  have htrace : WordTrace (prefixWord ++ tailWord_618703) baseStart_618703 baseEnd_618703 := by
    simpa [prefixWord, tailWord_618703, baseEnd_618703] using wordTrace_append hprefix tailTrace_618703
  have hstable : (prefixWord ++ tailWord_618703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618703).length < 2 ^ (prefixWord ++ tailWord_618703).sum := by decide
  have hdescent : baseEnd_618703 < baseStart_618703 := by decide
  rcases family_descends (prefixWord ++ tailWord_618703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618709 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 2, 3]
def baseStart_618709 : Nat := 118140960795 + 618709 * 2 ^ 59
def prefixEnd_618709 : Nat := 4983230072969 + 3 ^ 40 * 618709 * 2
def baseEnd_618709 : Nat := 211796734841816687928077

theorem tailTrace_618709 : CollatzResearch.WordTrace tailWord_618709 prefixEnd_618709 211796734841816687928077 := by
  unfold tailWord_618709
  simp only [CollatzResearch.WordTrace]
  refine ⟨22566171115530434929723181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15044114077020289953148787 22566171115530434929723181)
  ·
    refine ⟨8462314168323913098646193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22566171115530434929723181 8462314168323913098646193)
    ·
      refine ⟨6346735626242934823984645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8462314168323913098646193 6346735626242934823984645)
      ·
        refine ⟨1190012929920550279497121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6346735626242934823984645 1190012929920550279497121)
        ·
          refine ⟨892509697440412709622841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1190012929920550279497121 892509697440412709622841)
          ·
            refine ⟨669382273080309532217131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 892509697440412709622841 669382273080309532217131)
            ·
              refine ⟨1004073409620464298325697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669382273080309532217131 1004073409620464298325697)
              ·
                refine ⟨753055057215348223744273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004073409620464298325697 753055057215348223744273)
                ·
                  refine ⟨564791292911511167808205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 753055057215348223744273 564791292911511167808205)
                  ·
                    refine ⟨211796734841816687928077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 564791292911511167808205 211796734841816687928077)
                    ·
                      rfl

theorem cell22_618709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_618709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618709 prefixEnd_618709 := by exact prefixLift 618709
  have htrace : WordTrace (prefixWord ++ tailWord_618709) baseStart_618709 baseEnd_618709 := by
    simpa [prefixWord, tailWord_618709, baseEnd_618709] using wordTrace_append hprefix tailTrace_618709
  have hstable : (prefixWord ++ tailWord_618709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618709).length < 2 ^ (prefixWord ++ tailWord_618709).sum := by decide
  have hdescent : baseEnd_618709 < baseStart_618709 := by decide
  rcases family_descends (prefixWord ++ tailWord_618709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618720 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 3, 3]
def baseStart_618720 : Nat := 118140960795 + 618720 * 2 ^ 59
def prefixEnd_618720 : Nat := 4983230072969 + 3 ^ 40 * 618720 * 2
def baseEnd_618720 : Nat := 211800500366616325903043

theorem tailTrace_618720 : CollatzResearch.WordTrace tailWord_618720 prefixEnd_618720 211800500366616325903043 := by
  unfold tailWord_618720
  simp only [CollatzResearch.WordTrace]
  refine ⟨11283286159245291904186807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15044381545660389205582409 11283286159245291904186807)
  ·
    refine ⟨16924929238867937856280211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11283286159245291904186807 16924929238867937856280211)
    ·
      refine ⟨25387393858301906784420317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16924929238867937856280211 25387393858301906784420317)
      ·
        refine ⟨9520272696863215044157619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25387393858301906784420317 9520272696863215044157619)
        ·
          refine ⟨14280409045294822566236429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9520272696863215044157619 14280409045294822566236429)
          ·
            refine ⟨5355153391985558462338661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14280409045294822566236429 5355153391985558462338661)
            ·
              refine ⟨1004091260997292211688499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5355153391985558462338661 1004091260997292211688499)
              ·
                refine ⟨1506136891495938317532749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004091260997292211688499 1506136891495938317532749)
                ·
                  refine ⟨564801334310976869074781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1506136891495938317532749 564801334310976869074781)
                  ·
                    refine ⟨211800500366616325903043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 564801334310976869074781 211800500366616325903043)
                    ·
                      rfl

theorem cell22_618720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3, 3].length) (baseStart_618720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618720 prefixEnd_618720 := by exact prefixLift 618720
  have htrace : WordTrace (prefixWord ++ tailWord_618720) baseStart_618720 baseEnd_618720 := by
    simpa [prefixWord, tailWord_618720, baseEnd_618720] using wordTrace_append hprefix tailTrace_618720
  have hstable : (prefixWord ++ tailWord_618720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618720).length < 2 ^ (prefixWord ++ tailWord_618720).sum := by decide
  have hdescent : baseEnd_618720 < baseStart_618720 := by decide
  rcases family_descends (prefixWord ++ tailWord_618720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618808 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 1, 6]
def baseStart_618808 : Nat := 118140960795 + 618808 * 2 ^ 59
def prefixEnd_618808 : Nat := 4983230072969 + 3 ^ 40 * 618808 * 2
def baseEnd_618808 : Nat := 211830624565013429702773

theorem tailTrace_618808 : CollatzResearch.WordTrace tailWord_618808 prefixEnd_618808 211830624565013429702773 := by
  unfold tailWord_618808
  simp only [CollatzResearch.WordTrace]
  refine ⟨11284890971085887418788539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15046521294781183225051385 11284890971085887418788539)
  ·
    refine ⟨16927336456628831128182809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11284890971085887418788539 16927336456628831128182809)
    ·
      refine ⟨12695502342471623346137107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16927336456628831128182809 12695502342471623346137107)
      ·
        refine ⟨19043253513707435019205661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12695502342471623346137107 19043253513707435019205661)
        ·
          refine ⟨7141220067640288132202123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19043253513707435019205661 7141220067640288132202123)
          ·
            refine ⟨10711830101460432198303185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7141220067640288132202123 10711830101460432198303185)
            ·
              refine ⟨8033872576095324148727389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10711830101460432198303185 8033872576095324148727389)
              ·
                refine ⟨3012702216035746555772771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8033872576095324148727389 3012702216035746555772771)
                ·
                  refine ⟨4519053324053619833659157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3012702216035746555772771 4519053324053619833659157)
                  ·
                    refine ⟨211830624565013429702773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4519053324053619833659157 211830624565013429702773)
                    ·
                      rfl

theorem cell22_618808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_618808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618808 prefixEnd_618808 := by exact prefixLift 618808
  have htrace : WordTrace (prefixWord ++ tailWord_618808) baseStart_618808 baseEnd_618808 := by
    simpa [prefixWord, tailWord_618808, baseEnd_618808] using wordTrace_append hprefix tailTrace_618808
  have hstable : (prefixWord ++ tailWord_618808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618808).length < 2 ^ (prefixWord ++ tailWord_618808).sum := by decide
  have hdescent : baseEnd_618808 < baseStart_618808 := by decide
  rcases family_descends (prefixWord ++ tailWord_618808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618810 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_618810 : Nat := 118140960795 + 618810 * 2 ^ 59
def prefixEnd_618810 : Nat := 4983230072969 + 3 ^ 40 * 618810 * 2
def baseEnd_618810 : Nat := 211831309205886091152767

theorem tailTrace_618810 : CollatzResearch.WordTrace tailWord_618810 prefixEnd_618810 211831309205886091152767 := by
  unfold tailWord_618810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5642463722041132294787471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15046569925443019452766589 5642463722041132294787471)
  ·
    refine ⟨8463695583061698442181207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5642463722041132294787471 8463695583061698442181207)
    ·
      refine ⟨12695543374592547663271811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8463695583061698442181207 12695543374592547663271811)
      ·
        refine ⟨19043315061888821494907717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12695543374592547663271811 19043315061888821494907717)
        ·
          refine ⟨3570621574104154030295197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19043315061888821494907717 3570621574104154030295197)
          ·
            refine ⟨1338983090289057761360699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3570621574104154030295197 1338983090289057761360699)
            ·
              refine ⟨2008474635433586642041049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338983090289057761360699 2008474635433586642041049)
              ·
                refine ⟨1506355976575189981530787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2008474635433586642041049 1506355976575189981530787)
                ·
                  refine ⟨2259533964862784972296181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506355976575189981530787 2259533964862784972296181)
                  ·
                    refine ⟨211831309205886091152767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2259533964862784972296181 211831309205886091152767)
                    ·
                      rfl

theorem cell22_618810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_618810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618810 prefixEnd_618810 := by exact prefixLift 618810
  have htrace : WordTrace (prefixWord ++ tailWord_618810) baseStart_618810 baseEnd_618810 := by
    simpa [prefixWord, tailWord_618810, baseEnd_618810] using wordTrace_append hprefix tailTrace_618810
  have hstable : (prefixWord ++ tailWord_618810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618810).length < 2 ^ (prefixWord ++ tailWord_618810).sum := by decide
  have hdescent : baseEnd_618810 < baseStart_618810 := by decide
  rcases family_descends (prefixWord ++ tailWord_618810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618814 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_618814 : Nat := 118140960795 + 618814 * 2 ^ 59
def prefixEnd_618814 : Nat := 4983230072969 + 3 ^ 40 * 618814 * 2
def baseEnd_618814 : Nat := 211832678487631414052755

theorem tailTrace_618814 : CollatzResearch.WordTrace tailWord_618814 prefixEnd_618814 211832678487631414052755 := by
  unfold tailWord_618814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821250097518754732786937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15046667186766691908196997 2821250097518754732786937)
  ·
    refine ⟨2115937573139066049590203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2821250097518754732786937 2115937573139066049590203)
    ·
      refine ⟨3173906359708599074385305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2115937573139066049590203 3173906359708599074385305)
      ·
        refine ⟨2380429769781449305788979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3173906359708599074385305 2380429769781449305788979)
        ·
          refine ⟨3570644654672173958683469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2380429769781449305788979 3570644654672173958683469)
          ·
            refine ⟨1338991745502065234506301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3570644654672173958683469 1338991745502065234506301)
            ·
              refine ⟨502121904563274462939863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1338991745502065234506301 502121904563274462939863)
              ·
                refine ⟨753182856844911694409795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502121904563274462939863 753182856844911694409795)
                ·
                  refine ⟨1129774285267367541614693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753182856844911694409795 1129774285267367541614693)
                  ·
                    refine ⟨211832678487631414052755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1129774285267367541614693 211832678487631414052755)
                    ·
                      rfl

theorem cell22_618814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_618814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618814 prefixEnd_618814 := by exact prefixLift 618814
  have htrace : WordTrace (prefixWord ++ tailWord_618814) baseStart_618814 baseEnd_618814 := by
    simpa [prefixWord, tailWord_618814, baseEnd_618814] using wordTrace_append hprefix tailTrace_618814
  have hstable : (prefixWord ++ tailWord_618814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618814).length < 2 ^ (prefixWord ++ tailWord_618814).sum := by decide
  have hdescent : baseEnd_618814 < baseStart_618814 := by decide
  rcases family_descends (prefixWord ++ tailWord_618814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618844 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 1, 5]
def baseStart_618844 : Nat := 118140960795 + 618844 * 2 ^ 59
def prefixEnd_618844 : Nat := 4983230072969 + 3 ^ 40 * 618844 * 2
def baseEnd_618844 : Nat := 211842948100721335802663

theorem tailTrace_618844 : CollatzResearch.WordTrace tailWord_618844 prefixEnd_618844 211842948100721335802663 := by
  unfold tailWord_618844
  simp only [CollatzResearch.WordTrace]
  refine ⟨11285547485020676492943793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15047396646694235323925057 11285547485020676492943793)
  ·
    refine ⟨8464160613765507369707845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11285547485020676492943793 8464160613765507369707845)
    ·
      refine ⟨1587030115081032631820221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8464160613765507369707845 1587030115081032631820221)
      ·
        refine ⟨595136293155387236932583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1587030115081032631820221 595136293155387236932583)
        ·
          refine ⟨892704439733080855398875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595136293155387236932583 892704439733080855398875)
          ·
            refine ⟨1339056659599621283098313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892704439733080855398875 1339056659599621283098313)
            ·
              refine ⟨1004292494699715962323735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1339056659599621283098313 1004292494699715962323735)
              ·
                refine ⟨1506438742049573943485603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004292494699715962323735 1506438742049573943485603)
                ·
                  refine ⟨2259658113074360915228405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1506438742049573943485603 2259658113074360915228405)
                  ·
                    refine ⟨211842948100721335802663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2259658113074360915228405 211842948100721335802663)
                    ·
                      rfl

theorem cell22_618844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_618844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618844 prefixEnd_618844 := by exact prefixLift 618844
  have htrace : WordTrace (prefixWord ++ tailWord_618844) baseStart_618844 baseEnd_618844 := by
    simpa [prefixWord, tailWord_618844, baseEnd_618844] using wordTrace_append hprefix tailTrace_618844
  have hstable : (prefixWord ++ tailWord_618844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618844).length < 2 ^ (prefixWord ++ tailWord_618844).sum := by decide
  have hdescent : baseEnd_618844 < baseStart_618844 := by decide
  rcases family_descends (prefixWord ++ tailWord_618844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618889 : List Nat := [1, 2, 1, 1, 6, 1, 2, 4, 1, 3]
def baseStart_618889 : Nat := 118140960795 + 618889 * 2 ^ 59
def prefixEnd_618889 : Nat := 4983230072969 + 3 ^ 40 * 618889 * 2
def baseEnd_618889 : Nat := 211858352520356218427525

theorem tailTrace_618889 : CollatzResearch.WordTrace tailWord_618889 prefixEnd_618889 211858352520356218427525 := by
  unfold tailWord_618889
  simp only [CollatzResearch.WordTrace]
  refine ⟨22572736254878325671275721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15048490836585550447517147 22572736254878325671275721)
  ·
    refine ⟨16929552191158744253456791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22572736254878325671275721 16929552191158744253456791)
    ·
      refine ⟨25394328286738116380185187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16929552191158744253456791 25394328286738116380185187)
      ·
        refine ⟨38091492430107174570277781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25394328286738116380185187 38091492430107174570277781)
        ·
          refine ⟨1785538707661273807981771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38091492430107174570277781 1785538707661273807981771)
          ·
            refine ⟨2678308061491910711972657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785538707661273807981771 2678308061491910711972657)
            ·
              refine ⟨2008731046118933033979493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2678308061491910711972657 2008731046118933033979493)
              ·
                refine ⟨376637071147299943871155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2008731046118933033979493 376637071147299943871155)
                ·
                  refine ⟨564955606720949915806733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376637071147299943871155 564955606720949915806733)
                  ·
                    refine ⟨211858352520356218427525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 564955606720949915806733 211858352520356218427525)
                    ·
                      rfl

theorem cell22_618889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 1, 3].length) (baseStart_618889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618889 prefixEnd_618889 := by exact prefixLift 618889
  have htrace : WordTrace (prefixWord ++ tailWord_618889) baseStart_618889 baseEnd_618889 := by
    simpa [prefixWord, tailWord_618889, baseEnd_618889] using wordTrace_append hprefix tailTrace_618889
  have hstable : (prefixWord ++ tailWord_618889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618889).length < 2 ^ (prefixWord ++ tailWord_618889).sum := by decide
  have hdescent : baseEnd_618889 < baseStart_618889 := by decide
  rcases family_descends (prefixWord ++ tailWord_618889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618975 : List Nat := [1, 1, 2, 3, 3, 2, 2, 8]
def baseStart_618975 : Nat := 118140960795 + 618975 * 2 ^ 59
def prefixEnd_618975 : Nat := 4983230072969 + 3 ^ 40 * 618975 * 2
def baseEnd_618975 : Nat := 23543088008653406753029

theorem tailTrace_618975 : CollatzResearch.WordTrace tailWord_618975 prefixEnd_618975 23543088008653406753029 := by
  unfold tailWord_618975
  simp only [CollatzResearch.WordTrace]
  refine ⟨22575872932566762358906379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15050581955044508239270919 22575872932566762358906379)
  ·
    refine ⟨33863809398850143538359569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22575872932566762358906379 33863809398850143538359569)
    ·
      refine ⟨25397857049137607653769677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33863809398850143538359569 25397857049137607653769677)
      ·
        refine ⟨9524196393426602870163629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25397857049137607653769677 9524196393426602870163629)
        ·
          refine ⟨3571573647534976076311361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9524196393426602870163629 3571573647534976076311361)
          ·
            refine ⟨2678680235651232057233521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3571573647534976076311361 2678680235651232057233521)
            ·
              refine ⟨2009010176738424042925141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2678680235651232057233521 2009010176738424042925141)
              ·
                refine ⟨23543088008653406753029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2009010176738424042925141 23543088008653406753029)
                ·
                  rfl

theorem cell22_618975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 8].length) (baseStart_618975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618975 prefixEnd_618975 := by exact prefixLift 618975
  have htrace : WordTrace (prefixWord ++ tailWord_618975) baseStart_618975 baseEnd_618975 := by
    simpa [prefixWord, tailWord_618975, baseEnd_618975] using wordTrace_append hprefix tailTrace_618975
  have hstable : (prefixWord ++ tailWord_618975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618975).length < 2 ^ (prefixWord ++ tailWord_618975).sum := by decide
  have hdescent : baseEnd_618975 < baseStart_618975 := by decide
  rcases family_descends (prefixWord ++ tailWord_618975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_618977 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 2, 4]
def baseStart_618977 : Nat := 118140960795 + 618977 * 2 ^ 59
def prefixEnd_618977 : Nat := 4983230072969 + 3 ^ 40 * 618977 * 2
def baseEnd_618977 : Nat := 211888476718753322227255

theorem tailTrace_618977 : CollatzResearch.WordTrace tailWord_618977 prefixEnd_618977 211888476718753322227255 := by
  unfold tailWord_618977
  simp only [CollatzResearch.WordTrace]
  refine ⟨22575945878559516700479185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15050630585706344466986123 22575945878559516700479185)
  ·
    refine ⟨16931959408919637525359389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22575945878559516700479185 16931959408919637525359389)
    ·
      refine ⟨6349484778344864072009771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16931959408919637525359389 6349484778344864072009771)
      ·
        refine ⟨9524227167517296108014657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6349484778344864072009771 9524227167517296108014657)
        ·
          refine ⟨7143170375637972081010993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9524227167517296108014657 7143170375637972081010993)
          ·
            refine ⟨5357377781728479060758245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7143170375637972081010993 5357377781728479060758245)
            ·
              refine ⟨1004508334074089823892171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5357377781728479060758245 1004508334074089823892171)
              ·
                refine ⟨1506762501111134735838257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004508334074089823892171 1506762501111134735838257)
                ·
                  refine ⟨1130071875833351051878693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1506762501111134735838257 1130071875833351051878693)
                  ·
                    refine ⟨211888476718753322227255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1130071875833351051878693 211888476718753322227255)
                    ·
                      rfl

theorem cell22_618977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_618977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_618977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_618977 prefixEnd_618977 := by exact prefixLift 618977
  have htrace : WordTrace (prefixWord ++ tailWord_618977) baseStart_618977 baseEnd_618977 := by
    simpa [prefixWord, tailWord_618977, baseEnd_618977] using wordTrace_append hprefix tailTrace_618977
  have hstable : (prefixWord ++ tailWord_618977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_618977).length < 2 ^ (prefixWord ++ tailWord_618977).sum := by decide
  have hdescent : baseEnd_618977 < baseStart_618977 := by decide
  rcases family_descends (prefixWord ++ tailWord_618977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619005 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_619005 : Nat := 118140960795 + 619005 * 2 ^ 59
def prefixEnd_619005 : Nat := 4983230072969 + 3 ^ 40 * 619005 * 2
def baseEnd_619005 : Nat := 211898061690970582527169

theorem tailTrace_619005 : CollatzResearch.WordTrace tailWord_619005 prefixEnd_619005 211898061690970582527169 := by
  unfold tailWord_619005
  simp only [CollatzResearch.WordTrace]
  refine ⟨22576967122458077482498469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15051311414972051654998979 22576967122458077482498469)
  ·
    refine ⟨4233181335460889527968463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22576967122458077482498469 4233181335460889527968463)
    ·
      refine ⟨6349772003191334291952695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4233181335460889527968463 6349772003191334291952695)
      ·
        refine ⟨9524658004787001437929043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6349772003191334291952695 9524658004787001437929043)
        ·
          refine ⟨14286987007180502156893565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9524658004787001437929043 14286987007180502156893565)
          ·
            refine ⟨5357620127692688308835087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14286987007180502156893565 5357620127692688308835087)
            ·
              refine ⟨8036430191539032463252631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357620127692688308835087 8036430191539032463252631)
              ·
                refine ⟨12054645287308548694878947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8036430191539032463252631 12054645287308548694878947)
                ·
                  refine ⟨18081967930962823042318421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12054645287308548694878947 18081967930962823042318421)
                  ·
                    refine ⟨211898061690970582527169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18081967930962823042318421 211898061690970582527169)
                    ·
                      rfl

theorem cell22_619005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_619005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619005 prefixEnd_619005 := by exact prefixLift 619005
  have htrace : WordTrace (prefixWord ++ tailWord_619005) baseStart_619005 baseEnd_619005 := by
    simpa [prefixWord, tailWord_619005, baseEnd_619005] using wordTrace_append hprefix tailTrace_619005
  have hstable : (prefixWord ++ tailWord_619005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619005).length < 2 ^ (prefixWord ++ tailWord_619005).sum := by decide
  have hdescent : baseEnd_619005 < baseStart_619005 := by decide
  rcases family_descends (prefixWord ++ tailWord_619005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619007 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 3, 3]
def baseStart_619007 : Nat := 118140960795 + 619007 * 2 ^ 59
def prefixEnd_619007 : Nat := 4983230072969 + 3 ^ 40 * 619007 * 2
def baseEnd_619007 : Nat := 211898746331843243977163

theorem tailTrace_619007 : CollatzResearch.WordTrace tailWord_619007 prefixEnd_619007 211898746331843243977163 := by
  unfold tailWord_619007
  simp only [CollatzResearch.WordTrace]
  refine ⟨22577040068450831824071275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15051360045633887882714183 22577040068450831824071275)
  ·
    refine ⟨33865560102676247736106913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22577040068450831824071275 33865560102676247736106913)
    ·
      refine ⟨25399170077007185802080185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33865560102676247736106913 25399170077007185802080185)
      ·
        refine ⟨19049377557755389351560139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25399170077007185802080185 19049377557755389351560139)
        ·
          refine ⟨28574066336633084027340209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19049377557755389351560139 28574066336633084027340209)
          ·
            refine ⟨21430549752474813020505157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28574066336633084027340209 21430549752474813020505157)
            ·
              refine ⟨4018228078589027441344717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21430549752474813020505157 4018228078589027441344717)
              ·
                refine ⟨1506835529470885290504269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4018228078589027441344717 1506835529470885290504269)
                ·
                  refine ⟨565063323551581983939101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1506835529470885290504269 565063323551581983939101)
                  ·
                    refine ⟨211898746331843243977163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 565063323551581983939101 211898746331843243977163)
                    ·
                      rfl

theorem cell22_619007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 3].length) (baseStart_619007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619007 prefixEnd_619007 := by exact prefixLift 619007
  have htrace : WordTrace (prefixWord ++ tailWord_619007) baseStart_619007 baseEnd_619007 := by
    simpa [prefixWord, tailWord_619007, baseEnd_619007] using wordTrace_append hprefix tailTrace_619007
  have hstable : (prefixWord ++ tailWord_619007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619007).length < 2 ^ (prefixWord ++ tailWord_619007).sum := by decide
  have hdescent : baseEnd_619007 < baseStart_619007 := by decide
  rcases family_descends (prefixWord ++ tailWord_619007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619041 : List Nat := [1, 2, 3, 2, 2, 1, 4, 3, 1, 3]
def baseStart_619041 : Nat := 118140960795 + 619041 * 2 ^ 59
def prefixEnd_619041 : Nat := 4983230072969 + 3 ^ 40 * 619041 * 2
def baseEnd_619041 : Nat := 211910385226678488627059

theorem tailTrace_619041 : CollatzResearch.WordTrace tailWord_619041 prefixEnd_619041 211910385226678488627059 := by
  unfold tailWord_619041
  simp only [CollatzResearch.WordTrace]
  refine ⟨22578280150327655630808977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15052186766885103753872651 22578280150327655630808977)
  ·
    refine ⟨16933710112745741723106733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22578280150327655630808977 16933710112745741723106733)
    ·
      refine ⟨6350141292279653146165025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16933710112745741723106733 6350141292279653146165025)
      ·
        refine ⟨4762605969209739859623769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6350141292279653146165025 4762605969209739859623769)
        ·
          refine ⟨3571954476907304894717827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4762605969209739859623769 3571954476907304894717827)
          ·
            refine ⟨5357931715360957342076741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571954476907304894717827 5357931715360957342076741)
            ·
              refine ⟨1004612196630179501639389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5357931715360957342076741 1004612196630179501639389)
              ·
                refine ⟨376729573736317313114771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1004612196630179501639389 376729573736317313114771)
                ·
                  refine ⟨565094360604475969672157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376729573736317313114771 565094360604475969672157)
                  ·
                    refine ⟨211910385226678488627059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 565094360604475969672157 211910385226678488627059)
                    ·
                      rfl

theorem cell22_619041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_619041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619041 prefixEnd_619041 := by exact prefixLift 619041
  have htrace : WordTrace (prefixWord ++ tailWord_619041) baseStart_619041 baseEnd_619041 := by
    simpa [prefixWord, tailWord_619041, baseEnd_619041] using wordTrace_append hprefix tailTrace_619041
  have hstable : (prefixWord ++ tailWord_619041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619041).length < 2 ^ (prefixWord ++ tailWord_619041).sum := by decide
  have hdescent : baseEnd_619041 < baseStart_619041 := by decide
  rcases family_descends (prefixWord ++ tailWord_619041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619054 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_619054 : Nat := 118140960795 + 619054 * 2 ^ 59
def prefixEnd_619054 : Nat := 4983230072969 + 3 ^ 40 * 619054 * 2
def baseEnd_619054 : Nat := 70638278464116929350673

theorem tailTrace_619054 : CollatzResearch.WordTrace tailWord_619054 prefixEnd_619054 70638278464116929350673 := by
  unfold tailWord_619054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2822344287410069856379027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15052502866187039234021477 2822344287410069856379027)
  ·
    refine ⟨4233516431115104784568541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2822344287410069856379027 4233516431115104784568541)
    ·
      refine ⟨1587568661668164294213203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4233516431115104784568541 1587568661668164294213203)
      ·
        refine ⟨2381352992502246441319805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587568661668164294213203 2381352992502246441319805)
        ·
          refine ⟨893007372188342415494927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2381352992502246441319805 893007372188342415494927)
          ·
            refine ⟨1339511058282513623242391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893007372188342415494927 1339511058282513623242391)
            ·
              refine ⟨2009266587423770434863587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1339511058282513623242391 2009266587423770434863587)
              ·
                refine ⟨3013899881135655652295381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009266587423770434863587 3013899881135655652295381)
                ·
                  refine ⟨70638278464116929350673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3013899881135655652295381 70638278464116929350673)
                  ·
                    rfl

theorem cell22_619054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_619054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619054 prefixEnd_619054 := by exact prefixLift 619054
  have htrace : WordTrace (prefixWord ++ tailWord_619054) baseStart_619054 baseEnd_619054 := by
    simpa [prefixWord, tailWord_619054, baseEnd_619054] using wordTrace_append hprefix tailTrace_619054
  have hstable : (prefixWord ++ tailWord_619054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619054).length < 2 ^ (prefixWord ++ tailWord_619054).sum := by decide
  have hdescent : baseEnd_619054 < baseStart_619054 := by decide
  rcases family_descends (prefixWord ++ tailWord_619054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619082 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_619082 : Nat := 118140960795 + 619082 * 2 ^ 59
def prefixEnd_619082 : Nat := 4983230072969 + 3 ^ 40 * 619082 * 2
def baseEnd_619082 : Nat := 70641473454856016117311

theorem tailTrace_619082 : CollatzResearch.WordTrace tailWord_619082 prefixEnd_619082 70641473454856016117311 := by
  unfold tailWord_619082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5644943885794779908262875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15053183695452746422034333 5644943885794779908262875)
  ·
    refine ⟨8467415828692169862394313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5644943885794779908262875 8467415828692169862394313)
    ·
      refine ⟨6350561871519127396795735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8467415828692169862394313 6350561871519127396795735)
      ·
        refine ⟨9525842807278691095193603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6350561871519127396795735 9525842807278691095193603)
        ·
          refine ⟨14288764210918036642790405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9525842807278691095193603 14288764210918036642790405)
          ·
            refine ⟨2679143289547131870523201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14288764210918036642790405 2679143289547131870523201)
            ·
              refine ⟨2009357467160348902892401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2679143289547131870523201 2009357467160348902892401)
              ·
                refine ⟨1507018100370261677169301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2009357467160348902892401 1507018100370261677169301)
                ·
                  refine ⟨70641473454856016117311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1507018100370261677169301 70641473454856016117311)
                  ·
                    rfl

theorem cell22_619082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_619082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619082 prefixEnd_619082 := by exact prefixLift 619082
  have htrace : WordTrace (prefixWord ++ tailWord_619082) baseStart_619082 baseEnd_619082 := by
    simpa [prefixWord, tailWord_619082, baseEnd_619082] using wordTrace_append hprefix tailTrace_619082
  have hstable : (prefixWord ++ tailWord_619082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619082).length < 2 ^ (prefixWord ++ tailWord_619082).sum := by decide
  have hdescent : baseEnd_619082 < baseStart_619082 := by decide
  rcases family_descends (prefixWord ++ tailWord_619082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619084 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_619084 : Nat := 118140960795 + 619084 * 2 ^ 59
def prefixEnd_619084 : Nat := 4983230072969 + 3 ^ 40 * 619084 * 2
def baseEnd_619084 : Nat := 211925105005440709801927

theorem tailTrace_619084 : CollatzResearch.WordTrace tailWord_619084 prefixEnd_619084 211925105005440709801927 := by
  unfold tailWord_619084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11289924244585936987312153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15053232326114582649749537 11289924244585936987312153)
  ·
    refine ⟨8467443183439452740484115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11289924244585936987312153 8467443183439452740484115)
    ·
      refine ⟨12701164775159179110726173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8467443183439452740484115 12701164775159179110726173)
      ·
        refine ⟨4762936790684692166522315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12701164775159179110726173 4762936790684692166522315)
        ·
          refine ⟨7144405186027038249783473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4762936790684692166522315 7144405186027038249783473)
          ·
            refine ⟨5358303889520278687337605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7144405186027038249783473 5358303889520278687337605)
            ·
              refine ⟨1004681979285052253875801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5358303889520278687337605 1004681979285052253875801)
              ·
                refine ⟨753511484463789190406851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004681979285052253875801 753511484463789190406851)
                ·
                  refine ⟨1130267226695683785610277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753511484463789190406851 1130267226695683785610277)
                  ·
                    refine ⟨211925105005440709801927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1130267226695683785610277 211925105005440709801927)
                    ·
                      rfl

theorem cell22_619084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_619084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619084 prefixEnd_619084 := by exact prefixLift 619084
  have htrace : WordTrace (prefixWord ++ tailWord_619084) baseStart_619084 baseEnd_619084 := by
    simpa [prefixWord, tailWord_619084, baseEnd_619084] using wordTrace_append hprefix tailTrace_619084
  have hstable : (prefixWord ++ tailWord_619084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619084).length < 2 ^ (prefixWord ++ tailWord_619084).sum := by decide
  have hdescent : baseEnd_619084 < baseStart_619084 := by decide
  rcases family_descends (prefixWord ++ tailWord_619084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619114 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 4, 3]
def baseStart_619114 : Nat := 118140960795 + 619114 * 2 ^ 59
def prefixEnd_619114 : Nat := 4983230072969 + 3 ^ 40 * 619114 * 2
def baseEnd_619114 : Nat := 211935374618530631551835

theorem tailTrace_619114 : CollatzResearch.WordTrace tailWord_619114 prefixEnd_619114 211935374618530631551835 := by
  unfold tailWord_619114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5645235669765797274554099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15053961786042126065477597 5645235669765797274554099)
  ·
    refine ⟨8467853504648695911831149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5645235669765797274554099 8467853504648695911831149)
    ·
      refine ⟨3175445064243260966936681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8467853504648695911831149 3175445064243260966936681)
      ·
        refine ⟨2381583798182445725202511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3175445064243260966936681 2381583798182445725202511)
        ·
          refine ⟨3572375697273668587803767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381583798182445725202511 3572375697273668587803767)
          ·
            refine ⟨5358563545910502881705651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3572375697273668587803767 5358563545910502881705651)
            ·
              refine ⟨8037845318865754322558477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5358563545910502881705651 8037845318865754322558477)
              ·
                refine ⟨3014191994574657870959429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8037845318865754322558477 3014191994574657870959429)
                ·
                  refine ⟨565160998982748350804893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3014191994574657870959429 565160998982748350804893)
                  ·
                    refine ⟨211935374618530631551835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 565160998982748350804893 211935374618530631551835)
                    ·
                      rfl

theorem cell22_619114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_619114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619114 prefixEnd_619114 := by exact prefixLift 619114
  have htrace : WordTrace (prefixWord ++ tailWord_619114) baseStart_619114 baseEnd_619114 := by
    simpa [prefixWord, tailWord_619114, baseEnd_619114] using wordTrace_append hprefix tailTrace_619114
  have hstable : (prefixWord ++ tailWord_619114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619114).length < 2 ^ (prefixWord ++ tailWord_619114).sum := by decide
  have hdescent : baseEnd_619114 < baseStart_619114 := by decide
  rcases family_descends (prefixWord ++ tailWord_619114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619146 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_619146 : Nat := 118140960795 + 619146 * 2 ^ 59
def prefixEnd_619146 : Nat := 4983230072969 + 3 ^ 40 * 619146 * 2
def baseEnd_619146 : Nat := 211946328872493214751737

theorem tailTrace_619146 : CollatzResearch.WordTrace tailWord_619146 prefixEnd_619146 211946328872493214751737 := by
  unfold tailWord_619146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5645527453736814640845323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15054739876631505708920861 5645527453736814640845323)
  ·
    refine ⟨8468291180605221961267985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5645527453736814640845323 8468291180605221961267985)
    ·
      refine ⟨6351218385453916470950989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8468291180605221961267985 6351218385453916470950989)
      ·
        refine ⟨2381706894545218676606621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6351218385453916470950989 2381706894545218676606621)
        ·
          refine ⟨893140085454457003727483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2381706894545218676606621 893140085454457003727483)
          ·
            refine ⟨1339710128181685505591225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893140085454457003727483 1339710128181685505591225)
            ·
              refine ⟨1004782596136264129193419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1339710128181685505591225 1004782596136264129193419)
              ·
                refine ⟨1507173894204396193790129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004782596136264129193419 1507173894204396193790129)
                ·
                  refine ⟨1130380420653297145342597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1507173894204396193790129 1130380420653297145342597)
                  ·
                    refine ⟨211946328872493214751737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1130380420653297145342597 211946328872493214751737)
                    ·
                      rfl

theorem cell22_619146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_619146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619146 prefixEnd_619146 := by exact prefixLift 619146
  have htrace : WordTrace (prefixWord ++ tailWord_619146) baseStart_619146 baseEnd_619146 := by
    simpa [prefixWord, tailWord_619146, baseEnd_619146] using wordTrace_append hprefix tailTrace_619146
  have hstable : (prefixWord ++ tailWord_619146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619146).length < 2 ^ (prefixWord ++ tailWord_619146).sum := by decide
  have hdescent : baseEnd_619146 < baseStart_619146 := by decide
  rcases family_descends (prefixWord ++ tailWord_619146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619178 : List Nat := [3, 1, 5, 2, 1, 2, 1, 7]
def baseStart_619178 : Nat := 118140960795 + 619178 * 2 ^ 59
def prefixEnd_619178 : Nat := 4983230072969 + 3 ^ 40 * 619178 * 2
def baseEnd_619178 : Nat := 23550809236272866439071

theorem tailTrace_619178 : CollatzResearch.WordTrace tailWord_619178 prefixEnd_619178 23550809236272866439071 := by
  unfold tailWord_619178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5645819237707832007136547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15055517967220885352364125 5645819237707832007136547)
  ·
    refine ⟨8468728856561748010704821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5645819237707832007136547 8468728856561748010704821)
    ·
      refine ⟨793943330302663876003577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8468728856561748010704821 793943330302663876003577)
      ·
        refine ⟨595457497726997907002683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 793943330302663876003577 595457497726997907002683)
        ·
          refine ⟨893186246590496860504025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595457497726997907002683 893186246590496860504025)
          ·
            refine ⟨669889684942872645378019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 893186246590496860504025 669889684942872645378019)
            ·
              refine ⟨1004834527414308968067029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669889684942872645378019 1004834527414308968067029)
              ·
                refine ⟨23550809236272866439071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1004834527414308968067029 23550809236272866439071)
                ·
                  rfl

theorem cell22_619178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_619178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619178 prefixEnd_619178 := by exact prefixLift 619178
  have htrace : WordTrace (prefixWord ++ tailWord_619178) baseStart_619178 baseEnd_619178 := by
    simpa [prefixWord, tailWord_619178, baseEnd_619178] using wordTrace_append hprefix tailTrace_619178
  have hstable : (prefixWord ++ tailWord_619178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619178).length < 2 ^ (prefixWord ++ tailWord_619178).sum := by decide
  have hdescent : baseEnd_619178 < baseStart_619178 := by decide
  rcases family_descends (prefixWord ++ tailWord_619178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619187 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 1, 7]
def baseStart_619187 : Nat := 118140960795 + 619187 * 2 ^ 59
def prefixEnd_619187 : Nat := 4983230072969 + 3 ^ 40 * 619187 * 2
def baseEnd_619187 : Nat := 211960364010382774476611

theorem tailTrace_619187 : CollatzResearch.WordTrace tailWord_619187 prefixEnd_619187 211960364010382774476611 := by
  unfold tailWord_619187
  simp only [CollatzResearch.WordTrace]
  refine ⟨22583605207798722565623815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15055736805199148377082543 22583605207798722565623815)
  ·
    refine ⟨33875407811698083848435723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22583605207798722565623815 33875407811698083848435723)
    ·
      refine ⟨50813111717547125772653585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33875407811698083848435723 50813111717547125772653585)
      ·
        refine ⟨38109833788160344329490189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50813111717547125772653585 38109833788160344329490189)
        ·
          refine ⟨14291187670560129123558821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38109833788160344329490189 14291187670560129123558821)
          ·
            refine ⟨2679597688230024210667279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14291187670560129123558821 2679597688230024210667279)
            ·
              refine ⟨4019396532345036316000919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679597688230024210667279 4019396532345036316000919)
              ·
                refine ⟨6029094798517554474001379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4019396532345036316000919 6029094798517554474001379)
                ·
                  refine ⟨9043642197776331711002069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6029094798517554474001379 9043642197776331711002069)
                  ·
                    refine ⟨211960364010382774476611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9043642197776331711002069 211960364010382774476611)
                    ·
                      rfl

theorem cell22_619187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_619187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619187 prefixEnd_619187 := by exact prefixLift 619187
  have htrace : WordTrace (prefixWord ++ tailWord_619187) baseStart_619187 baseEnd_619187 := by
    simpa [prefixWord, tailWord_619187, baseEnd_619187] using wordTrace_append hprefix tailTrace_619187
  have hstable : (prefixWord ++ tailWord_619187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619187).length < 2 ^ (prefixWord ++ tailWord_619187).sum := by decide
  have hdescent : baseEnd_619187 < baseStart_619187 := by decide
  rcases family_descends (prefixWord ++ tailWord_619187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619217 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 8]
def baseStart_619217 : Nat := 118140960795 + 619217 * 2 ^ 59
def prefixEnd_619217 : Nat := 4983230072969 + 3 ^ 40 * 619217 * 2
def baseEnd_619217 : Nat := 70656877874490898742173

theorem tailTrace_619217 : CollatzResearch.WordTrace tailWord_619217 prefixEnd_619217 70656877874490898742173 := by
  unfold tailWord_619217
  simp only [CollatzResearch.WordTrace]
  refine ⟨22584699397690037689215905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15056466265126691792810603 22584699397690037689215905)
  ·
    refine ⟨16938524548267528266911929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22584699397690037689215905 16938524548267528266911929)
    ·
      refine ⟨12703893411200646200183947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16938524548267528266911929 12703893411200646200183947)
      ·
        refine ⟨19055840116800969300275921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12703893411200646200183947 19055840116800969300275921)
        ·
          refine ⟨14291880087600726975206941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19055840116800969300275921 14291880087600726975206941)
          ·
            refine ⟨5359455032850272615702603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14291880087600726975206941 5359455032850272615702603)
            ·
              refine ⟨8039182549275408923553905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5359455032850272615702603 8039182549275408923553905)
              ·
                refine ⟨6029386911956556692665429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8039182549275408923553905 6029386911956556692665429)
                ·
                  refine ⟨70656877874490898742173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6029386911956556692665429 70656877874490898742173)
                  ·
                    rfl

theorem cell22_619217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_619217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619217 prefixEnd_619217 := by exact prefixLift 619217
  have htrace : WordTrace (prefixWord ++ tailWord_619217) baseStart_619217 baseEnd_619217 := by
    simpa [prefixWord, tailWord_619217, baseEnd_619217] using wordTrace_append hprefix tailTrace_619217
  have hstable : (prefixWord ++ tailWord_619217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619217).length < 2 ^ (prefixWord ++ tailWord_619217).sum := by decide
  have hdescent : baseEnd_619217 < baseStart_619217 := by decide
  rcases family_descends (prefixWord ++ tailWord_619217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619345 : List Nat := [1, 2, 2, 1, 6, 1, 1, 4, 1, 3]
def baseStart_619345 : Nat := 118140960795 + 619345 * 2 ^ 59
def prefixEnd_619345 : Nat := 4983230072969 + 3 ^ 40 * 619345 * 2
def baseEnd_619345 : Nat := 212014450639323029026127

theorem tailTrace_619345 : CollatzResearch.WordTrace tailWord_619345 prefixEnd_619345 212014450639323029026127 := by
  unfold tailWord_619345
  simp only [CollatzResearch.WordTrace]
  refine ⟨22589367941226315549875489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15059578627484210366583659 22589367941226315549875489)
  ·
    refine ⟨16942025955919736662406617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22589367941226315549875489 16942025955919736662406617)
    ·
      refine ⟨12706519466939802496804963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16942025955919736662406617 12706519466939802496804963)
      ·
        refine ⟨19059779200409703745207445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12706519466939802496804963 19059779200409703745207445)
        ·
          refine ⟨893427150019204863056599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19059779200409703745207445 893427150019204863056599)
          ·
            refine ⟨1340140725028807294584899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893427150019204863056599 1340140725028807294584899)
            ·
              refine ⟨2010211087543210941877349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340140725028807294584899 2010211087543210941877349)
              ·
                refine ⟨376914578914352051602003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2010211087543210941877349 376914578914352051602003)
                ·
                  refine ⟨565371868371528077403005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376914578914352051602003 565371868371528077403005)
                  ·
                    refine ⟨212014450639323029026127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 565371868371528077403005 212014450639323029026127)
                    ·
                      rfl

theorem cell22_619345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_619345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619345 prefixEnd_619345 := by exact prefixLift 619345
  have htrace : WordTrace (prefixWord ++ tailWord_619345) baseStart_619345 baseEnd_619345 := by
    simpa [prefixWord, tailWord_619345, baseEnd_619345] using wordTrace_append hprefix tailTrace_619345
  have hstable : (prefixWord ++ tailWord_619345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619345).length < 2 ^ (prefixWord ++ tailWord_619345).sum := by decide
  have hdescent : baseEnd_619345 < baseStart_619345 := by decide
  rcases family_descends (prefixWord ++ tailWord_619345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619356 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_619356 : Nat := 118140960795 + 619356 * 2 ^ 59
def prefixEnd_619356 : Nat := 4983230072969 + 3 ^ 40 * 619356 * 2
def baseEnd_619356 : Nat := 212018216164122667001093

theorem tailTrace_619356 : CollatzResearch.WordTrace tailWord_619356 prefixEnd_619356 212018216164122667001093 := by
  unfold tailWord_619356
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294884572093232214262961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15059846096124309619017281 11294884572093232214262961)
  ·
    refine ⟨8471163429069924160697221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11294884572093232214262961 8471163429069924160697221)
    ·
      refine ⟨1588343142950610780130729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8471163429069924160697221 1588343142950610780130729)
      ·
        refine ⟨1191257357212958085098047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1588343142950610780130729 1191257357212958085098047)
        ·
          refine ⟨1786886035819437127647071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191257357212958085098047 1786886035819437127647071)
          ·
            refine ⟨2680329053729155691470607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786886035819437127647071 2680329053729155691470607)
            ·
              refine ⟨4020493580593733537205911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680329053729155691470607 4020493580593733537205911)
              ·
                refine ⟨6030740370890600305808867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4020493580593733537205911 6030740370890600305808867)
                ·
                  refine ⟨9046110556335900458713301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6030740370890600305808867 9046110556335900458713301)
                  ·
                    refine ⟨212018216164122667001093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9046110556335900458713301 212018216164122667001093)
                    ·
                      rfl

theorem cell22_619356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_619356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619356 prefixEnd_619356 := by exact prefixLift 619356
  have htrace : WordTrace (prefixWord ++ tailWord_619356) baseStart_619356 baseEnd_619356 := by
    simpa [prefixWord, tailWord_619356, baseEnd_619356] using wordTrace_append hprefix tailTrace_619356
  have hstable : (prefixWord ++ tailWord_619356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619356).length < 2 ^ (prefixWord ++ tailWord_619356).sum := by decide
  have hdescent : baseEnd_619356 < baseStart_619356 := by decide
  rcases family_descends (prefixWord ++ tailWord_619356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619384 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 3, 5]
def baseStart_619384 : Nat := 118140960795 + 619384 * 2 ^ 59
def prefixEnd_619384 : Nat := 4983230072969 + 3 ^ 40 * 619384 * 2
def baseEnd_619384 : Nat := 212027801136339927301007

theorem tailTrace_619384 : CollatzResearch.WordTrace tailWord_619384 prefixEnd_619384 212027801136339927301007 := by
  unfold tailWord_619384
  simp only [CollatzResearch.WordTrace]
  refine ⟨11295395194042512605272603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15060526925390016807030137 11295395194042512605272603)
  ·
    refine ⟨16943092791063768907908905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11295395194042512605272603 16943092791063768907908905)
    ·
      refine ⟨12707319593297826680931679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16943092791063768907908905 12707319593297826680931679)
      ·
        refine ⟨19060979389946740021397519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12707319593297826680931679 19060979389946740021397519)
        ·
          refine ⟨28591469084920110032096279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19060979389946740021397519 28591469084920110032096279)
          ·
            refine ⟨42887203627380165048144419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28591469084920110032096279 42887203627380165048144419)
            ·
              refine ⟨64330805441070247572216629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42887203627380165048144419 64330805441070247572216629)
              ·
                refine ⟨6031013010100335709895309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64330805441070247572216629 6031013010100335709895309)
                ·
                  refine ⟨2261629878787625891210741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6031013010100335709895309 2261629878787625891210741)
                  ·
                    refine ⟨212027801136339927301007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2261629878787625891210741 212027801136339927301007)
                    ·
                      rfl

theorem cell22_619384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_619384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619384 prefixEnd_619384 := by exact prefixLift 619384
  have htrace : WordTrace (prefixWord ++ tailWord_619384) baseStart_619384 baseEnd_619384 := by
    simpa [prefixWord, tailWord_619384, baseEnd_619384] using wordTrace_append hprefix tailTrace_619384
  have hstable : (prefixWord ++ tailWord_619384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619384).length < 2 ^ (prefixWord ++ tailWord_619384).sum := by decide
  have hdescent : baseEnd_619384 < baseStart_619384 := by decide
  rcases family_descends (prefixWord ++ tailWord_619384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619463 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 3, 3]
def baseStart_619463 : Nat := 118140960795 + 619463 * 2 ^ 59
def prefixEnd_619463 : Nat := 4983230072969 + 3 ^ 40 * 619463 * 2
def baseEnd_619463 : Nat := 212054844450810054575765

theorem tailTrace_619463 : CollatzResearch.WordTrace tailWord_619463 prefixEnd_619463 212054844450810054575765 := by
  unfold tailWord_619463
  simp only [CollatzResearch.WordTrace]
  refine ⟨22593671754798821702671043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15062447836532547801780695 22593671754798821702671043)
  ·
    refine ⟨33890507632198232554006565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22593671754798821702671043 33890507632198232554006565)
    ·
      refine ⟨6354470181037168603876231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33890507632198232554006565 6354470181037168603876231)
      ·
        refine ⟨9531705271555752905814347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6354470181037168603876231 9531705271555752905814347)
        ·
          refine ⟨14297557907333629358721521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9531705271555752905814347 14297557907333629358721521)
          ·
            refine ⟨10723168430500222019041141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14297557907333629358721521 10723168430500222019041141)
            ·
              refine ⟨1005297040359395814285107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10723168430500222019041141 1005297040359395814285107)
              ·
                refine ⟨1507945560539093721427661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005297040359395814285107 1507945560539093721427661)
                ·
                  refine ⟨565479585202160145535373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1507945560539093721427661 565479585202160145535373)
                  ·
                    refine ⟨212054844450810054575765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 565479585202160145535373 212054844450810054575765)
                    ·
                      rfl

theorem cell22_619463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_619463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619463 prefixEnd_619463 := by exact prefixLift 619463
  have htrace : WordTrace (prefixWord ++ tailWord_619463) baseStart_619463 baseEnd_619463 := by
    simpa [prefixWord, tailWord_619463, baseEnd_619463] using wordTrace_append hprefix tailTrace_619463
  have hstable : (prefixWord ++ tailWord_619463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619463).length < 2 ^ (prefixWord ++ tailWord_619463).sum := by decide
  have hdescent : baseEnd_619463 < baseStart_619463 := by decide
  rcases family_descends (prefixWord ++ tailWord_619463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619510 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_619510 : Nat := 118140960795 + 619510 * 2 ^ 59
def prefixEnd_619510 : Nat := 4983230072969 + 3 ^ 40 * 619510 * 2
def baseEnd_619510 : Nat := 70690311170439199550207

theorem tailTrace_619510 : CollatzResearch.WordTrace tailWord_619510 prefixEnd_619510 70690311170439199550207 := by
  unfold tailWord_619510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1412211624101784295601999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15063590657085699153087989 1412211624101784295601999)
  ·
    refine ⟨2118317436152676443402999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1412211624101784295601999 2118317436152676443402999)
    ·
      refine ⟨3177476154229014665104499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2118317436152676443402999 3177476154229014665104499)
      ·
        refine ⟨4766214231343521997656749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3177476154229014665104499 4766214231343521997656749)
        ·
          refine ⟨1787330336753820749121281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4766214231343521997656749 1787330336753820749121281)
          ·
            refine ⟨1340497752565365561840961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1787330336753820749121281 1340497752565365561840961)
            ·
              refine ⟨1005373314424024171380721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340497752565365561840961 1005373314424024171380721)
              ·
                refine ⟨754029985818018128535541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1005373314424024171380721 754029985818018128535541)
                ·
                  refine ⟨70690311170439199550207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 754029985818018128535541 70690311170439199550207)
                  ·
                    rfl

theorem cell22_619510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_619510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619510 prefixEnd_619510 := by exact prefixLift 619510
  have htrace : WordTrace (prefixWord ++ tailWord_619510) baseStart_619510 baseEnd_619510 := by
    simpa [prefixWord, tailWord_619510, baseEnd_619510] using wordTrace_append hprefix tailTrace_619510
  have hstable : (prefixWord ++ tailWord_619510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619510).length < 2 ^ (prefixWord ++ tailWord_619510).sum := by decide
  have hdescent : baseEnd_619510 < baseStart_619510 := by decide
  rcases family_descends (prefixWord ++ tailWord_619510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619553 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 1, 5]
def baseStart_619553 : Nat := 118140960795 + 619553 * 2 ^ 59
def prefixEnd_619553 : Nat := 4983230072969 + 3 ^ 40 * 619553 * 2
def baseEnd_619553 : Nat := 212085653290079819825489

theorem tailTrace_619553 : CollatzResearch.WordTrace tailWord_619553 prefixEnd_619553 212085653290079819825489 := by
  unfold tailWord_619553
  simp only [CollatzResearch.WordTrace]
  refine ⟨22596954324472767073447313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15064636216315178048964875 22596954324472767073447313)
  ·
    refine ⟨16947715743354575305085485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22596954324472767073447313 16947715743354575305085485)
    ·
      refine ⟨6355393403757965739407057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16947715743354575305085485 6355393403757965739407057)
      ·
        refine ⟨4766545052818474304555293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6355393403757965739407057 4766545052818474304555293)
        ·
          refine ⟨1787454394806927864208235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4766545052818474304555293 1787454394806927864208235)
          ·
            refine ⟨2681181592210391796312353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787454394806927864208235 2681181592210391796312353)
            ·
              refine ⟨2010886194157793847234265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2681181592210391796312353 2010886194157793847234265)
              ·
                refine ⟨1508164645618345385425699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2010886194157793847234265 1508164645618345385425699)
                ·
                  refine ⟨2262246968427518078138549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508164645618345385425699 2262246968427518078138549)
                  ·
                    refine ⟨212085653290079819825489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2262246968427518078138549 212085653290079819825489)
                    ·
                      rfl

theorem cell22_619553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_619553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619553 prefixEnd_619553 := by exact prefixLift 619553
  have htrace : WordTrace (prefixWord ++ tailWord_619553) baseStart_619553 baseEnd_619553 := by
    simpa [prefixWord, tailWord_619553, baseEnd_619553] using wordTrace_append hprefix tailTrace_619553
  have hstable : (prefixWord ++ tailWord_619553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619553).length < 2 ^ (prefixWord ++ tailWord_619553).sum := by decide
  have hdescent : baseEnd_619553 < baseStart_619553 := by decide
  rcases family_descends (prefixWord ++ tailWord_619553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619555 : List Nat := [1, 1, 1, 4, 3, 3, 2, 3, 4]
def baseStart_619555 : Nat := 118140960795 + 619555 * 2 ^ 59
def prefixEnd_619555 : Nat := 4983230072969 + 3 ^ 40 * 619555 * 2
def baseEnd_619555 : Nat := 70695445976984160425161

theorem tailTrace_619555 : CollatzResearch.WordTrace tailWord_619555 prefixEnd_619555 70695445976984160425161 := by
  unfold tailWord_619555
  simp only [CollatzResearch.WordTrace]
  refine ⟨22597027270465521415020119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15064684846977014276680079 22597027270465521415020119)
  ·
    refine ⟨33895540905698282122530179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22597027270465521415020119 33895540905698282122530179)
    ·
      refine ⟨50843311358547423183795269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33895540905698282122530179 50843311358547423183795269)
      ·
        refine ⟨9533120879727641846961613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50843311358547423183795269 9533120879727641846961613)
        ·
          refine ⟨3574920329897865692610605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9533120879727641846961613 3574920329897865692610605)
          ·
            refine ⟨1340595123711699634728977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3574920329897865692610605 1340595123711699634728977)
            ·
              refine ⟨1005446342783774726046733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340595123711699634728977 1005446342783774726046733)
              ·
                refine ⟨377042378543915522267525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1005446342783774726046733 377042378543915522267525)
                ·
                  refine ⟨70695445976984160425161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377042378543915522267525 70695445976984160425161)
                  ·
                    rfl

theorem cell22_619555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 4].length) (baseStart_619555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619555 prefixEnd_619555 := by exact prefixLift 619555
  have htrace : WordTrace (prefixWord ++ tailWord_619555) baseStart_619555 baseEnd_619555 := by
    simpa [prefixWord, tailWord_619555, baseEnd_619555] using wordTrace_append hprefix tailTrace_619555
  have hstable : (prefixWord ++ tailWord_619555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619555).length < 2 ^ (prefixWord ++ tailWord_619555).sum := by decide
  have hdescent : baseEnd_619555 < baseStart_619555 := by decide
  rcases family_descends (prefixWord ++ tailWord_619555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619572 : List Nat := [2, 5, 1, 2, 1, 1, 2, 4, 4]
def baseStart_619572 : Nat := 118140960795 + 619572 * 2 ^ 59
def prefixEnd_619572 : Nat := 4983230072969 + 3 ^ 40 * 619572 * 2
def baseEnd_619572 : Nat := 70697385792790034533477

theorem tailTrace_619572 : CollatzResearch.WordTrace tailWord_619572 prefixEnd_619572 70697385792790034533477 := by
  unfold tailWord_619572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11298823655701966659194485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15065098207602622212259313 11298823655701966659194485)
  ·
    refine ⟨1059264717722059374299483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11298823655701966659194485 1059264717722059374299483)
    ·
      refine ⟨1588897076583089061449225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1059264717722059374299483 1588897076583089061449225)
      ·
        refine ⟨1191672807437316796086919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1588897076583089061449225 1191672807437316796086919)
        ·
          refine ⟨1787509211155975194130379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191672807437316796086919 1787509211155975194130379)
          ·
            refine ⟨2681263816733962791195569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787509211155975194130379 2681263816733962791195569)
            ·
              refine ⟨2010947862550472093396677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2681263816733962791195569 2010947862550472093396677)
              ·
                refine ⟨377052724228213517511877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2010947862550472093396677 377052724228213517511877)
                ·
                  refine ⟨70697385792790034533477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377052724228213517511877 70697385792790034533477)
                  ·
                    rfl

theorem cell22_619572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_619572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619572 prefixEnd_619572 := by exact prefixLift 619572
  have htrace : WordTrace (prefixWord ++ tailWord_619572) baseStart_619572 baseEnd_619572 := by
    simpa [prefixWord, tailWord_619572, baseEnd_619572] using wordTrace_append hprefix tailTrace_619572
  have hstable : (prefixWord ++ tailWord_619572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619572).length < 2 ^ (prefixWord ++ tailWord_619572).sum := by decide
  have hdescent : baseEnd_619572 < baseStart_619572 := by decide
  rcases family_descends (prefixWord ++ tailWord_619572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619606 : List Nat := [5, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_619606 : Nat := 118140960795 + 619606 * 2 ^ 59
def prefixEnd_619606 : Nat := 4983230072969 + 3 ^ 40 * 619606 * 2
def baseEnd_619606 : Nat := 70701265424401782750109

theorem tailTrace_619606 : CollatzResearch.WordTrace tailWord_619606 prefixEnd_619606 70701265424401782750109 := by
  unfold tailWord_619606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1412430462080047320320417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15065924928853838083417781 1412430462080047320320417)
  ·
    refine ⟨1059322846560035490240313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1412430462080047320320417 1059322846560035490240313)
    ·
      refine ⟨794492134920026617680235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1059322846560035490240313 794492134920026617680235)
      ·
        refine ⟨1191738202380039926520353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794492134920026617680235 1191738202380039926520353)
        ·
          refine ⟨893803651785029944890265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1191738202380039926520353 893803651785029944890265)
          ·
            refine ⟨670352738838772458667699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 893803651785029944890265 670352738838772458667699)
            ·
              refine ⟨1005529108258158688001549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670352738838772458667699 1005529108258158688001549)
              ·
                refine ⟨377073415596809508000581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1005529108258158688001549 377073415596809508000581)
                ·
                  refine ⟨70701265424401782750109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377073415596809508000581 70701265424401782750109)
                  ·
                    rfl

theorem cell22_619606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_619606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619606 prefixEnd_619606 := by exact prefixLift 619606
  have htrace : WordTrace (prefixWord ++ tailWord_619606) baseStart_619606 baseEnd_619606 := by
    simpa [prefixWord, tailWord_619606, baseEnd_619606] using wordTrace_append hprefix tailTrace_619606
  have hstable : (prefixWord ++ tailWord_619606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619606).length < 2 ^ (prefixWord ++ tailWord_619606).sum := by decide
  have hdescent : baseEnd_619606 < baseStart_619606 := by decide
  rcases family_descends (prefixWord ++ tailWord_619606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619628 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 5]
def baseStart_619628 : Nat := 118140960795 + 619628 * 2 ^ 59
def prefixEnd_619628 : Nat := 4983230072969 + 3 ^ 40 * 619628 * 2
def baseEnd_619628 : Nat := 70703775774268208066753

theorem tailTrace_619628 : CollatzResearch.WordTrace tailWord_619628 prefixEnd_619628 70703775774268208066753 := by
  unfold tailWord_619628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11299844899600527441213769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15066459866134036588285025 11299844899600527441213769)
  ·
    refine ⟨8474883674700395580910327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11299844899600527441213769 8474883674700395580910327)
    ·
      refine ⟨12712325512050593371365491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8474883674700395580910327 12712325512050593371365491)
      ·
        refine ⟨19068488268075890057048237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12712325512050593371365491 19068488268075890057048237)
        ·
          refine ⟨7150683100528458771393089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19068488268075890057048237 7150683100528458771393089)
          ·
            refine ⟨5363012325396344078544817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7150683100528458771393089 5363012325396344078544817)
            ·
              refine ⟨4022259244047258058908613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5363012325396344078544817 4022259244047258058908613)
              ·
                refine ⟨754173608258860886045365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4022259244047258058908613 754173608258860886045365)
                ·
                  refine ⟨70703775774268208066753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 754173608258860886045365 70703775774268208066753)
                  ·
                    rfl

theorem cell22_619628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_619628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619628 prefixEnd_619628 := by exact prefixLift 619628
  have htrace : WordTrace (prefixWord ++ tailWord_619628) baseStart_619628 baseEnd_619628 := by
    simpa [prefixWord, tailWord_619628, baseEnd_619628] using wordTrace_append hprefix tailTrace_619628
  have hstable : (prefixWord ++ tailWord_619628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619628).length < 2 ^ (prefixWord ++ tailWord_619628).sum := by decide
  have hdescent : baseEnd_619628 < baseStart_619628 := by decide
  rcases family_descends (prefixWord ++ tailWord_619628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619703 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 1, 6]
def baseStart_619703 : Nat := 118140960795 + 619703 * 2 ^ 59
def prefixEnd_619703 : Nat := 4983230072969 + 3 ^ 40 * 619703 * 2
def baseEnd_619703 : Nat := 212137001355529428575029

theorem tailTrace_619703 : CollatzResearch.WordTrace tailWord_619703 prefixEnd_619703 212137001355529428575029 := by
  unfold tailWord_619703
  simp only [CollatzResearch.WordTrace]
  refine ⟨22602425273929342691407763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15068283515952895127605175 22602425273929342691407763)
  ·
    refine ⟨33903637910894014037111645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22602425273929342691407763 33903637910894014037111645)
    ·
      refine ⟨12713864216585255263916867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33903637910894014037111645 12713864216585255263916867)
      ·
        refine ⟨19070796324877882895875301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12713864216585255263916867 19070796324877882895875301)
        ·
          refine ⟨3575774310914603042976619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19070796324877882895875301 3575774310914603042976619)
          ·
            refine ⟨5363661466371904564464929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3575774310914603042976619 5363661466371904564464929)
            ·
              refine ⟨4022746099778928423348697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5363661466371904564464929 4022746099778928423348697)
              ·
                refine ⟨3017059574834196317511523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4022746099778928423348697 3017059574834196317511523)
                ·
                  refine ⟨4525589362251294476267285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3017059574834196317511523 4525589362251294476267285)
                  ·
                    refine ⟨212137001355529428575029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4525589362251294476267285 212137001355529428575029)
                    ·
                      rfl

theorem cell22_619703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_619703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619703 prefixEnd_619703 := by exact prefixLift 619703
  have htrace : WordTrace (prefixWord ++ tailWord_619703) baseStart_619703 baseEnd_619703 := by
    simpa [prefixWord, tailWord_619703, baseEnd_619703] using wordTrace_append hprefix tailTrace_619703
  have hstable : (prefixWord ++ tailWord_619703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619703).length < 2 ^ (prefixWord ++ tailWord_619703).sum := by decide
  have hdescent : baseEnd_619703 < baseStart_619703 := by decide
  rcases family_descends (prefixWord ++ tailWord_619703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619705 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 1, 5]
def baseStart_619705 : Nat := 118140960795 + 619705 * 2 ^ 59
def prefixEnd_619705 : Nat := 4983230072969 + 3 ^ 40 * 619705 * 2
def baseEnd_619705 : Nat := 212137685996402090025023

theorem tailTrace_619705 : CollatzResearch.WordTrace tailWord_619705 prefixEnd_619705 212137685996402090025023 := by
  unfold tailWord_619705
  simp only [CollatzResearch.WordTrace]
  refine ⟨22602498219922097032980569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15068332146614731355320379 22602498219922097032980569)
  ·
    refine ⟨16951873664941572774735427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22602498219922097032980569 16951873664941572774735427)
    ·
      refine ⟨25427810497412359162103141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16951873664941572774735427 25427810497412359162103141)
      ·
        refine ⟨4767714468264817342894339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25427810497412359162103141 4767714468264817342894339)
        ·
          refine ⟨7151571702397226014341509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4767714468264817342894339 7151571702397226014341509)
          ·
            refine ⟨1340919694199479877689033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7151571702397226014341509 1340919694199479877689033)
            ·
              refine ⟨1005689770649609908266775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340919694199479877689033 1005689770649609908266775)
              ·
                refine ⟨1508534655974414862400163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005689770649609908266775 1508534655974414862400163)
                ·
                  refine ⟨2262801983961622293600245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508534655974414862400163 2262801983961622293600245)
                  ·
                    refine ⟨212137685996402090025023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2262801983961622293600245 212137685996402090025023)
                    ·
                      rfl

theorem cell22_619705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 5].length) (baseStart_619705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619705 prefixEnd_619705 := by exact prefixLift 619705
  have htrace : WordTrace (prefixWord ++ tailWord_619705) baseStart_619705 baseEnd_619705 := by
    simpa [prefixWord, tailWord_619705, baseEnd_619705] using wordTrace_append hprefix tailTrace_619705
  have hstable : (prefixWord ++ tailWord_619705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619705).length < 2 ^ (prefixWord ++ tailWord_619705).sum := by decide
  have hdescent : baseEnd_619705 < baseStart_619705 := by decide
  rcases family_descends (prefixWord ++ tailWord_619705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619720 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 2, 4]
def baseStart_619720 : Nat := 118140960795 + 619720 * 2 ^ 59
def prefixEnd_619720 : Nat := 4983230072969 + 3 ^ 40 * 619720 * 2
def baseEnd_619720 : Nat := 212142820802947050899977

theorem tailTrace_619720 : CollatzResearch.WordTrace tailWord_619720 prefixEnd_619720 212142820802947050899977 := by
  unfold tailWord_619720
  simp only [CollatzResearch.WordTrace]
  refine ⟨11301522657433877297388307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15068696876578503063184409 11301522657433877297388307)
  ·
    refine ⟨16952283986150815946082461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11301522657433877297388307 16952283986150815946082461)
    ·
      refine ⟨6357106494806555979780923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16952283986150815946082461 6357106494806555979780923)
      ·
        refine ⟨9535659742209833969671385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6357106494806555979780923 9535659742209833969671385)
        ·
          refine ⟨7151744806657375477253539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9535659742209833969671385 7151744806657375477253539)
          ·
            refine ⟨10727617209986063215880309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7151744806657375477253539 10727617209986063215880309)
            ·
              refine ⟨1005714113436193426488779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10727617209986063215880309 1005714113436193426488779)
              ·
                refine ⟨1508571170154290139733169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005714113436193426488779 1508571170154290139733169)
                ·
                  refine ⟨1131428377615717604799877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1508571170154290139733169 1131428377615717604799877)
                  ·
                    refine ⟨212142820802947050899977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1131428377615717604799877 212142820802947050899977)
                    ·
                      rfl

theorem cell22_619720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_619720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619720 prefixEnd_619720 := by exact prefixLift 619720
  have htrace : WordTrace (prefixWord ++ tailWord_619720) baseStart_619720 baseEnd_619720 := by
    simpa [prefixWord, tailWord_619720, baseEnd_619720] using wordTrace_append hprefix tailTrace_619720
  have hstable : (prefixWord ++ tailWord_619720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619720).length < 2 ^ (prefixWord ++ tailWord_619720).sum := by decide
  have hdescent : baseEnd_619720 < baseStart_619720 := by decide
  rcases family_descends (prefixWord ++ tailWord_619720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619726 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_619726 : Nat := 118140960795 + 619726 * 2 ^ 59
def prefixEnd_619726 : Nat := 4983230072969 + 3 ^ 40 * 619726 * 2
def baseEnd_619726 : Nat := 212144874725565035249959

theorem tailTrace_619726 : CollatzResearch.WordTrace tailWord_619726 prefixEnd_619726 212144874725565035249959 := by
  unfold tailWord_619726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2825408019105752202436879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15068842768564011746330021 2825408019105752202436879)
  ·
    refine ⟨4238112028658628303655319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2825408019105752202436879 4238112028658628303655319)
    ·
      refine ⟨6357168042987942455482979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4238112028658628303655319 6357168042987942455482979)
      ·
        refine ⟨9535752064481913683224469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6357168042987942455482979 9535752064481913683224469)
        ·
          refine ⟨446988378022589703901147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9535752064481913683224469 446988378022589703901147)
          ·
            refine ⟨670482567033884555851721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446988378022589703901147 670482567033884555851721)
            ·
              refine ⟨502861925275413416888791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670482567033884555851721 502861925275413416888791)
              ·
                refine ⟨754292887913120125333187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502861925275413416888791 754292887913120125333187)
                ·
                  refine ⟨1131439331869680187999781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754292887913120125333187 1131439331869680187999781)
                  ·
                    refine ⟨212144874725565035249959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1131439331869680187999781 212144874725565035249959)
                    ·
                      rfl

theorem cell22_619726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_619726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619726 prefixEnd_619726 := by exact prefixLift 619726
  have htrace : WordTrace (prefixWord ++ tailWord_619726) baseStart_619726 baseEnd_619726 := by
    simpa [prefixWord, tailWord_619726, baseEnd_619726] using wordTrace_append hprefix tailTrace_619726
  have hstable : (prefixWord ++ tailWord_619726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619726).length < 2 ^ (prefixWord ++ tailWord_619726).sum := by decide
  have hdescent : baseEnd_619726 < baseStart_619726 := by decide
  rcases family_descends (prefixWord ++ tailWord_619726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619748 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_619748 : Nat := 118140960795 + 619748 * 2 ^ 59
def prefixEnd_619748 : Nat := 4983230072969 + 3 ^ 40 * 619748 * 2
def baseEnd_619748 : Nat := 212152405775164311199891

theorem tailTrace_619748 : CollatzResearch.WordTrace tailWord_619748 prefixEnd_619748 212152405775164311199891 := by
  unfold tailWord_619748
  simp only [CollatzResearch.WordTrace]
  refine ⟨11302033279383157688397949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15069377705844210251197265 11302033279383157688397949)
  ·
    refine ⟨4238262479768684133149231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11302033279383157688397949 4238262479768684133149231)
    ·
      refine ⟨6357393719653026199723847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4238262479768684133149231 6357393719653026199723847)
      ·
        refine ⟨9536090579479539299585771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6357393719653026199723847 9536090579479539299585771)
        ·
          refine ⟨14304135869219308949378657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9536090579479539299585771 14304135869219308949378657)
          ·
            refine ⟨10728101901914481712033993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14304135869219308949378657 10728101901914481712033993)
            ·
              refine ⟨8046076426435861284025495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10728101901914481712033993 8046076426435861284025495)
              ·
                refine ⟨12069114639653791926038243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8046076426435861284025495 12069114639653791926038243)
                ·
                  refine ⟨18103671959480687889057365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12069114639653791926038243 18103671959480687889057365)
                  ·
                    refine ⟨212152405775164311199891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18103671959480687889057365 212152405775164311199891)
                    ·
                      rfl

theorem cell22_619748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_619748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619748 prefixEnd_619748 := by exact prefixLift 619748
  have htrace : WordTrace (prefixWord ++ tailWord_619748) baseStart_619748 baseEnd_619748 := by
    simpa [prefixWord, tailWord_619748, baseEnd_619748] using wordTrace_append hprefix tailTrace_619748
  have hstable : (prefixWord ++ tailWord_619748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619748).length < 2 ^ (prefixWord ++ tailWord_619748).sum := by decide
  have hdescent : baseEnd_619748 < baseStart_619748 := by decide
  rcases family_descends (prefixWord ++ tailWord_619748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619780 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 7]
def baseStart_619780 : Nat := 118140960795 + 619780 * 2 ^ 59
def prefixEnd_619780 : Nat := 4983230072969 + 3 ^ 40 * 619780 * 2
def baseEnd_619780 : Nat := 70721120009708964799931

theorem tailTrace_619780 : CollatzResearch.WordTrace tailWord_619780 prefixEnd_619780 70721120009708964799931 := by
  unfold tailWord_619780
  simp only [CollatzResearch.WordTrace]
  refine ⟨11302616847325192420980397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15070155796433589894640529 11302616847325192420980397)
  ·
    refine ⟨4238481317746947157867649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11302616847325192420980397 4238481317746947157867649)
    ·
      refine ⟨3178860988310210368400737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4238481317746947157867649 3178860988310210368400737)
      ·
        refine ⟨2384145741232657776300553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3178860988310210368400737 2384145741232657776300553)
        ·
          refine ⟨1788109305924493332225415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2384145741232657776300553 1788109305924493332225415)
          ·
            refine ⟨2682163958886739998338123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788109305924493332225415 2682163958886739998338123)
            ·
              refine ⟨4023245938330109997507185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682163958886739998338123 4023245938330109997507185)
              ·
                refine ⟨3017434453747582498130389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4023245938330109997507185 3017434453747582498130389)
                ·
                  refine ⟨70721120009708964799931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3017434453747582498130389 70721120009708964799931)
                  ·
                    rfl

theorem cell22_619780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_619780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619780 prefixEnd_619780 := by exact prefixLift 619780
  have htrace : WordTrace (prefixWord ++ tailWord_619780) baseStart_619780 baseEnd_619780 := by
    simpa [prefixWord, tailWord_619780, baseEnd_619780] using wordTrace_append hprefix tailTrace_619780
  have hstable : (prefixWord ++ tailWord_619780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619780).length < 2 ^ (prefixWord ++ tailWord_619780).sum := by decide
  have hdescent : baseEnd_619780 < baseStart_619780 := by decide
  rcases family_descends (prefixWord ++ tailWord_619780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619827 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 1, 4]
def baseStart_619827 : Nat := 118140960795 + 619827 * 2 ^ 59
def prefixEnd_619827 : Nat := 4983230072969 + 3 ^ 40 * 619827 * 2
def baseEnd_619827 : Nat := 212179449089634438474649

theorem tailTrace_619827 : CollatzResearch.WordTrace tailWord_619827 prefixEnd_619827 212179449089634438474649 := by
  unfold tailWord_619827
  simp only [CollatzResearch.WordTrace]
  refine ⟨22606947925480111868921735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15071298616986741245947823 22606947925480111868921735)
  ·
    refine ⟨33910421888220167803382603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22606947925480111868921735 33910421888220167803382603)
    ·
      refine ⟨50865632832330251705073905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33910421888220167803382603 50865632832330251705073905)
      ·
        refine ⟨38149224624247688778805429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50865632832330251705073905 38149224624247688778805429)
        ·
          refine ⟨3576489808523220823013009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38149224624247688778805429 3576489808523220823013009)
          ·
            refine ⟨2682367356392415617259757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3576489808523220823013009 2682367356392415617259757)
            ·
              refine ⟨1005887758647155856472409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2682367356392415617259757 1005887758647155856472409)
              ·
                refine ⟨754415818985366892354307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1005887758647155856472409 754415818985366892354307)
                ·
                  refine ⟨1131623728478050338531461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754415818985366892354307 1131623728478050338531461)
                  ·
                    refine ⟨212179449089634438474649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1131623728478050338531461 212179449089634438474649)
                    ·
                      rfl

theorem cell22_619827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 4].length) (baseStart_619827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619827 prefixEnd_619827 := by exact prefixLift 619827
  have htrace : WordTrace (prefixWord ++ tailWord_619827) baseStart_619827 baseEnd_619827 := by
    simpa [prefixWord, tailWord_619827, baseEnd_619827] using wordTrace_append hprefix tailTrace_619827
  have hstable : (prefixWord ++ tailWord_619827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619827).length < 2 ^ (prefixWord ++ tailWord_619827).sum := by decide
  have hdescent : baseEnd_619827 < baseStart_619827 := by decide
  rcases family_descends (prefixWord ++ tailWord_619827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619840 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 1, 5]
def baseStart_619840 : Nat := 118140960795 + 619840 * 2 ^ 59
def prefixEnd_619840 : Nat := 4983230072969 + 3 ^ 40 * 619840 * 2
def baseEnd_619840 : Nat := 212183899255306737899609

theorem tailTrace_619840 : CollatzResearch.WordTrace tailWord_619840 prefixEnd_619840 212183899255306737899609 := by
  unfold tailWord_619840
  simp only [CollatzResearch.WordTrace]
  refine ⟨11303711037216507544572487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15071614716288676726096649 11303711037216507544572487)
  ·
    refine ⟨16955566555824761316858731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11303711037216507544572487 16955566555824761316858731)
    ·
      refine ⟨25433349833737141975288097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16955566555824761316858731 25433349833737141975288097)
      ·
        refine ⟨19075012375302856481466073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25433349833737141975288097 19075012375302856481466073)
        ·
          refine ⟨14306259281477142361099555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19075012375302856481466073 14306259281477142361099555)
          ·
            refine ⟨21459388922215713541649333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14306259281477142361099555 21459388922215713541649333)
            ·
              refine ⟨2011817711457723144529625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21459388922215713541649333 2011817711457723144529625)
              ·
                refine ⟨1508863283593292358397219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2011817711457723144529625 1508863283593292358397219)
                ·
                  refine ⟨2263294925389938537595829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1508863283593292358397219 2263294925389938537595829)
                  ·
                    refine ⟨212183899255306737899609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2263294925389938537595829 212183899255306737899609)
                    ·
                      rfl

theorem cell22_619840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_619840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619840 prefixEnd_619840 := by exact prefixLift 619840
  have htrace : WordTrace (prefixWord ++ tailWord_619840) baseStart_619840 baseEnd_619840 := by
    simpa [prefixWord, tailWord_619840, baseEnd_619840] using wordTrace_append hprefix tailTrace_619840
  have hstable : (prefixWord ++ tailWord_619840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619840).length < 2 ^ (prefixWord ++ tailWord_619840).sum := by decide
  have hdescent : baseEnd_619840 < baseStart_619840 := by decide
  rcases family_descends (prefixWord ++ tailWord_619840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619874 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_619874 : Nat := 118140960795 + 619874 * 2 ^ 59
def prefixEnd_619874 : Nat := 4983230072969 + 3 ^ 40 * 619874 * 2
def baseEnd_619874 : Nat := 212195538150141982549505

theorem tailTrace_619874 : CollatzResearch.WordTrace tailWord_619874 prefixEnd_619874 212195538150141982549505 := by
  unfold tailWord_619874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5652165539077459723970669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15072441437539892597255117 5652165539077459723970669)
  ·
    refine ⟨2119562077154047396489001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5652165539077459723970669 2119562077154047396489001)
    ·
      refine ⟨1589671557865535547366751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2119562077154047396489001 1589671557865535547366751)
      ·
        refine ⟨2384507336798303321050127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1589671557865535547366751 2384507336798303321050127)
        ·
          refine ⟨3576761005197454981575191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384507336798303321050127 3576761005197454981575191)
          ·
            refine ⟨5365141507796182472362787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576761005197454981575191 5365141507796182472362787)
            ·
              refine ⟨8047712261694273708544181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365141507796182472362787 8047712261694273708544181)
              ·
                refine ⟨754473024533838160176017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8047712261694273708544181 754473024533838160176017)
                ·
                  refine ⟨565854768400378620132013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 754473024533838160176017 565854768400378620132013)
                  ·
                    refine ⟨212195538150141982549505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 565854768400378620132013 212195538150141982549505)
                    ·
                      rfl

theorem cell22_619874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_619874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619874 prefixEnd_619874 := by exact prefixLift 619874
  have htrace : WordTrace (prefixWord ++ tailWord_619874) baseStart_619874 baseEnd_619874 := by
    simpa [prefixWord, tailWord_619874, baseEnd_619874] using wordTrace_append hprefix tailTrace_619874
  have hstable : (prefixWord ++ tailWord_619874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619874).length < 2 ^ (prefixWord ++ tailWord_619874).sum := by decide
  have hdescent : baseEnd_619874 < baseStart_619874 := by decide
  rcases family_descends (prefixWord ++ tailWord_619874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619915 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 7]
def baseStart_619915 : Nat := 118140960795 + 619915 * 2 ^ 59
def prefixEnd_619915 : Nat := 4983230072969 + 3 ^ 40 * 619915 * 2
def baseEnd_619915 : Nat := 70736524429343847424793

theorem tailTrace_619915 : CollatzResearch.WordTrace tailWord_619915 prefixEnd_619915 70736524429343847424793 := by
  unfold tailWord_619915
  simp only [CollatzResearch.WordTrace]
  refine ⟨22610157549161302898125199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15073438366107535265416799 22610157549161302898125199)
  ·
    refine ⟨33915236323741954347187799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22610157549161302898125199 33915236323741954347187799)
    ·
      refine ⟨50872854485612931520781699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33915236323741954347187799 50872854485612931520781699)
      ·
        refine ⟨76309281728419397281172549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50872854485612931520781699 76309281728419397281172549)
        ·
          refine ⟨14307990324078636990219853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76309281728419397281172549 14307990324078636990219853)
          ·
            refine ⟨5365496371529488871332445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14307990324078636990219853 5365496371529488871332445)
            ·
              refine ⟨2012061139323558326749667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5365496371529488871332445 2012061139323558326749667)
              ·
                refine ⟨3018091708985337490124501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2012061139323558326749667 3018091708985337490124501)
                ·
                  refine ⟨70736524429343847424793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3018091708985337490124501 70736524429343847424793)
                  ·
                    rfl

theorem cell22_619915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 7].length) (baseStart_619915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619915 prefixEnd_619915 := by exact prefixLift 619915
  have htrace : WordTrace (prefixWord ++ tailWord_619915) baseStart_619915 baseEnd_619915 := by
    simpa [prefixWord, tailWord_619915, baseEnd_619915] using wordTrace_append hprefix tailTrace_619915
  have hstable : (prefixWord ++ tailWord_619915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619915).length < 2 ^ (prefixWord ++ tailWord_619915).sum := by decide
  have hdescent : baseEnd_619915 < baseStart_619915 := by decide
  rcases family_descends (prefixWord ++ tailWord_619915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_619960 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 8]
def baseStart_619960 : Nat := 118140960795 + 619960 * 2 ^ 59
def prefixEnd_619960 : Nat := 4983230072969 + 3 ^ 40 * 619960 * 2
def baseEnd_619960 : Nat := 70741659235888808299747

theorem tailTrace_619960 : CollatzResearch.WordTrace tailWord_619960 prefixEnd_619960 70741659235888808299747 := by
  unfold tailWord_619960
  simp only [CollatzResearch.WordTrace]
  refine ⟨11305899416999137791756667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15074532555998850389008889 11305899416999137791756667)
  ·
    refine ⟨16958849125498706687635001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11305899416999137791756667 16958849125498706687635001)
    ·
      refine ⟨12719136844124030015726251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16958849125498706687635001 12719136844124030015726251)
      ·
        refine ⟨19078705266186045023589377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12719136844124030015726251 19078705266186045023589377)
        ·
          refine ⟨14309028949639533767692033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19078705266186045023589377 14309028949639533767692033)
          ·
            refine ⟨10731771712229650325769025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14309028949639533767692033 10731771712229650325769025)
            ·
              refine ⟨8048828784172237744326769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10731771712229650325769025 8048828784172237744326769)
              ·
                refine ⟨6036621588129178308245077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8048828784172237744326769 6036621588129178308245077)
                ·
                  refine ⟨70741659235888808299747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6036621588129178308245077 70741659235888808299747)
                  ·
                    rfl

theorem cell22_619960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_619960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_619960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_619960 prefixEnd_619960 := by exact prefixLift 619960
  have htrace : WordTrace (prefixWord ++ tailWord_619960) baseStart_619960 baseEnd_619960 := by
    simpa [prefixWord, tailWord_619960, baseEnd_619960] using wordTrace_append hprefix tailTrace_619960
  have hstable : (prefixWord ++ tailWord_619960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_619960).length < 2 ^ (prefixWord ++ tailWord_619960).sum := by decide
  have hdescent : baseEnd_619960 < baseStart_619960 := by decide
  rcases family_descends (prefixWord ++ tailWord_619960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620013 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_620013 : Nat := 118140960795 + 620013 * 2 ^ 59
def prefixEnd_620013 : Nat := 4983230072969 + 3 ^ 40 * 620013 * 2
def baseEnd_620013 : Nat := 212243120690791953324079

theorem tailTrace_620013 : CollatzResearch.WordTrace tailWord_620013 prefixEnd_620013 212243120690791953324079 := by
  unfold tailWord_620013
  simp only [CollatzResearch.WordTrace]
  refine ⟨22613731902806265635192693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15075821268537510423461795 22613731902806265635192693)
  ·
    refine ⟨2120037365888087403299315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22613731902806265635192693 2120037365888087403299315)
    ·
      refine ⟨3180056048832131104948973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2120037365888087403299315 3180056048832131104948973)
      ·
        refine ⟨1192521018312049164355865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3180056048832131104948973 1192521018312049164355865)
        ·
          refine ⟨894390763734036873266899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1192521018312049164355865 894390763734036873266899)
          ·
            refine ⟨1341586145601055309900349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894390763734036873266899 1341586145601055309900349)
            ·
              refine ⟨503094804600395741212631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1341586145601055309900349 503094804600395741212631)
              ·
                refine ⟨754642206900593611818947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503094804600395741212631 754642206900593611818947)
                ·
                  refine ⟨1131963310350890417728421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754642206900593611818947 1131963310350890417728421)
                  ·
                    refine ⟨212243120690791953324079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1131963310350890417728421 212243120690791953324079)
                    ·
                      rfl

theorem cell22_620013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_620013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620013 prefixEnd_620013 := by exact prefixLift 620013
  have htrace : WordTrace (prefixWord ++ tailWord_620013) baseStart_620013 baseEnd_620013 := by
    simpa [prefixWord, tailWord_620013, baseEnd_620013] using wordTrace_append hprefix tailTrace_620013
  have hstable : (prefixWord ++ tailWord_620013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620013).length < 2 ^ (prefixWord ++ tailWord_620013).sum := by decide
  have hdescent : baseEnd_620013 < baseStart_620013 := by decide
  rcases family_descends (prefixWord ++ tailWord_620013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620022 : List Nat := [5, 1, 1, 1, 2, 12]
def baseStart_620022 : Nat := 118140960795 + 620022 * 2 ^ 59
def prefixEnd_620022 : Nat := 4983230072969 + 3 ^ 40 * 620022 * 2
def baseEnd_620022 : Nat := 2620323476231097899371

theorem tailTrace_620022 : CollatzResearch.WordTrace tailWord_620022 prefixEnd_620022 2620323476231097899371 := by
  unfold tailWord_620022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413378759985853760766895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15076040106515773448180213 1413378759985853760766895)
  ·
    refine ⟨2120068139978780641150343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1413378759985853760766895 2120068139978780641150343)
    ·
      refine ⟨3180102209968170961725515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2120068139978780641150343 3180102209968170961725515)
      ·
        refine ⟨4770153314952256442588273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3180102209968170961725515 4770153314952256442588273)
        ·
          refine ⟨3577614986214192331941205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4770153314952256442588273 3577614986214192331941205)
          ·
            refine ⟨2620323476231097899371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3577614986214192331941205 2620323476231097899371)
            ·
              rfl

theorem cell22_620022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 12].length) (baseStart_620022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620022 prefixEnd_620022 := by exact prefixLift 620022
  have htrace : WordTrace (prefixWord ++ tailWord_620022) baseStart_620022 baseEnd_620022 := by
    simpa [prefixWord, tailWord_620022, baseEnd_620022] using wordTrace_append hprefix tailTrace_620022
  have hstable : (prefixWord ++ tailWord_620022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620022).length < 2 ^ (prefixWord ++ tailWord_620022).sum := by decide
  have hdescent : baseEnd_620022 < baseStart_620022 := by decide
  rcases family_descends (prefixWord ++ tailWord_620022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620039 : List Nat := [1, 1, 4, 3, 2, 3, 1, 7]
def baseStart_620039 : Nat := 118140960795 + 620039 * 2 ^ 59
def prefixEnd_620039 : Nat := 4983230072969 + 3 ^ 40 * 620039 * 2
def baseEnd_620039 : Nat := 23583557891348505797111

theorem tailTrace_620039 : CollatzResearch.WordTrace tailWord_620039 prefixEnd_620039 23583557891348505797111 := by
  unfold tailWord_620039
  simp only [CollatzResearch.WordTrace]
  refine ⟨22614680200712072075639171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15076453467141381383759447 22614680200712072075639171)
  ·
    refine ⟨33922020301068108113458757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22614680200712072075639171 33922020301068108113458757)
    ·
      refine ⟨6360378806450270271273517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33922020301068108113458757 6360378806450270271273517)
      ·
        refine ⟨2385142052418851351727569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6360378806450270271273517 2385142052418851351727569)
        ·
          refine ⟨1788856539314138513795677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2385142052418851351727569 1788856539314138513795677)
          ·
            refine ⟨670821202242801942673379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1788856539314138513795677 670821202242801942673379)
            ·
              refine ⟨1006231803364202914010069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670821202242801942673379 1006231803364202914010069)
              ·
                refine ⟨23583557891348505797111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1006231803364202914010069 23583557891348505797111)
                ·
                  rfl

theorem cell22_620039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 7].length) (baseStart_620039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620039 prefixEnd_620039 := by exact prefixLift 620039
  have htrace : WordTrace (prefixWord ++ tailWord_620039) baseStart_620039 baseEnd_620039 := by
    simpa [prefixWord, tailWord_620039, baseEnd_620039] using wordTrace_append hprefix tailTrace_620039
  have hstable : (prefixWord ++ tailWord_620039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620039).length < 2 ^ (prefixWord ++ tailWord_620039).sum := by decide
  have hdescent : baseEnd_620039 < baseStart_620039 := by decide
  rcases family_descends (prefixWord ++ tailWord_620039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620062 : List Nat := [4, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_620062 : Nat := 118140960795 + 620062 * 2 ^ 59
def prefixEnd_620062 : Nat := 4983230072969 + 3 ^ 40 * 620062 * 2
def baseEnd_620062 : Nat := 70753298130724052949643

theorem tailTrace_620062 : CollatzResearch.WordTrace tailWord_620062 prefixEnd_620062 70753298130724052949643 := by
  unfold tailWord_620062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2826939884953593375465805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15077012719752498002484293 2826939884953593375465805)
  ·
    refine ⟨1060102456857597515799677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2826939884953593375465805 1060102456857597515799677)
    ·
      refine ⟨397538421321599068424879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1060102456857597515799677 397538421321599068424879)
      ·
        refine ⟨596307631982398602637319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397538421321599068424879 596307631982398602637319)
        ·
          refine ⟨894461447973597903955979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596307631982398602637319 894461447973597903955979)
          ·
            refine ⟨1341692171960396855933969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894461447973597903955979 1341692171960396855933969)
            ·
              refine ⟨1006269128970297641950477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1341692171960396855933969 1006269128970297641950477)
              ·
                refine ⟨377350923363861615731429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006269128970297641950477 377350923363861615731429)
                ·
                  refine ⟨70753298130724052949643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377350923363861615731429 70753298130724052949643)
                  ·
                    rfl

theorem cell22_620062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_620062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620062 prefixEnd_620062 := by exact prefixLift 620062
  have htrace : WordTrace (prefixWord ++ tailWord_620062) baseStart_620062 baseEnd_620062 := by
    simpa [prefixWord, tailWord_620062, baseEnd_620062] using wordTrace_append hprefix tailTrace_620062
  have hstable : (prefixWord ++ tailWord_620062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620062).length < 2 ^ (prefixWord ++ tailWord_620062).sum := by decide
  have hdescent : baseEnd_620062 < baseStart_620062 := by decide
  rcases family_descends (prefixWord ++ tailWord_620062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620112 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 6]
def baseStart_620112 : Nat := 118140960795 + 620112 * 2 ^ 59
def prefixEnd_620112 : Nat := 4983230072969 + 3 ^ 40 * 620112 * 2
def baseEnd_620112 : Nat := 70759003471329565032925

theorem tailTrace_620112 : CollatzResearch.WordTrace tailWord_620112 prefixEnd_620112 70759003471329565032925 := by
  unfold tailWord_620112
  simp only [CollatzResearch.WordTrace]
  refine ⟨11308671364723802771523295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15078228486298403695364393 11308671364723802771523295)
  ·
    refine ⟨16963007047085704157284943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11308671364723802771523295 16963007047085704157284943)
    ·
      refine ⟨25444510570628556235927415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16963007047085704157284943 25444510570628556235927415)
      ·
        refine ⟨38166765855942834353891123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25444510570628556235927415 38166765855942834353891123)
        ·
          refine ⟨57250148783914251530836685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38166765855942834353891123 57250148783914251530836685)
          ·
            refine ⟨21468805793967844324063757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57250148783914251530836685 21468805793967844324063757)
            ·
              refine ⟨8050802172737941621523909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21468805793967844324063757 8050802172737941621523909)
              ·
                refine ⟨1509525407388364054035733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8050802172737941621523909 1509525407388364054035733)
                ·
                  refine ⟨70759003471329565032925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1509525407388364054035733 70759003471329565032925)
                  ·
                    rfl

theorem cell22_620112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 6].length) (baseStart_620112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620112 prefixEnd_620112 := by exact prefixLift 620112
  have htrace : WordTrace (prefixWord ++ tailWord_620112) baseStart_620112 baseEnd_620112 := by
    simpa [prefixWord, tailWord_620112, baseEnd_620112] using wordTrace_append hprefix tailTrace_620112
  have hstable : (prefixWord ++ tailWord_620112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620112).length < 2 ^ (prefixWord ++ tailWord_620112).sum := by decide
  have hdescent : baseEnd_620112 < baseStart_620112 := by decide
  rcases family_descends (prefixWord ++ tailWord_620112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620146 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 6]
def baseStart_620146 : Nat := 118140960795 + 620146 * 2 ^ 59
def prefixEnd_620146 : Nat := 4983230072969 + 3 ^ 40 * 620146 * 2
def baseEnd_620146 : Nat := 70762883102941313249557

theorem tailTrace_620146 : CollatzResearch.WordTrace tailWord_620146 prefixEnd_620146 70762883102941313249557 := by
  unfold tailWord_620146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5654645702831107337446073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15079055207549619566522861 5654645702831107337446073)
  ·
    refine ⟨4240984277123330503084555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5654645702831107337446073 4240984277123330503084555)
    ·
      refine ⟨6361476415684995754626833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4240984277123330503084555 6361476415684995754626833)
      ·
        refine ⟨4771107311763746815970125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6361476415684995754626833 4771107311763746815970125)
        ·
          refine ⟨1789165241911405055988797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4771107311763746815970125 1789165241911405055988797)
          ·
            refine ⟨670936965716776895995799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1789165241911405055988797 670936965716776895995799)
            ·
              refine ⟨1006405448575165343993699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670936965716776895995799 1006405448575165343993699)
              ·
                refine ⟨1509608172862748015990549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006405448575165343993699 1509608172862748015990549)
                ·
                  refine ⟨70762883102941313249557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1509608172862748015990549 70762883102941313249557)
                  ·
                    rfl

theorem cell22_620146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_620146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620146 prefixEnd_620146 := by exact prefixLift 620146
  have htrace : WordTrace (prefixWord ++ tailWord_620146) baseStart_620146 baseEnd_620146 := by
    simpa [prefixWord, tailWord_620146, baseEnd_620146] using wordTrace_append hprefix tailTrace_620146
  have hstable : (prefixWord ++ tailWord_620146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620146).length < 2 ^ (prefixWord ++ tailWord_620146).sum := by decide
  have hdescent : baseEnd_620146 < baseStart_620146 := by decide
  rcases family_descends (prefixWord ++ tailWord_620146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620174 : List Nat := [4, 1, 1, 3, 1, 2, 2, 8]
def baseStart_620174 : Nat := 118140960795 + 620174 * 2 ^ 59
def prefixEnd_620174 : Nat := 4983230072969 + 3 ^ 40 * 620174 * 2
def baseEnd_620174 : Nat := 23588692697893466672065

theorem tailTrace_620174 : CollatzResearch.WordTrace tailWord_620174 prefixEnd_620174 23588692697893466672065 := by
  unfold tailWord_620174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827450506902873766475447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15079736036815326754535717 2827450506902873766475447)
  ·
    refine ⟨4241175760354310649713171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2827450506902873766475447 4241175760354310649713171)
    ·
      refine ⟨6361763640531465974569757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4241175760354310649713171 6361763640531465974569757)
      ·
        refine ⟨2385661365199299740463659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6361763640531465974569757 2385661365199299740463659)
        ·
          refine ⟨3578492047798949610695489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385661365199299740463659 3578492047798949610695489)
          ·
            refine ⟨2683869035849212208021617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3578492047798949610695489 2683869035849212208021617)
            ·
              refine ⟨2012901776886909156016213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2683869035849212208021617 2012901776886909156016213)
              ·
                refine ⟨23588692697893466672065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2012901776886909156016213 23588692697893466672065)
                ·
                  rfl

theorem cell22_620174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_620174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620174 prefixEnd_620174 := by exact prefixLift 620174
  have htrace : WordTrace (prefixWord ++ tailWord_620174) baseStart_620174 baseEnd_620174 := by
    simpa [prefixWord, tailWord_620174, baseEnd_620174] using wordTrace_append hprefix tailTrace_620174
  have hstable : (prefixWord ++ tailWord_620174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620174).length < 2 ^ (prefixWord ++ tailWord_620174).sum := by decide
  have hdescent : baseEnd_620174 < baseStart_620174 := by decide
  rcases family_descends (prefixWord ++ tailWord_620174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620191 : List Nat := [1, 1, 2, 7, 2, 9]
def baseStart_620191 : Nat := 118140960795 + 620191 * 2 ^ 59
def prefixEnd_620191 : Nat := 4983230072969 + 3 ^ 40 * 620191 * 2
def baseEnd_620191 : Nat := 2621037700351343486093

theorem tailTrace_620191 : CollatzResearch.WordTrace tailWord_620191 prefixEnd_620191 2621037700351343486093 := by
  unfold tailWord_620191
  simp only [CollatzResearch.WordTrace]
  refine ⟨22620224096161402035172427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15080149397440934690114951 22620224096161402035172427)
  ·
    refine ⟨33930336144242103052758641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22620224096161402035172427 33930336144242103052758641)
    ·
      refine ⟨25447752108181577289568981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33930336144242103052758641 25447752108181577289568981)
      ·
        refine ⟨596431690035505717724273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 25447752108181577289568981 596431690035505717724273)
        ·
          refine ⟨447323767526629288293205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596431690035505717724273 447323767526629288293205)
          ·
            refine ⟨2621037700351343486093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 447323767526629288293205 2621037700351343486093)
            ·
              rfl

theorem cell22_620191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 9].length) (baseStart_620191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620191 prefixEnd_620191 := by exact prefixLift 620191
  have htrace : WordTrace (prefixWord ++ tailWord_620191) baseStart_620191 baseEnd_620191 := by
    simpa [prefixWord, tailWord_620191, baseEnd_620191] using wordTrace_append hprefix tailTrace_620191
  have hstable : (prefixWord ++ tailWord_620191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620191).length < 2 ^ (prefixWord ++ tailWord_620191).sum := by decide
  have hdescent : baseEnd_620191 < baseStart_620191 := by decide
  rcases family_descends (prefixWord ++ tailWord_620191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620253 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 7]
def baseStart_620253 : Nat := 118140960795 + 620253 * 2 ^ 59
def prefixEnd_620253 : Nat := 4983230072969 + 3 ^ 40 * 620253 * 2
def baseEnd_620253 : Nat := 70775092531837109107781

theorem tailTrace_620253 : CollatzResearch.WordTrace tailWord_620253 prefixEnd_620253 70775092531837109107781 := by
  unfold tailWord_620253
  simp only [CollatzResearch.WordTrace]
  refine ⟨22622485421936786623929413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15081656947957857749286275 22622485421936786623929413)
  ·
    refine ⟨4241716016613147491986765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22622485421936786623929413 4241716016613147491986765)
    ·
      refine ⟨1590643506229930309495037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4241716016613147491986765 1590643506229930309495037)
      ·
        refine ⟨596491314836223866060639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1590643506229930309495037 596491314836223866060639)
        ·
          refine ⟨894736972254335799090959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596491314836223866060639 894736972254335799090959)
          ·
            refine ⟨1342105458381503698636439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894736972254335799090959 1342105458381503698636439)
            ·
              refine ⟨2013158187572255547954659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342105458381503698636439 2013158187572255547954659)
              ·
                refine ⟨3019737281358383321931989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013158187572255547954659 3019737281358383321931989)
                ·
                  refine ⟨70775092531837109107781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3019737281358383321931989 70775092531837109107781)
                  ·
                    rfl

theorem cell22_620253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_620253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620253 prefixEnd_620253 := by exact prefixLift 620253
  have htrace : WordTrace (prefixWord ++ tailWord_620253) baseStart_620253 baseEnd_620253 := by
    simpa [prefixWord, tailWord_620253, baseEnd_620253] using wordTrace_append hprefix tailTrace_620253
  have hstable : (prefixWord ++ tailWord_620253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620253).length < 2 ^ (prefixWord ++ tailWord_620253).sum := by decide
  have hdescent : baseEnd_620253 < baseStart_620253 := by decide
  rcases family_descends (prefixWord ++ tailWord_620253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620296 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 6, 3]
def baseStart_620296 : Nat := 118140960795 + 620296 * 2 ^ 59
def prefixEnd_620296 : Nat := 4983230072969 + 3 ^ 40 * 620296 * 2
def baseEnd_620296 : Nat := 212339997374273548498211

theorem tailTrace_620296 : CollatzResearch.WordTrace tailWord_620296 prefixEnd_620296 212339997374273548498211 := by
  unfold tailWord_620296
  simp only [CollatzResearch.WordTrace]
  refine ⟨11312026880390502483872371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15082702507187336645163161 11312026880390502483872371)
  ·
    refine ⟨16968040320585753725808557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11312026880390502483872371 16968040320585753725808557)
    ·
      refine ⟨6363015120219657647178209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16968040320585753725808557 6363015120219657647178209)
      ·
        refine ⟨4772261340164743235383657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6363015120219657647178209 4772261340164743235383657)
        ·
          refine ⟨3579196005123557426537743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4772261340164743235383657 3579196005123557426537743)
          ·
            refine ⟨5368794007685336139806615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3579196005123557426537743 5368794007685336139806615)
            ·
              refine ⟨8053191011528004209709923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5368794007685336139806615 8053191011528004209709923)
              ·
                refine ⟨12079786517292006314564885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8053191011528004209709923 12079786517292006314564885)
                ·
                  refine ⟨566239992998062795995229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12079786517292006314564885 566239992998062795995229)
                  ·
                    refine ⟨212339997374273548498211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 566239992998062795995229 212339997374273548498211)
                    ·
                      rfl

theorem cell22_620296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_620296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620296 prefixEnd_620296 := by exact prefixLift 620296
  have htrace : WordTrace (prefixWord ++ tailWord_620296) baseStart_620296 baseEnd_620296 := by
    simpa [prefixWord, tailWord_620296, baseEnd_620296] using wordTrace_append hprefix tailTrace_620296
  have hstable : (prefixWord ++ tailWord_620296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620296).length < 2 ^ (prefixWord ++ tailWord_620296).sum := by decide
  have hdescent : baseEnd_620296 < baseStart_620296 := by decide
  rcases family_descends (prefixWord ++ tailWord_620296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620298 : List Nat := [3, 1, 2, 2, 1, 3, 3, 3, 4]
def baseStart_620298 : Nat := 118140960795 + 620298 * 2 ^ 59
def prefixEnd_620298 : Nat := 4983230072969 + 3 ^ 40 * 620298 * 2
def baseEnd_620298 : Nat := 70780227338382069982735

theorem tailTrace_620298 : CollatzResearch.WordTrace tailWord_620298 prefixEnd_620298 70780227338382069982735 := by
  unfold tailWord_620298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5656031676693439827329387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15082751137849172872878365 5656031676693439827329387)
  ·
    refine ⟨8484047515040159740994081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5656031676693439827329387 8484047515040159740994081)
    ·
      refine ⟨6363035636280119805745561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8484047515040159740994081 6363035636280119805745561)
      ·
        refine ⟨4772276727210089854309171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6363035636280119805745561 4772276727210089854309171)
        ·
          refine ⟨7158415090815134781463757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772276727210089854309171 7158415090815134781463757)
          ·
            refine ⟨2684405659055675543048909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7158415090815134781463757 2684405659055675543048909)
            ·
              refine ⟨1006652122145878328643341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2684405659055675543048909 1006652122145878328643341)
              ·
                refine ⟨377494545804704373241253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006652122145878328643341 377494545804704373241253)
                ·
                  refine ⟨70780227338382069982735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377494545804704373241253 70780227338382069982735)
                  ·
                    rfl

theorem cell22_620298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_620298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620298 prefixEnd_620298 := by exact prefixLift 620298
  have htrace : WordTrace (prefixWord ++ tailWord_620298) baseStart_620298 baseEnd_620298 := by
    simpa [prefixWord, tailWord_620298, baseEnd_620298] using wordTrace_append hprefix tailTrace_620298
  have hstable : (prefixWord ++ tailWord_620298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620298).length < 2 ^ (prefixWord ++ tailWord_620298).sum := by decide
  have hdescent : baseEnd_620298 < baseStart_620298 := by decide
  rcases family_descends (prefixWord ++ tailWord_620298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620309 : List Nat := [1, 3, 2, 1, 2, 3, 10]
def baseStart_620309 : Nat := 118140960795 + 620309 * 2 ^ 59
def prefixEnd_620309 : Nat := 4983230072969 + 3 ^ 40 * 620309 * 2
def baseEnd_620309 : Nat := 7864609168146142515673

theorem tailTrace_620309 : CollatzResearch.WordTrace tailWord_620309 prefixEnd_620309 7864609168146142515673 := by
  unfold tailWord_620309
  simp only [CollatzResearch.WordTrace]
  refine ⟨22624527909733908187967981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15083018606489272125311987 22624527909733908187967981)
  ·
    refine ⟨8484197966150215570487993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22624527909733908187967981 8484197966150215570487993)
    ·
      refine ⟨6363148474612661677865995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8484197966150215570487993 6363148474612661677865995)
      ·
        refine ⟨9544722711918992516798993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6363148474612661677865995 9544722711918992516798993)
        ·
          refine ⟨7158542033939244387599245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9544722711918992516798993 7158542033939244387599245)
          ·
            refine ⟨2684453262727216645349717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7158542033939244387599245 2684453262727216645349717)
            ·
              refine ⟨7864609168146142515673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2684453262727216645349717 7864609168146142515673)
              ·
                rfl

theorem cell22_620309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 10].length) (baseStart_620309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620309 prefixEnd_620309 := by exact prefixLift 620309
  have htrace : WordTrace (prefixWord ++ tailWord_620309) baseStart_620309 baseEnd_620309 := by
    simpa [prefixWord, tailWord_620309, baseEnd_620309] using wordTrace_append hprefix tailTrace_620309
  have hstable : (prefixWord ++ tailWord_620309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620309).length < 2 ^ (prefixWord ++ tailWord_620309).sum := by decide
  have hdescent : baseEnd_620309 < baseStart_620309 := by decide
  rcases family_descends (prefixWord ++ tailWord_620309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_620311 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 4, 4]
def baseStart_620311 : Nat := 118140960795 + 620311 * 2 ^ 59
def prefixEnd_620311 : Nat := 4983230072969 + 3 ^ 40 * 620311 * 2
def baseEnd_620311 : Nat := 212345132180818509373165

theorem tailTrace_620311 : CollatzResearch.WordTrace tailWord_620311 prefixEnd_620311 212345132180818509373165 := by
  unfold tailWord_620311
  simp only [CollatzResearch.WordTrace]
  refine ⟨22624600855726662529540787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15083067237151108353027191 22624600855726662529540787)
  ·
    refine ⟨33936901283589993794311181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22624600855726662529540787 33936901283589993794311181)
    ·
      refine ⟨12726337981346247672866693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33936901283589993794311181 12726337981346247672866693)
      ·
        refine ⟨2386188371502421438662505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12726337981346247672866693 2386188371502421438662505)
        ·
          refine ⟨1789641278626816078996879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2386188371502421438662505 1789641278626816078996879)
          ·
            refine ⟨2684461917940224118495319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789641278626816078996879 2684461917940224118495319)
            ·
              refine ⟨4026692876910336177742979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684461917940224118495319 4026692876910336177742979)
              ·
                refine ⟨6040039315365504266614469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4026692876910336177742979 6040039315365504266614469)
                ·
                  refine ⟨1132507371631032049990213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6040039315365504266614469 1132507371631032049990213)
                  ·
                    refine ⟨212345132180818509373165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1132507371631032049990213 212345132180818509373165)
                    ·
                      rfl

theorem cell22_620311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_620311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_620311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_620311 prefixEnd_620311 := by exact prefixLift 620311
  have htrace : WordTrace (prefixWord ++ tailWord_620311) baseStart_620311 baseEnd_620311 := by
    simpa [prefixWord, tailWord_620311, baseEnd_620311] using wordTrace_append hprefix tailTrace_620311
  have hstable : (prefixWord ++ tailWord_620311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_620311).length < 2 ^ (prefixWord ++ tailWord_620311).sum := by decide
  have hdescent : baseEnd_620311 < baseStart_620311 := by decide
  rcases family_descends (prefixWord ++ tailWord_620311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
