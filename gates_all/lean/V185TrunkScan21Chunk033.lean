import V185TrunkScan21Chunk032

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_398949 : List Nat := [1, 3, 1, 3, 3, 2, 1, 7]
def baseStart_398949 : Nat := 118140960795 + 398949 * 2 ^ 59
def prefixEnd_398949 : Nat := 4983230072969 + 3 ^ 40 * 398949 * 2
def baseEnd_398949 : Nat := 30348532389728125022633

theorem tailTrace_398949 : CollatzResearch.WordTrace tailWord_398949 prefixEnd_398949 30348532389728125022633 := by
  unfold tailWord_398949
  simp only [CollatzResearch.WordTrace]
  refine ⟨14550865431683382909799901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9700576954455588606533267 14550865431683382909799901)
  ·
    refine ⟨5456574536881268591174963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14550865431683382909799901 5456574536881268591174963)
    ·
      refine ⟨8184861805321902886762445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5456574536881268591174963 8184861805321902886762445)
      ·
        refine ⟨3069323176995713582535917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8184861805321902886762445 3069323176995713582535917)
        ·
          refine ⟨1150996191373392593450969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3069323176995713582535917 1150996191373392593450969)
          ·
            refine ⟨863247143530044445088227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1150996191373392593450969 863247143530044445088227)
            ·
              refine ⟨1294870715295066667632341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863247143530044445088227 1294870715295066667632341)
              ·
                refine ⟨30348532389728125022633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1294870715295066667632341 30348532389728125022633)
                ·
                  rfl

theorem cell21_398949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 7].length) (baseStart_398949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398949 prefixEnd_398949 := by exact prefixLift 398949
  have htrace : WordTrace (prefixWord ++ tailWord_398949) baseStart_398949 baseEnd_398949 := by
    simpa [prefixWord, tailWord_398949, baseEnd_398949] using wordTrace_append hprefix tailTrace_398949
  have hstable : (prefixWord ++ tailWord_398949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398949).length < 2 ^ (prefixWord ++ tailWord_398949).sum := by decide
  have hdescent : baseEnd_398949 < baseStart_398949 := by decide
  rcases family_descends (prefixWord ++ tailWord_398949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398966 : List Nat := [5, 1, 1, 2, 2, 3, 7]
def baseStart_398966 : Nat := 118140960795 + 398966 * 2 ^ 59
def prefixEnd_398966 : Nat := 4983230072969 + 3 ^ 40 * 398966 * 2
def baseEnd_398966 : Nat := 10116608533421791476059

theorem tailTrace_398966 : CollatzResearch.WordTrace tailWord_398966 prefixEnd_398966 10116608533421791476059 := by
  unfold tailWord_398966
  simp only [CollatzResearch.WordTrace]
  refine ⟨909467842038862175823047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9700990315081196542112501 909467842038862175823047)
  ·
    refine ⟨1364201763058293263734571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 909467842038862175823047 1364201763058293263734571)
    ·
      refine ⟨2046302644587439895601857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1364201763058293263734571 2046302644587439895601857)
      ·
        refine ⟨1534726983440579921701393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2046302644587439895601857 1534726983440579921701393)
        ·
          refine ⟨1151045237580434941276045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534726983440579921701393 1151045237580434941276045)
          ·
            refine ⟨431641964092663102978517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1151045237580434941276045 431641964092663102978517)
            ·
              refine ⟨10116608533421791476059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 431641964092663102978517 10116608533421791476059)
              ·
                rfl

theorem cell21_398966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 7].length) (baseStart_398966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398966 prefixEnd_398966 := by exact prefixLift 398966
  have htrace : WordTrace (prefixWord ++ tailWord_398966) baseStart_398966 baseEnd_398966 := by
    simpa [prefixWord, tailWord_398966, baseEnd_398966] using wordTrace_append hprefix tailTrace_398966
  have hstable : (prefixWord ++ tailWord_398966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398966).length < 2 ^ (prefixWord ++ tailWord_398966).sum := by decide
  have hdescent : baseEnd_398966 < baseStart_398966 := by decide
  rcases family_descends (prefixWord ++ tailWord_398966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399039 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 5]
def baseStart_399039 : Nat := 118140960795 + 399039 * 2 ^ 59
def prefixEnd_399039 : Nat := 4983230072969 + 3 ^ 40 * 399039 * 2
def baseEnd_399039 : Nat := 91066136395364218567715

theorem tailTrace_399039 : CollatzResearch.WordTrace tailWord_399039 prefixEnd_399039 91066136395364218567715 := by
  unfold tailWord_399039
  simp only [CollatzResearch.WordTrace]
  refine ⟨14554148001357328280576171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9702765334238218853717447 14554148001357328280576171)
  ·
    refine ⟨21831222002035992420864257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14554148001357328280576171 21831222002035992420864257)
    ·
      refine ⟨16373416501526994315648193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21831222002035992420864257 16373416501526994315648193)
      ·
        refine ⟨12280062376145245736736145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16373416501526994315648193 12280062376145245736736145)
        ·
          refine ⟨9210046782108934302552109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12280062376145245736736145 9210046782108934302552109)
          ·
            refine ⟨3453767543290850363457041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9210046782108934302552109 3453767543290850363457041)
            ·
              refine ⟨2590325657468137772592781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3453767543290850363457041 2590325657468137772592781)
              ·
                refine ⟨971372121550551664722293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2590325657468137772592781 971372121550551664722293)
                ·
                  refine ⟨91066136395364218567715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 971372121550551664722293 91066136395364218567715)
                  ·
                    rfl

theorem cell21_399039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_399039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399039 prefixEnd_399039 := by exact prefixLift 399039
  have htrace : WordTrace (prefixWord ++ tailWord_399039) baseStart_399039 baseEnd_399039 := by
    simpa [prefixWord, tailWord_399039, baseEnd_399039] using wordTrace_append hprefix tailTrace_399039
  have hstable : (prefixWord ++ tailWord_399039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399039).length < 2 ^ (prefixWord ++ tailWord_399039).sum := by decide
  have hdescent : baseEnd_399039 < baseStart_399039 := by decide
  rcases family_descends (prefixWord ++ tailWord_399039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399115 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 5]
def baseStart_399115 : Nat := 118140960795 + 399115 * 2 ^ 59
def prefixEnd_399115 : Nat := 4983230072969 + 3 ^ 40 * 399115 * 2
def baseEnd_399115 : Nat := 91083480630804975300893

theorem tailTrace_399115 : CollatzResearch.WordTrace tailWord_399115 prefixEnd_399115 91083480630804975300893 := by
  unfold tailWord_399115
  simp only [CollatzResearch.WordTrace]
  refine ⟨14556919949081993260342799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9704613299387995506895199 14556919949081993260342799)
  ·
    refine ⟨21835379923622989890514199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14556919949081993260342799 21835379923622989890514199)
    ·
      refine ⟨32753069885434484835771299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21835379923622989890514199 32753069885434484835771299)
      ·
        refine ⟨49129604828151727253656949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32753069885434484835771299 49129604828151727253656949)
        ·
          refine ⟨4605900452639224430030339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49129604828151727253656949 4605900452639224430030339)
          ·
            refine ⟨6908850678958836645045509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605900452639224430030339 6908850678958836645045509)
            ·
              refine ⟨1295409502304781870946033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6908850678958836645045509 1295409502304781870946033)
              ·
                refine ⟨971557126728586403209525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1295409502304781870946033 971557126728586403209525)
                ·
                  refine ⟨91083480630804975300893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 971557126728586403209525 91083480630804975300893)
                  ·
                    rfl

theorem cell21_399115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_399115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399115 prefixEnd_399115 := by exact prefixLift 399115
  have htrace : WordTrace (prefixWord ++ tailWord_399115) baseStart_399115 baseEnd_399115 := by
    simpa [prefixWord, tailWord_399115, baseEnd_399115] using wordTrace_append hprefix tailTrace_399115
  have hstable : (prefixWord ++ tailWord_399115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399115).length < 2 ^ (prefixWord ++ tailWord_399115).sum := by decide
  have hdescent : baseEnd_399115 < baseStart_399115 := by decide
  rcases family_descends (prefixWord ++ tailWord_399115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399160 : List Nat := [2, 1, 2, 1, 3, 3, 1, 8]
def baseStart_399160 : Nat := 118140960795 + 399160 * 2 ^ 59
def prefixEnd_399160 : Nat := 4983230072969 + 3 ^ 40 * 399160 * 2
def baseEnd_399160 : Nat := 30364583414631632350267

theorem tailTrace_399160 : CollatzResearch.WordTrace tailWord_399160 prefixEnd_399160 30364583414631632350267 := by
  unfold tailWord_399160
  simp only [CollatzResearch.WordTrace]
  refine ⟨7279280616959482972865467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9705707489279310630487289 7279280616959482972865467)
  ·
    refine ⟨10918920925439224459298201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7279280616959482972865467 10918920925439224459298201)
    ·
      refine ⟨8189190694079418344473651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10918920925439224459298201 8189190694079418344473651)
      ·
        refine ⟨12283786041119127516710477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8189190694079418344473651 12283786041119127516710477)
        ·
          refine ⟨4606419765419672818766429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12283786041119127516710477 4606419765419672818766429)
          ·
            refine ⟨1727407412032377307037411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4606419765419672818766429 1727407412032377307037411)
            ·
              refine ⟨2591111118048565960556117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727407412032377307037411 2591111118048565960556117)
              ·
                refine ⟨30364583414631632350267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2591111118048565960556117 30364583414631632350267)
                ·
                  rfl

theorem cell21_399160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_399160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399160 prefixEnd_399160 := by exact prefixLift 399160
  have htrace : WordTrace (prefixWord ++ tailWord_399160) baseStart_399160 baseEnd_399160 := by
    simpa [prefixWord, tailWord_399160, baseEnd_399160] using wordTrace_append hprefix tailTrace_399160
  have hstable : (prefixWord ++ tailWord_399160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399160).length < 2 ^ (prefixWord ++ tailWord_399160).sum := by decide
  have hdescent : baseEnd_399160 < baseStart_399160 := by decide
  rcases family_descends (prefixWord ++ tailWord_399160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399236 : List Nat := [2, 3, 2, 1, 1, 1, 2, 9]
def baseStart_399236 : Nat := 118140960795 + 399236 * 2 ^ 59
def prefixEnd_399236 : Nat := 4983230072969 + 3 ^ 40 * 399236 * 2
def baseEnd_399236 : Nat := 30370364826445217927993

theorem tailTrace_399236 : CollatzResearch.WordTrace tailWord_399236 prefixEnd_399236 30370364826445217927993 := by
  unfold tailWord_399236
  simp only [CollatzResearch.WordTrace]
  refine ⟨7280666590821815462748781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9707555454429087283665041 7280666590821815462748781)
  ·
    refine ⟨2730249971558180798530793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7280666590821815462748781 2730249971558180798530793)
    ·
      refine ⟨2047687478668635598898095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2730249971558180798530793 2047687478668635598898095)
      ·
        refine ⟨3071531218002953398347143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2047687478668635598898095 3071531218002953398347143)
        ·
          refine ⟨4607296827004430097520715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3071531218002953398347143 4607296827004430097520715)
          ·
            refine ⟨6910945240506645146281073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4607296827004430097520715 6910945240506645146281073)
            ·
              refine ⟨5183208930379983859710805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6910945240506645146281073 5183208930379983859710805)
              ·
                refine ⟨30370364826445217927993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5183208930379983859710805 30370364826445217927993)
                ·
                  rfl

theorem cell21_399236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_399236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399236 prefixEnd_399236 := by exact prefixLift 399236
  have htrace : WordTrace (prefixWord ++ tailWord_399236) baseStart_399236 baseEnd_399236 := by
    simpa [prefixWord, tailWord_399236, baseEnd_399236] using wordTrace_append hprefix tailTrace_399236
  have hstable : (prefixWord ++ tailWord_399236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399236).length < 2 ^ (prefixWord ++ tailWord_399236).sum := by decide
  have hdescent : baseEnd_399236 < baseStart_399236 := by decide
  rcases family_descends (prefixWord ++ tailWord_399236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399242 : List Nat := [3, 1, 2, 4, 2, 1, 2, 3, 3]
def baseStart_399242 : Nat := 118140960795 + 399242 * 2 ^ 59
def prefixEnd_399242 : Nat := 4983230072969 + 3 ^ 40 * 399242 * 2
def baseEnd_399242 : Nat := 91112463761080976683967

theorem tailTrace_399242 : CollatzResearch.WordTrace tailWord_399242 prefixEnd_399242 91112463761080976683967 := by
  unfold tailWord_399242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640388004905473487553995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9707701346414595966810653 3640388004905473487553995)
  ·
    refine ⟨5460582007358210231330993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3640388004905473487553995 5460582007358210231330993)
    ·
      refine ⟨4095436505518657673498245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5460582007358210231330993 4095436505518657673498245)
      ·
        refine ⟨767894344784748313780921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4095436505518657673498245 767894344784748313780921)
        ·
          refine ⟨575920758588561235335691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767894344784748313780921 575920758588561235335691)
          ·
            refine ⟨863881137882841853003537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575920758588561235335691 863881137882841853003537)
            ·
              refine ⟨647910853412131389752653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 863881137882841853003537 647910853412131389752653)
              ·
                refine ⟨242966570029549271157245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 647910853412131389752653 242966570029549271157245)
                ·
                  refine ⟨91112463761080976683967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242966570029549271157245 91112463761080976683967)
                  ·
                    rfl

theorem cell21_399242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_399242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399242 prefixEnd_399242 := by exact prefixLift 399242
  have htrace : WordTrace (prefixWord ++ tailWord_399242) baseStart_399242 baseEnd_399242 := by
    simpa [prefixWord, tailWord_399242, baseEnd_399242] using wordTrace_append hprefix tailTrace_399242
  have hstable : (prefixWord ++ tailWord_399242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399242).length < 2 ^ (prefixWord ++ tailWord_399242).sum := by decide
  have hdescent : baseEnd_399242 < baseStart_399242 := by decide
  rcases family_descends (prefixWord ++ tailWord_399242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399318 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_399318 : Nat := 118140960795 + 399318 * 2 ^ 59
def prefixEnd_399318 : Nat := 4983230072969 + 3 ^ 40 * 399318 * 2
def baseEnd_399318 : Nat := 91129807996521733417145

theorem tailTrace_399318 : CollatzResearch.WordTrace tailWord_399318 prefixEnd_399318 91129807996521733417145 := by
  unfold tailWord_399318
  simp only [CollatzResearch.WordTrace]
  refine ⟨910270247959159933123913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9709549311564372619988405 910270247959159933123913)
  ·
    refine ⟨682702685969369949842935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 910270247959159933123913 682702685969369949842935)
    ·
      refine ⟨1024054028954054924764403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682702685969369949842935 1024054028954054924764403)
      ·
        refine ⟨1536081043431082387146605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1024054028954054924764403 1536081043431082387146605)
        ·
          refine ⟨576030391286655895179977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1536081043431082387146605 576030391286655895179977)
          ·
            refine ⟨432022793464991921384983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576030391286655895179977 432022793464991921384983)
            ·
              refine ⟨648034190197487882077475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432022793464991921384983 648034190197487882077475)
              ·
                refine ⟨972051285296231823116213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648034190197487882077475 972051285296231823116213)
                ·
                  refine ⟨91129807996521733417145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 972051285296231823116213 91129807996521733417145)
                  ·
                    rfl

theorem cell21_399318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_399318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399318 prefixEnd_399318 := by exact prefixLift 399318
  have htrace : WordTrace (prefixWord ++ tailWord_399318) baseStart_399318 baseEnd_399318 := by
    simpa [prefixWord, tailWord_399318, baseEnd_399318] using wordTrace_append hprefix tailTrace_399318
  have hstable : (prefixWord ++ tailWord_399318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399318).length < 2 ^ (prefixWord ++ tailWord_399318).sum := by decide
  have hdescent : baseEnd_399318 < baseStart_399318 := by decide
  rcases family_descends (prefixWord ++ tailWord_399318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399357 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 8]
def baseStart_399357 : Nat := 118140960795 + 399357 * 2 ^ 59
def prefixEnd_399357 : Nat := 4983230072969 + 3 ^ 40 * 399357 * 2
def baseEnd_399357 : Nat := 91138708327866332267065

theorem tailTrace_399357 : CollatzResearch.WordTrace tailWord_399357 prefixEnd_399357 91138708327866332267065 := by
  unfold tailWord_399357
  simp only [CollatzResearch.WordTrace]
  refine ⟨14565746414205268590652325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9710497609470179060434883 14565746414205268590652325)
  ·
    refine ⟨2731077452663487860747311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14565746414205268590652325 2731077452663487860747311)
    ·
      refine ⟨4096616178995231791120967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2731077452663487860747311 4096616178995231791120967)
      ·
        refine ⟨6144924268492847686681451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4096616178995231791120967 6144924268492847686681451)
        ·
          refine ⟨9217386402739271530022177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6144924268492847686681451 9217386402739271530022177)
          ·
            refine ⟨6913039802054453647516633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9217386402739271530022177 6913039802054453647516633)
            ·
              refine ⟨5184779851540840235637475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6913039802054453647516633 5184779851540840235637475)
              ·
                refine ⟨7777169777311260353456213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5184779851540840235637475 7777169777311260353456213)
                ·
                  refine ⟨91138708327866332267065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7777169777311260353456213 91138708327866332267065)
                  ·
                    rfl

theorem cell21_399357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_399357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399357 prefixEnd_399357 := by exact prefixLift 399357
  have htrace : WordTrace (prefixWord ++ tailWord_399357) baseStart_399357 baseEnd_399357 := by
    simpa [prefixWord, tailWord_399357, baseEnd_399357] using wordTrace_append hprefix tailTrace_399357
  have hstable : (prefixWord ++ tailWord_399357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399357).length < 2 ^ (prefixWord ++ tailWord_399357).sum := by decide
  have hdescent : baseEnd_399357 < baseStart_399357 := by decide
  rcases family_descends (prefixWord ++ tailWord_399357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399380 : List Nat := [2, 4, 3, 2, 2, 1, 1, 6]
def baseStart_399380 : Nat := 118140960795 + 399380 * 2 ^ 59
def prefixEnd_399380 : Nat := 4983230072969 + 3 ^ 40 * 399380 * 2
def baseEnd_399380 : Nat := 30381319080407801127895

theorem tailTrace_399380 : CollatzResearch.WordTrace tailWord_399380 prefixEnd_399380 30381319080407801127895 := by
  unfold tailWord_399380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7283292646560971759369797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9711056862081295679159729 7283292646560971759369797)
  ·
    refine ⟨1365617371230182204881837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7283292646560971759369797 1365617371230182204881837)
    ·
      refine ⟨512106514211318326830689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1365617371230182204881837 512106514211318326830689)
      ·
        refine ⟨384079885658488745123017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 512106514211318326830689 384079885658488745123017)
        ·
          refine ⟨288059914243866558842263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384079885658488745123017 288059914243866558842263)
          ·
            refine ⟨432089871365799838263395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288059914243866558842263 432089871365799838263395)
            ·
              refine ⟨648134807048699757395093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432089871365799838263395 648134807048699757395093)
              ·
                refine ⟨30381319080407801127895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 648134807048699757395093 30381319080407801127895)
                ·
                  rfl

theorem cell21_399380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 6].length) (baseStart_399380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399380 prefixEnd_399380 := by exact prefixLift 399380
  have htrace : WordTrace (prefixWord ++ tailWord_399380) baseStart_399380 baseEnd_399380 := by
    simpa [prefixWord, tailWord_399380, baseEnd_399380] using wordTrace_append hprefix tailTrace_399380
  have hstable : (prefixWord ++ tailWord_399380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399380).length < 2 ^ (prefixWord ++ tailWord_399380).sum := by decide
  have hdescent : baseEnd_399380 < baseStart_399380 := by decide
  rcases family_descends (prefixWord ++ tailWord_399380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399433 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 6]
def baseStart_399433 : Nat := 118140960795 + 399433 * 2 ^ 59
def prefixEnd_399433 : Nat := 4983230072969 + 3 ^ 40 * 399433 * 2
def baseEnd_399433 : Nat := 91156052563307089000243

theorem tailTrace_399433 : CollatzResearch.WordTrace tailWord_399433 prefixEnd_399433 91156052563307089000243 := by
  unfold tailWord_399433
  simp only [CollatzResearch.WordTrace]
  refine ⟨14568518361929933570418953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9712345574619955713612635 14568518361929933570418953)
  ·
    refine ⟨10926388771447450177814215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14568518361929933570418953 10926388771447450177814215)
    ·
      refine ⟨16389583157171175266721323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10926388771447450177814215 16389583157171175266721323)
      ·
        refine ⟨24584374735756762900081985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16389583157171175266721323 24584374735756762900081985)
        ·
          refine ⟨18438281051817572175061489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24584374735756762900081985 18438281051817572175061489)
          ·
            refine ⟨13828710788863179131296117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18438281051817572175061489 13828710788863179131296117)
            ·
              refine ⟨1296441636455923043559011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13828710788863179131296117 1296441636455923043559011)
              ·
                refine ⟨1944662454683884565338517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296441636455923043559011 1944662454683884565338517)
                ·
                  refine ⟨91156052563307089000243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1944662454683884565338517 91156052563307089000243)
                  ·
                    rfl

theorem cell21_399433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_399433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399433 prefixEnd_399433 := by exact prefixLift 399433
  have htrace : WordTrace (prefixWord ++ tailWord_399433) baseStart_399433 baseEnd_399433 := by
    simpa [prefixWord, tailWord_399433, baseEnd_399433] using wordTrace_append hprefix tailTrace_399433
  have hstable : (prefixWord ++ tailWord_399433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399433).length < 2 ^ (prefixWord ++ tailWord_399433).sum := by decide
  have hdescent : baseEnd_399433 < baseStart_399433 := by decide
  rcases family_descends (prefixWord ++ tailWord_399433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399436 : List Nat := [2, 2, 1, 3, 1, 1, 4, 4, 3]
def baseStart_399436 : Nat := 118140960795 + 399436 * 2 ^ 59
def prefixEnd_399436 : Nat := 4983230072969 + 3 ^ 40 * 399436 * 2
def baseEnd_399436 : Nat := 91156737204179750450237

theorem tailTrace_399436 : CollatzResearch.WordTrace tailWord_399436 prefixEnd_399436 91156737204179750450237 := by
  unfold tailWord_399436
  simp only [CollatzResearch.WordTrace]
  refine ⟨7284313890459532541389081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9712418520612710055185441 7284313890459532541389081)
  ·
    refine ⟨5463235417844649406041811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7284313890459532541389081 5463235417844649406041811)
    ·
      refine ⟨8194853126766974109062717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5463235417844649406041811 8194853126766974109062717)
      ·
        refine ⟨3073069922537615290898519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8194853126766974109062717 3073069922537615290898519)
        ·
          refine ⟨4609604883806422936347779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3073069922537615290898519 4609604883806422936347779)
          ·
            refine ⟨6914407325709634404521669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609604883806422936347779 6914407325709634404521669)
            ·
              refine ⟨1296451373570556450847813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6914407325709634404521669 1296451373570556450847813)
              ·
                refine ⟨243084632544479334533965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1296451373570556450847813 243084632544479334533965)
                ·
                  refine ⟨91156737204179750450237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243084632544479334533965 91156737204179750450237)
                  ·
                    rfl

theorem cell21_399436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_399436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399436 prefixEnd_399436 := by exact prefixLift 399436
  have htrace : WordTrace (prefixWord ++ tailWord_399436) baseStart_399436 baseEnd_399436 := by
    simpa [prefixWord, tailWord_399436, baseEnd_399436] using wordTrace_append hprefix tailTrace_399436
  have hstable : (prefixWord ++ tailWord_399436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399436).length < 2 ^ (prefixWord ++ tailWord_399436).sum := by decide
  have hdescent : baseEnd_399436 < baseStart_399436 := by decide
  rcases family_descends (prefixWord ++ tailWord_399436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399495 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 5]
def baseStart_399495 : Nat := 118140960795 + 399495 * 2 ^ 59
def prefixEnd_399495 : Nat := 4983230072969 + 3 ^ 40 * 399495 * 2
def baseEnd_399495 : Nat := 91170201808008758966783

theorem tailTrace_399495 : CollatzResearch.WordTrace tailWord_399495 prefixEnd_399495 91170201808008758966783 := by
  unfold tailWord_399495
  simp only [CollatzResearch.WordTrace]
  refine ⟨14570779687705318159175939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9713853125136878772783959 14570779687705318159175939)
  ·
    refine ⟨21856169531557977238763909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14570779687705318159175939 21856169531557977238763909)
    ·
      refine ⟨4098031787167120732268233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21856169531557977238763909 4098031787167120732268233)
      ·
        refine ⟨3073523840375340549201175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4098031787167120732268233 3073523840375340549201175)
        ·
          refine ⟨4610285760563010823801763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3073523840375340549201175 4610285760563010823801763)
          ·
            refine ⟨6915428640844516235702645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610285760563010823801763 6915428640844516235702645)
            ·
              refine ⟨648321435079173397097123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6915428640844516235702645 648321435079173397097123)
              ·
                refine ⟨972482152618760095645685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648321435079173397097123 972482152618760095645685)
                ·
                  refine ⟨91170201808008758966783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 972482152618760095645685 91170201808008758966783)
                  ·
                    rfl

theorem cell21_399495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 5].length) (baseStart_399495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399495 prefixEnd_399495 := by exact prefixLift 399495
  have htrace : WordTrace (prefixWord ++ tailWord_399495) baseStart_399495 baseEnd_399495 := by
    simpa [prefixWord, tailWord_399495, baseEnd_399495] using wordTrace_append hprefix tailTrace_399495
  have hstable : (prefixWord ++ tailWord_399495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399495).length < 2 ^ (prefixWord ++ tailWord_399495).sum := by decide
  have hdescent : baseEnd_399495 < baseStart_399495 := by decide
  rcases family_descends (prefixWord ++ tailWord_399495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399585 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 6]
def baseStart_399585 : Nat := 118140960795 + 399585 * 2 ^ 59
def prefixEnd_399585 : Nat := 4983230072969 + 3 ^ 40 * 399585 * 2
def baseEnd_399585 : Nat := 91190741034188602466599

theorem tailTrace_399585 : CollatzResearch.WordTrace tailWord_399585 prefixEnd_399585 91190741034188602466599 := by
  unfold tailWord_399585
  simp only [CollatzResearch.WordTrace]
  refine ⟨14574062257379263529952209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9716041504919509019968139 14574062257379263529952209)
  ·
    refine ⟨10930546693034447647464157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14574062257379263529952209 10930546693034447647464157)
    ·
      refine ⟨4098955009887917867799059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10930546693034447647464157 4098955009887917867799059)
      ·
        refine ⟨6148432514831876801698589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4098955009887917867799059 6148432514831876801698589)
        ·
          refine ⟨2305662193061953800636971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6148432514831876801698589 2305662193061953800636971)
          ·
            refine ⟨3458493289592930700955457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305662193061953800636971 3458493289592930700955457)
            ·
              refine ⟨2593869967194698025716593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3458493289592930700955457 2593869967194698025716593)
              ·
                refine ⟨1945402475396023519287445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2593869967194698025716593 1945402475396023519287445)
                ·
                  refine ⟨91190741034188602466599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1945402475396023519287445 91190741034188602466599)
                  ·
                    rfl

theorem cell21_399585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_399585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399585 prefixEnd_399585 := by exact prefixLift 399585
  have htrace : WordTrace (prefixWord ++ tailWord_399585) baseStart_399585 baseEnd_399585 := by
    simpa [prefixWord, tailWord_399585, baseEnd_399585] using wordTrace_append hprefix tailTrace_399585
  have hstable : (prefixWord ++ tailWord_399585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399585).length < 2 ^ (prefixWord ++ tailWord_399585).sum := by decide
  have hdescent : baseEnd_399585 < baseStart_399585 := by decide
  rcases family_descends (prefixWord ++ tailWord_399585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399602 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_399602 : Nat := 118140960795 + 399602 * 2 ^ 59
def prefixEnd_399602 : Nat := 4983230072969 + 3 ^ 40 * 399602 * 2
def baseEnd_399602 : Nat := 91194620665800350683231

theorem tailTrace_399602 : CollatzResearch.WordTrace tailWord_399602 prefixEnd_399602 91194620665800350683231 := by
  unfold tailWord_399602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3643670574579418858330265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9716454865545116955547373 3643670574579418858330265)
  ·
    refine ⟨2732752930934564143747699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3643670574579418858330265 2732752930934564143747699)
    ·
      refine ⟨4099129396401846215621549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2732752930934564143747699 4099129396401846215621549)
      ·
        refine ⟨1537173523650692330858081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4099129396401846215621549 1537173523650692330858081)
        ·
          refine ⟨1152880142738019248143561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1537173523650692330858081 1152880142738019248143561)
          ·
            refine ⟨864660107053514436107671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1152880142738019248143561 864660107053514436107671)
            ·
              refine ⟨1296990160580271654161507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864660107053514436107671 1296990160580271654161507)
              ·
                refine ⟨1945485240870407481242261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296990160580271654161507 1945485240870407481242261)
                ·
                  refine ⟨91194620665800350683231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1945485240870407481242261 91194620665800350683231)
                  ·
                    rfl

theorem cell21_399602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_399602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399602 prefixEnd_399602 := by exact prefixLift 399602
  have htrace : WordTrace (prefixWord ++ tailWord_399602) baseStart_399602 baseEnd_399602 := by
    simpa [prefixWord, tailWord_399602, baseEnd_399602] using wordTrace_append hprefix tailTrace_399602
  have hstable : (prefixWord ++ tailWord_399602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399602).length < 2 ^ (prefixWord ++ tailWord_399602).sum := by decide
  have hdescent : baseEnd_399602 < baseStart_399602 := by decide
  rcases family_descends (prefixWord ++ tailWord_399602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399633 : List Nat := [1, 2, 2, 1, 1, 7, 2, 5]
def baseStart_399633 : Nat := 118140960795 + 399633 * 2 ^ 59
def prefixEnd_399633 : Nat := 4983230072969 + 3 ^ 40 * 399633 * 2
def baseEnd_399633 : Nat := 30400565096050395222167

theorem tailTrace_399633 : CollatzResearch.WordTrace tailWord_399633 prefixEnd_399633 30400565096050395222167 := by
  unfold tailWord_399633
  simp only [CollatzResearch.WordTrace]
  refine ⟨14575812961205367727699553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9717208640803578485133035 14575812961205367727699553)
  ·
    refine ⟨10931859720904025795774665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14575812961205367727699553 10931859720904025795774665)
    ·
      refine ⟨8198894790678019346830999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10931859720904025795774665 8198894790678019346830999)
      ·
        refine ⟨12298342186017029020246499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8198894790678019346830999 12298342186017029020246499)
        ·
          refine ⟨18447513279025543530369749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12298342186017029020246499 18447513279025543530369749)
          ·
            refine ⟨432363592477161176493041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 18447513279025543530369749 432363592477161176493041)
            ·
              refine ⟨324272694357870882369781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432363592477161176493041 324272694357870882369781)
              ·
                refine ⟨30400565096050395222167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 324272694357870882369781 30400565096050395222167)
                ·
                  rfl

theorem cell21_399633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 5].length) (baseStart_399633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399633 prefixEnd_399633 := by exact prefixLift 399633
  have htrace : WordTrace (prefixWord ++ tailWord_399633) baseStart_399633 baseEnd_399633 := by
    simpa [prefixWord, tailWord_399633, baseEnd_399633] using wordTrace_append hprefix tailTrace_399633
  have hstable : (prefixWord ++ tailWord_399633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399633).length < 2 ^ (prefixWord ++ tailWord_399633).sum := by decide
  have hdescent : baseEnd_399633 < baseStart_399633 := by decide
  rcases family_descends (prefixWord ++ tailWord_399633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399723 : List Nat := [1, 1, 1, 1, 2, 2, 2, 8, 3]
def baseStart_399723 : Nat := 118140960795 + 399723 * 2 ^ 59
def prefixEnd_399723 : Nat := 4983230072969 + 3 ^ 40 * 399723 * 2
def baseEnd_399723 : Nat := 91222234514331029166317

theorem tailTrace_399723 : CollatzResearch.WordTrace tailWord_399723 prefixEnd_399723 91222234514331029166317 := by
  unfold tailWord_399723
  simp only [CollatzResearch.WordTrace]
  refine ⟨14579095530879313098475823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9719397020586208732317215 14579095530879313098475823)
  ·
    refine ⟨21868643296318969647713735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14579095530879313098475823 21868643296318969647713735)
    ·
      refine ⟨32802964944478454471570603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21868643296318969647713735 32802964944478454471570603)
      ·
        refine ⟨49204447416717681707355905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32802964944478454471570603 49204447416717681707355905)
        ·
          refine ⟨36903335562538261280516929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49204447416717681707355905 36903335562538261280516929)
          ·
            refine ⟨27677501671903695960387697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36903335562538261280516929 27677501671903695960387697)
            ·
              refine ⟨20758126253927771970290773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27677501671903695960387697 20758126253927771970290773)
              ·
                refine ⟨243259292038216077776845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 20758126253927771970290773 243259292038216077776845)
                ·
                  refine ⟨91222234514331029166317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243259292038216077776845 91222234514331029166317)
                  ·
                    rfl

theorem cell21_399723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 8, 3].length) (baseStart_399723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399723 prefixEnd_399723 := by exact prefixLift 399723
  have htrace : WordTrace (prefixWord ++ tailWord_399723) baseStart_399723 baseEnd_399723 := by
    simpa [prefixWord, tailWord_399723, baseEnd_399723] using wordTrace_append hprefix tailTrace_399723
  have hstable : (prefixWord ++ tailWord_399723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399723).length < 2 ^ (prefixWord ++ tailWord_399723).sum := by decide
  have hdescent : baseEnd_399723 < baseStart_399723 := by decide
  rcases family_descends (prefixWord ++ tailWord_399723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399768 : List Nat := [2, 1, 2, 5, 1, 2, 8]
def baseStart_399768 : Nat := 118140960795 + 399768 * 2 ^ 59
def prefixEnd_399768 : Nat := 4983230072969 + 3 ^ 40 * 399768 * 2
def baseEnd_399768 : Nat := 10136944903046772324025

theorem tailTrace_399768 : CollatzResearch.WordTrace tailWord_399768 prefixEnd_399768 10136944903046772324025 := by
  unfold tailWord_399768
  simp only [CollatzResearch.WordTrace]
  refine ⟨7290368407858142891931979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9720491210477523855909305 7290368407858142891931979)
  ·
    refine ⟨10935552611787214337897969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7290368407858142891931979 10935552611787214337897969)
    ·
      refine ⟨8201664458840410753423477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10935552611787214337897969 8201664458840410753423477)
      ·
        refine ⟨768906043016288508133451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8201664458840410753423477 768906043016288508133451)
        ·
          refine ⟨1153359064524432762200177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768906043016288508133451 1153359064524432762200177)
          ·
            refine ⟨865019298393324571650133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1153359064524432762200177 865019298393324571650133)
            ·
              refine ⟨10136944903046772324025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 865019298393324571650133 10136944903046772324025)
              ·
                rfl

theorem cell21_399768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 8].length) (baseStart_399768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399768 prefixEnd_399768 := by exact prefixLift 399768
  have htrace : WordTrace (prefixWord ++ tailWord_399768) baseStart_399768 baseEnd_399768 := by
    simpa [prefixWord, tailWord_399768, baseEnd_399768] using wordTrace_append hprefix tailTrace_399768
  have hstable : (prefixWord ++ tailWord_399768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399768).length < 2 ^ (prefixWord ++ tailWord_399768).sum := by decide
  have hdescent : baseEnd_399768 < baseStart_399768 := by decide
  rcases family_descends (prefixWord ++ tailWord_399768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399816 : List Nat := [2, 1, 3, 1, 3, 2, 3, 3, 3]
def baseStart_399816 : Nat := 118140960795 + 399816 * 2 ^ 59
def prefixEnd_399816 : Nat := 4983230072969 + 3 ^ 40 * 399816 * 2
def baseEnd_399816 : Nat := 91243458381383534116127

theorem tailTrace_399816 : CollatzResearch.WordTrace tailWord_399816 prefixEnd_399816 91243458381383534116127 := by
  unfold tailWord_399816
  simp only [CollatzResearch.WordTrace]
  refine ⟨7291243759771194990805651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9721658346361593321074201 7291243759771194990805651)
  ·
    refine ⟨10936865639656792486208477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7291243759771194990805651 10936865639656792486208477)
    ·
      refine ⟨4101324614871297182328179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10936865639656792486208477 4101324614871297182328179)
      ·
        refine ⟨6151986922306945773492269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4101324614871297182328179 6151986922306945773492269)
        ·
          refine ⟨2306995095865104665059601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6151986922306945773492269 2306995095865104665059601)
          ·
            refine ⟨1730246321898828498794701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2306995095865104665059601 1730246321898828498794701)
            ·
              refine ⟨648842370712060687048013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1730246321898828498794701 648842370712060687048013)
              ·
                refine ⟨243315889017022757643005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 648842370712060687048013 243315889017022757643005)
                ·
                  refine ⟨91243458381383534116127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243315889017022757643005 91243458381383534116127)
                  ·
                    rfl

theorem cell21_399816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 3].length) (baseStart_399816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399816 prefixEnd_399816 := by exact prefixLift 399816
  have htrace : WordTrace (prefixWord ++ tailWord_399816) baseStart_399816 baseEnd_399816 := by
    simpa [prefixWord, tailWord_399816, baseEnd_399816] using wordTrace_append hprefix tailTrace_399816
  have hstable : (prefixWord ++ tailWord_399816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399816).length < 2 ^ (prefixWord ++ tailWord_399816).sum := by decide
  have hdescent : baseEnd_399816 < baseStart_399816 := by decide
  rcases family_descends (prefixWord ++ tailWord_399816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399830 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_399830 : Nat := 118140960795 + 399830 * 2 ^ 59
def prefixEnd_399830 : Nat := 4983230072969 + 3 ^ 40 * 399830 * 2
def baseEnd_399830 : Nat := 91246653372122620882765

theorem tailTrace_399830 : CollatzResearch.WordTrace tailWord_399830 prefixEnd_399830 91246653372122620882765 := by
  unfold tailWord_399830
  simp only [CollatzResearch.WordTrace]
  refine ⟨911437383843229398288809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9721998760994446915080629 911437383843229398288809)
  ·
    refine ⟨683578037882422048716607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 911437383843229398288809 683578037882422048716607)
    ·
      refine ⟨1025367056823633073074911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 683578037882422048716607 1025367056823633073074911)
      ·
        refine ⟨1538050585235449609612367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025367056823633073074911 1538050585235449609612367)
        ·
          refine ⟨2307075877853174414418551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538050585235449609612367 2307075877853174414418551)
          ·
            refine ⟨3460613816779761621627827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307075877853174414418551 3460613816779761621627827)
            ·
              refine ⟨5190920725169642432441741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460613816779761621627827 5190920725169642432441741)
              ·
                refine ⟨1946595271938615912165653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5190920725169642432441741 1946595271938615912165653)
                ·
                  refine ⟨91246653372122620882765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1946595271938615912165653 91246653372122620882765)
                  ·
                    rfl

theorem cell21_399830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_399830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399830 prefixEnd_399830 := by exact prefixLift 399830
  have htrace : WordTrace (prefixWord ++ tailWord_399830) baseStart_399830 baseEnd_399830 := by
    simpa [prefixWord, tailWord_399830, baseEnd_399830] using wordTrace_append hprefix tailTrace_399830
  have hstable : (prefixWord ++ tailWord_399830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399830).length < 2 ^ (prefixWord ++ tailWord_399830).sum := by decide
  have hdescent : baseEnd_399830 < baseStart_399830 := by decide
  rcases family_descends (prefixWord ++ tailWord_399830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399875 : List Nat := [1, 1, 1, 3, 2, 1, 4, 5, 3]
def baseStart_399875 : Nat := 118140960795 + 399875 * 2 ^ 59
def prefixEnd_399875 : Nat := 4983230072969 + 3 ^ 40 * 399875 * 2
def baseEnd_399875 : Nat := 91256922985212542632673

theorem tailTrace_399875 : CollatzResearch.WordTrace tailWord_399875 prefixEnd_399875 91256922985212542632673 := by
  unfold tailWord_399875
  simp only [CollatzResearch.WordTrace]
  refine ⟨14584639426328643058009079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9723092950885762038672719 14584639426328643058009079)
  ·
    refine ⟨21876959139492964587013619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14584639426328643058009079 21876959139492964587013619)
    ·
      refine ⟨32815438709239446880520429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21876959139492964587013619 32815438709239446880520429)
      ·
        refine ⟨12305789515964792580195161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32815438709239446880520429 12305789515964792580195161)
        ·
          refine ⟨9229342136973594435146371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12305789515964792580195161 9229342136973594435146371)
          ·
            refine ⟨13844013205460391652719557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9229342136973594435146371 13844013205460391652719557)
            ·
              refine ⟨2595752476023823434884917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13844013205460391652719557 2595752476023823434884917)
              ·
                refine ⟨243351794627233447020461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2595752476023823434884917 243351794627233447020461)
                ·
                  refine ⟨91256922985212542632673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243351794627233447020461 91256922985212542632673)
                  ·
                    rfl

theorem cell21_399875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 3].length) (baseStart_399875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399875 prefixEnd_399875 := by exact prefixLift 399875
  have htrace : WordTrace (prefixWord ++ tailWord_399875) baseStart_399875 baseEnd_399875 := by
    simpa [prefixWord, tailWord_399875, baseEnd_399875] using wordTrace_append hprefix tailTrace_399875
  have hstable : (prefixWord ++ tailWord_399875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399875).length < 2 ^ (prefixWord ++ tailWord_399875).sum := by decide
  have hdescent : baseEnd_399875 < baseStart_399875 := by decide
  rcases family_descends (prefixWord ++ tailWord_399875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399878 : List Nat := [6, 2, 1, 1, 1, 10]
def baseStart_399878 : Nat := 118140960795 + 399878 * 2 ^ 59
def prefixEnd_399878 : Nat := 4983230072969 + 3 ^ 40 * 399878 * 2
def baseEnd_399878 : Nat := 3379911393558711262321

theorem tailTrace_399878 : CollatzResearch.WordTrace tailWord_399878 prefixEnd_399878 3379911393558711262321 := by
  unfold tailWord_399878
  simp only [CollatzResearch.WordTrace]
  refine ⟨455773401416180455324009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9723165896878516380245525 455773401416180455324009)
  ·
    refine ⟨341830051062135341493007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 455773401416180455324009 341830051062135341493007)
    ·
      refine ⟨512745076593203012239511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341830051062135341493007 512745076593203012239511)
      ·
        refine ⟨769117614889804518359267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512745076593203012239511 769117614889804518359267)
        ·
          refine ⟨1153676422334706777538901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769117614889804518359267 1153676422334706777538901)
          ·
            refine ⟨3379911393558711262321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1153676422334706777538901 3379911393558711262321)
            ·
              rfl

theorem cell21_399878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 10].length) (baseStart_399878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399878 prefixEnd_399878 := by exact prefixLift 399878
  have htrace : WordTrace (prefixWord ++ tailWord_399878) baseStart_399878 baseEnd_399878 := by
    simpa [prefixWord, tailWord_399878, baseEnd_399878] using wordTrace_append hprefix tailTrace_399878
  have hstable : (prefixWord ++ tailWord_399878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399878).length < 2 ^ (prefixWord ++ tailWord_399878).sum := by decide
  have hdescent : baseEnd_399878 < baseStart_399878 := by decide
  rcases family_descends (prefixWord ++ tailWord_399878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399940 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 6]
def baseStart_399940 : Nat := 118140960795 + 399940 * 2 ^ 59
def prefixEnd_399940 : Nat := 4983230072969 + 3 ^ 40 * 399940 * 2
def baseEnd_399940 : Nat := 91271756870786874049207

theorem tailTrace_399940 : CollatzResearch.WordTrace tailWord_399940 prefixEnd_399940 91271756870786874049207 := by
  unfold tailWord_399940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7293505085546579579562637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9724673447395439439416849 7293505085546579579562637)
  ·
    refine ⟨2735064407079967342335989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7293505085546579579562637 2735064407079967342335989)
    ·
      refine ⟨256412288163746938343999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2735064407079967342335989 256412288163746938343999)
      ·
        refine ⟨384618432245620407515999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256412288163746938343999 384618432245620407515999)
        ·
          refine ⟨576927648368430611273999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384618432245620407515999 576927648368430611273999)
          ·
            refine ⟨865391472552645916910999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576927648368430611273999 865391472552645916910999)
            ·
              refine ⟨1298087208828968875366499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865391472552645916910999 1298087208828968875366499)
              ·
                refine ⟨1947130813243453313049749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298087208828968875366499 1947130813243453313049749)
                ·
                  refine ⟨91271756870786874049207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1947130813243453313049749 91271756870786874049207)
                  ·
                    rfl

theorem cell21_399940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_399940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399940 prefixEnd_399940 := by exact prefixLift 399940
  have htrace : WordTrace (prefixWord ++ tailWord_399940) baseStart_399940 baseEnd_399940 := by
    simpa [prefixWord, tailWord_399940, baseEnd_399940] using wordTrace_append hprefix tailTrace_399940
  have hstable : (prefixWord ++ tailWord_399940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399940).length < 2 ^ (prefixWord ++ tailWord_399940).sum := by decide
  have hdescent : baseEnd_399940 < baseStart_399940 := by decide
  rcases family_descends (prefixWord ++ tailWord_399940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399951 : List Nat := [1, 1, 2, 1, 1, 2, 6, 4, 3]
def baseStart_399951 : Nat := 118140960795 + 399951 * 2 ^ 59
def prefixEnd_399951 : Nat := 4983230072969 + 3 ^ 40 * 399951 * 2
def baseEnd_399951 : Nat := 91274267220653299365851

theorem tailTrace_399951 : CollatzResearch.WordTrace tailWord_399951 prefixEnd_399951 91274267220653299365851 := by
  unfold tailWord_399951
  simp only [CollatzResearch.WordTrace]
  refine ⟨14587411374053308037775707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9724940916035538691850471 14587411374053308037775707)
  ·
    refine ⟨21881117061079962056663561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14587411374053308037775707 21881117061079962056663561)
    ·
      refine ⟨16410837795809971542497671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21881117061079962056663561 16410837795809971542497671)
      ·
        refine ⟨24616256693714957313746507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16410837795809971542497671 24616256693714957313746507)
        ·
          refine ⟨36924385040572435970619761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24616256693714957313746507 36924385040572435970619761)
          ·
            refine ⟨27693288780429326977964821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36924385040572435970619761 27693288780429326977964821)
            ·
              refine ⟨1298122911582624702092101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27693288780429326977964821 1298122911582624702092101)
              ·
                refine ⟨243398045921742131642269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1298122911582624702092101 243398045921742131642269)
                ·
                  refine ⟨91274267220653299365851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243398045921742131642269 91274267220653299365851)
                  ·
                    rfl

theorem cell21_399951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 3].length) (baseStart_399951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_399951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_399951 prefixEnd_399951 := by exact prefixLift 399951
  have htrace : WordTrace (prefixWord ++ tailWord_399951) baseStart_399951 baseEnd_399951 := by
    simpa [prefixWord, tailWord_399951, baseEnd_399951] using wordTrace_append hprefix tailTrace_399951
  have hstable : (prefixWord ++ tailWord_399951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399951).length < 2 ^ (prefixWord ++ tailWord_399951).sum := by decide
  have hdescent : baseEnd_399951 < baseStart_399951 := by decide
  rcases family_descends (prefixWord ++ tailWord_399951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400055 : List Nat := [1, 1, 3, 1, 6, 9]
def baseStart_400055 : Nat := 118140960795 + 400055 * 2 ^ 59
def prefixEnd_400055 : Nat := 4983230072969 + 3 ^ 40 * 400055 * 2
def baseEnd_400055 : Nat := 3381407460650823319715

theorem tailTrace_400055 : CollatzResearch.WordTrace tailWord_400055 prefixEnd_400055 3381407460650823319715 := by
  unfold tailWord_400055
  simp only [CollatzResearch.WordTrace]
  refine ⟨14591204565676533799561619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9727469710451022533041079 14591204565676533799561619)
  ·
    refine ⟨21886806848514800699342429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14591204565676533799561619 21886806848514800699342429)
    ·
      refine ⟨8207552568193050262253411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21886806848514800699342429 8207552568193050262253411)
      ·
        refine ⟨12311328852289575393380117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8207552568193050262253411 12311328852289575393380117)
        ·
          refine ⟨577093539951073846564693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12311328852289575393380117 577093539951073846564693)
          ·
            refine ⟨3381407460650823319715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 577093539951073846564693 3381407460650823319715)
            ·
              rfl

theorem cell21_400055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 9].length) (baseStart_400055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400055 prefixEnd_400055 := by exact prefixLift 400055
  have htrace : WordTrace (prefixWord ++ tailWord_400055) baseStart_400055 baseEnd_400055 := by
    simpa [prefixWord, tailWord_400055, baseEnd_400055] using wordTrace_append hprefix tailTrace_400055
  have hstable : (prefixWord ++ tailWord_400055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400055).length < 2 ^ (prefixWord ++ tailWord_400055).sum := by decide
  have hdescent : baseEnd_400055 < baseStart_400055 := by decide
  rcases family_descends (prefixWord ++ tailWord_400055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400061 : List Nat := [1, 4, 1, 2, 1, 5, 2, 2, 3]
def baseStart_400061 : Nat := 118140960795 + 400061 * 2 ^ 59
def prefixEnd_400061 : Nat := 4983230072969 + 3 ^ 40 * 400061 * 2
def baseEnd_400061 : Nat := 91299370719317552532293

theorem tailTrace_400061 : CollatzResearch.WordTrace tailWord_400061 prefixEnd_400061 91299370719317552532293 := by
  unfold tailWord_400061
  simp only [CollatzResearch.WordTrace]
  refine ⟨14591423403654796824280037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9727615602436531216186691 14591423403654796824280037)
  ·
    refine ⟨2735891888185274404552507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14591423403654796824280037 2735891888185274404552507)
    ·
      refine ⟨4103837832277911606828761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2735891888185274404552507 4103837832277911606828761)
      ·
        refine ⟨3077878374208433705121571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4103837832277911606828761 3077878374208433705121571)
        ·
          refine ⟨4616817561312650557682357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3077878374208433705121571 4616817561312650557682357)
          ·
            refine ⟨432826646373060989782721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4616817561312650557682357 432826646373060989782721)
            ·
              refine ⟨324619984779795742337041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432826646373060989782721 324619984779795742337041)
              ·
                refine ⟨243464988584846806752781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324619984779795742337041 243464988584846806752781)
                ·
                  refine ⟨91299370719317552532293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243464988584846806752781 91299370719317552532293)
                  ·
                    rfl

theorem cell21_400061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_400061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400061 prefixEnd_400061 := by exact prefixLift 400061
  have htrace : WordTrace (prefixWord ++ tailWord_400061) baseStart_400061 baseEnd_400061 := by
    simpa [prefixWord, tailWord_400061, baseEnd_400061] using wordTrace_append hprefix tailTrace_400061
  have hstable : (prefixWord ++ tailWord_400061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400061).length < 2 ^ (prefixWord ++ tailWord_400061).sum := by decide
  have hdescent : baseEnd_400061 < baseStart_400061 := by decide
  rcases family_descends (prefixWord ++ tailWord_400061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400072 : List Nat := [2, 1, 3, 1, 2, 5, 1, 6]
def baseStart_400072 : Nat := 118140960795 + 400072 * 2 ^ 59
def prefixEnd_400072 : Nat := 4983230072969 + 3 ^ 40 * 400072 * 2
def baseEnd_400072 : Nat := 30433960356394659282979

theorem tailTrace_400072 : CollatzResearch.WordTrace tailWord_400072 prefixEnd_400072 30433960356394659282979 := by
  unfold tailWord_400072
  simp only [CollatzResearch.WordTrace]
  refine ⟨7295912303307472851465235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9727883071076630468620313 7295912303307472851465235)
  ·
    refine ⟨10943868454961209277197853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7295912303307472851465235 10943868454961209277197853)
    ·
      refine ⟨4103950670610453478949195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10943868454961209277197853 4103950670610453478949195)
      ·
        refine ⟨6155926005915680218423793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4103950670610453478949195 6155926005915680218423793)
        ·
          refine ⟨4616944504436760163817845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6155926005915680218423793 4616944504436760163817845)
          ·
            refine ⟨432838547290946265357923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4616944504436760163817845 432838547290946265357923)
            ·
              refine ⟨649257820936419398036885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432838547290946265357923 649257820936419398036885)
              ·
                refine ⟨30433960356394659282979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 649257820936419398036885 30433960356394659282979)
                ·
                  rfl

theorem cell21_400072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_400072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400072 prefixEnd_400072 := by exact prefixLift 400072
  have htrace : WordTrace (prefixWord ++ tailWord_400072) baseStart_400072 baseEnd_400072 := by
    simpa [prefixWord, tailWord_400072, baseEnd_400072] using wordTrace_append hprefix tailTrace_400072
  have hstable : (prefixWord ++ tailWord_400072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400072).length < 2 ^ (prefixWord ++ tailWord_400072).sum := by decide
  have hdescent : baseEnd_400072 < baseStart_400072 := by decide
  rcases family_descends (prefixWord ++ tailWord_400072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400179 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 5]
def baseStart_400179 : Nat := 118140960795 + 400179 * 2 ^ 59
def prefixEnd_400179 : Nat := 4983230072969 + 3 ^ 40 * 400179 * 2
def baseEnd_400179 : Nat := 91326299926975569565385

theorem tailTrace_400179 : CollatzResearch.WordTrace tailWord_400179 prefixEnd_400179 91326299926975569565385 := by
  unfold tailWord_400179
  simp only [CollatzResearch.WordTrace]
  refine ⟨14595727217227302977075591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9730484811484868651383727 14595727217227302977075591)
  ·
    refine ⟨21893590825840954465613387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14595727217227302977075591 21893590825840954465613387)
    ·
      refine ⟨32840386238761431698420081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21893590825840954465613387 32840386238761431698420081)
      ·
        refine ⟨24630289679071073773815061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32840386238761431698420081 24630289679071073773815061)
        ·
          refine ⟨1154544828706456583147581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24630289679071073773815061 1154544828706456583147581)
          ·
            refine ⟨432954310764921218680343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1154544828706456583147581 432954310764921218680343)
            ·
              refine ⟨649431466147381828020515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432954310764921218680343 649431466147381828020515)
              ·
                refine ⟨974147199221072742030773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649431466147381828020515 974147199221072742030773)
                ·
                  refine ⟨91326299926975569565385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 974147199221072742030773 91326299926975569565385)
                  ·
                    rfl

theorem cell21_400179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 5].length) (baseStart_400179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400179 prefixEnd_400179 := by exact prefixLift 400179
  have htrace : WordTrace (prefixWord ++ tailWord_400179) baseStart_400179 baseEnd_400179 := by
    simpa [prefixWord, tailWord_400179, baseEnd_400179] using wordTrace_append hprefix tailTrace_400179
  have hstable : (prefixWord ++ tailWord_400179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400179).length < 2 ^ (prefixWord ++ tailWord_400179).sum := by decide
  have hdescent : baseEnd_400179 < baseStart_400179 := by decide
  rcases family_descends (prefixWord ++ tailWord_400179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400317 : List Nat := [1, 4, 1, 2, 4, 2, 2, 5]
def baseStart_400317 : Nat := 118140960795 + 400317 * 2 ^ 59
def prefixEnd_400317 : Nat := 4983230072969 + 3 ^ 40 * 400317 * 2
def baseEnd_400317 : Nat := 30452597802372665421701

theorem tailTrace_400317 : CollatzResearch.WordTrace tailWord_400317 prefixEnd_400317 30452597802372665421701 := by
  unfold tailWord_400317
  simp only [CollatzResearch.WordTrace]
  refine ⟨14600760490727352545599205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9733840327151568363732803 14600760490727352545599205)
  ·
    refine ⟨2737642592011378602299851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14600760490727352545599205 2737642592011378602299851)
    ·
      refine ⟨4106463888017067903449777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2737642592011378602299851 4106463888017067903449777)
      ·
        refine ⟨3079847916012800927587333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4106463888017067903449777 3079847916012800927587333)
        ·
          refine ⟨577471484252400173922625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3079847916012800927587333 577471484252400173922625)
          ·
            refine ⟨433103613189300130441969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577471484252400173922625 433103613189300130441969)
            ·
              refine ⟨324827709891975097831477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433103613189300130441969 324827709891975097831477)
              ·
                refine ⟨30452597802372665421701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 324827709891975097831477 30452597802372665421701)
                ·
                  rfl

theorem cell21_400317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 5].length) (baseStart_400317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400317 prefixEnd_400317 := by exact prefixLift 400317
  have htrace : WordTrace (prefixWord ++ tailWord_400317) baseStart_400317 baseEnd_400317 := by
    simpa [prefixWord, tailWord_400317, baseEnd_400317] using wordTrace_append hprefix tailTrace_400317
  have hstable : (prefixWord ++ tailWord_400317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400317).length < 2 ^ (prefixWord ++ tailWord_400317).sum := by decide
  have hdescent : baseEnd_400317 < baseStart_400317 := by decide
  rcases family_descends (prefixWord ++ tailWord_400317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400331 : List Nat := [1, 1, 1, 1, 3, 5, 3, 3, 3]
def baseStart_400331 : Nat := 118140960795 + 400331 * 2 ^ 59
def prefixEnd_400331 : Nat := 4983230072969 + 3 ^ 40 * 400331 * 2
def baseEnd_400331 : Nat := 91360988397857083031741

theorem tailTrace_400331 : CollatzResearch.WordTrace tailWord_400331 prefixEnd_400331 91360988397857083031741 := by
  unfold tailWord_400331
  simp only [CollatzResearch.WordTrace]
  refine ⟨14601271112676632936608847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9734180741784421957739231 14601271112676632936608847)
  ·
    refine ⟨21901906669014949404913271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14601271112676632936608847 21901906669014949404913271)
    ·
      refine ⟨32852860003522424107369907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21901906669014949404913271 32852860003522424107369907)
      ·
        refine ⟨49279290005283636161054861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32852860003522424107369907 49279290005283636161054861)
        ·
          refine ⟨18479733751981363560395573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49279290005283636161054861 18479733751981363560395573)
          ·
            refine ⟨1732475039248252833787085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18479733751981363560395573 1732475039248252833787085)
            ·
              refine ⟨649678139718094812670157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1732475039248252833787085 649678139718094812670157)
              ·
                refine ⟨243629302394285554751309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 649678139718094812670157 243629302394285554751309)
                ·
                  refine ⟨91360988397857083031741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243629302394285554751309 91360988397857083031741)
                  ·
                    rfl

theorem cell21_400331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 3].length) (baseStart_400331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400331 prefixEnd_400331 := by exact prefixLift 400331
  have htrace : WordTrace (prefixWord ++ tailWord_400331) baseStart_400331 baseEnd_400331 := by
    simpa [prefixWord, tailWord_400331, baseEnd_400331] using wordTrace_append hprefix tailTrace_400331
  have hstable : (prefixWord ++ tailWord_400331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400331).length < 2 ^ (prefixWord ++ tailWord_400331).sum := by decide
  have hdescent : baseEnd_400331 < baseStart_400331 := by decide
  rcases family_descends (prefixWord ++ tailWord_400331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400359 : List Nat := [1, 1, 5, 2, 2, 1, 1, 8]
def baseStart_400359 : Nat := 118140960795 + 400359 * 2 ^ 59
def prefixEnd_400359 : Nat := 4983230072969 + 3 ^ 40 * 400359 * 2
def baseEnd_400359 : Nat := 30455792793111752188339

theorem tailTrace_400359 : CollatzResearch.WordTrace tailWord_400359 prefixEnd_400359 30455792793111752188339 := by
  unfold tailWord_400359
  simp only [CollatzResearch.WordTrace]
  refine ⟨14602292356575193718628131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9734861571050129145752087 14602292356575193718628131)
  ·
    refine ⟨21903438534862790577942197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14602292356575193718628131 21903438534862790577942197)
    ·
      refine ⟨2053447362643386616682081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21903438534862790577942197 2053447362643386616682081)
      ·
        refine ⟨1540085521982539962511561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2053447362643386616682081 1540085521982539962511561)
        ·
          refine ⟨1155064141486904971883671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1540085521982539962511561 1155064141486904971883671)
          ·
            refine ⟨1732596212230357457825507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155064141486904971883671 1732596212230357457825507)
            ·
              refine ⟨2598894318345536186738261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732596212230357457825507 2598894318345536186738261)
              ·
                refine ⟨30455792793111752188339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2598894318345536186738261 30455792793111752188339)
                ·
                  rfl

theorem cell21_400359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 8].length) (baseStart_400359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400359 prefixEnd_400359 := by exact prefixLift 400359
  have htrace : WordTrace (prefixWord ++ tailWord_400359) baseStart_400359 baseEnd_400359 := by
    simpa [prefixWord, tailWord_400359, baseEnd_400359] using wordTrace_append hprefix tailTrace_400359
  have hstable : (prefixWord ++ tailWord_400359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400359).length < 2 ^ (prefixWord ++ tailWord_400359).sum := by decide
  have hdescent : baseEnd_400359 < baseStart_400359 := by decide
  rcases family_descends (prefixWord ++ tailWord_400359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400362 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_400362 : Nat := 118140960795 + 400362 * 2 ^ 59
def prefixEnd_400362 : Nat := 4983230072969 + 3 ^ 40 * 400362 * 2
def baseEnd_400362 : Nat := 91368063020207918015011

theorem tailTrace_400362 : CollatzResearch.WordTrace tailWord_400362 prefixEnd_400362 91368063020207918015011 := by
  unfold tailWord_400362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650600443891081307746835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9734934517042883487324893 3650600443891081307746835)
  ·
    refine ⟨5475900665836621961620253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3650600443891081307746835 5475900665836621961620253)
    ·
      refine ⟨2053462749688733235607595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5475900665836621961620253 2053462749688733235607595)
      ·
        refine ⟨3080194124533099853411393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2053462749688733235607595 3080194124533099853411393)
        ·
          refine ⟨2310145593399824890058545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3080194124533099853411393 2310145593399824890058545)
          ·
            refine ⟨1732609195049868667543909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2310145593399824890058545 1732609195049868667543909)
            ·
              refine ⟨324864224071850375164483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1732609195049868667543909 324864224071850375164483)
              ·
                refine ⟨487296336107775562746725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324864224071850375164483 487296336107775562746725)
                ·
                  refine ⟨91368063020207918015011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 487296336107775562746725 91368063020207918015011)
                  ·
                    rfl

theorem cell21_400362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_400362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400362 prefixEnd_400362 := by exact prefixLift 400362
  have htrace : WordTrace (prefixWord ++ tailWord_400362) baseStart_400362 baseEnd_400362 := by
    simpa [prefixWord, tailWord_400362, baseEnd_400362] using wordTrace_append hprefix tailTrace_400362
  have hstable : (prefixWord ++ tailWord_400362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400362).length < 2 ^ (prefixWord ++ tailWord_400362).sum := by decide
  have hdescent : baseEnd_400362 < baseStart_400362 := by decide
  rcases family_descends (prefixWord ++ tailWord_400362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400466 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 5]
def baseStart_400466 : Nat := 118140960795 + 400466 * 2 ^ 59
def prefixEnd_400466 : Nat := 4983230072969 + 3 ^ 40 * 400466 * 2
def baseEnd_400466 : Nat := 91391797237126848281465

theorem tailTrace_400466 : CollatzResearch.WordTrace tailWord_400466 prefixEnd_400466 91391797237126848281465 := by
  unfold tailWord_400466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3651548741796887748193313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9737463311458367328515501 3651548741796887748193313)
  ·
    refine ⟨2738661556347665811144985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3651548741796887748193313 2738661556347665811144985)
    ·
      refine ⟨2053996167260749358358739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2738661556347665811144985 2053996167260749358358739)
      ·
        refine ⟨3080994250891124037538109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2053996167260749358358739 3080994250891124037538109)
        ·
          refine ⟨1155372844084171514076791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3080994250891124037538109 1155372844084171514076791)
          ·
            refine ⟨1733059266126257271115187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155372844084171514076791 1733059266126257271115187)
            ·
              refine ⟨2599588899189385906672781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733059266126257271115187 2599588899189385906672781)
              ·
                refine ⟨974845837196019715002293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2599588899189385906672781 974845837196019715002293)
                ·
                  refine ⟨91391797237126848281465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 974845837196019715002293 91391797237126848281465)
                  ·
                    rfl

theorem cell21_400466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_400466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400466 prefixEnd_400466 := by exact prefixLift 400466
  have htrace : WordTrace (prefixWord ++ tailWord_400466) baseStart_400466 baseEnd_400466 := by
    simpa [prefixWord, tailWord_400466, baseEnd_400466] using wordTrace_append hprefix tailTrace_400466
  have hstable : (prefixWord ++ tailWord_400466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400466).length < 2 ^ (prefixWord ++ tailWord_400466).sum := by decide
  have hdescent : baseEnd_400466 < baseStart_400466 := by decide
  rcases family_descends (prefixWord ++ tailWord_400466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400539 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 10]
def baseStart_400539 : Nat := 118140960795 + 400539 * 2 ^ 59
def prefixEnd_400539 : Nat := 4983230072969 + 3 ^ 40 * 400539 * 2
def baseEnd_400539 : Nat := 91408456831694943564649

theorem tailTrace_400539 : CollatzResearch.WordTrace tailWord_400539 prefixEnd_400539 91408456831694943564649 := by
  unfold tailWord_400539
  simp only [CollatzResearch.WordTrace]
  refine ⟨14608857495923084460180671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9739238330615389640120447 14608857495923084460180671)
  ·
    refine ⟨21913286243884626690271007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14608857495923084460180671 21913286243884626690271007)
    ·
      refine ⟨32869929365826940035406511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21913286243884626690271007 32869929365826940035406511)
      ·
        refine ⟨49304894048740410053109767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32869929365826940035406511 49304894048740410053109767)
        ·
          refine ⟨73957341073110615079664651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49304894048740410053109767 73957341073110615079664651)
          ·
            refine ⟨110936011609665922619496977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73957341073110615079664651 110936011609665922619496977)
            ·
              refine ⟨83202008707249441964622733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110936011609665922619496977 83202008707249441964622733)
              ·
                refine ⟨31200753265218540736733525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83202008707249441964622733 31200753265218540736733525)
                ·
                  refine ⟨91408456831694943564649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 31200753265218540736733525 91408456831694943564649)
                  ·
                    rfl

theorem cell21_400539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_400539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400539 prefixEnd_400539 := by exact prefixLift 400539
  have htrace : WordTrace (prefixWord ++ tailWord_400539) baseStart_400539 baseEnd_400539 := by
    simpa [prefixWord, tailWord_400539, baseEnd_400539] using wordTrace_append hprefix tailTrace_400539
  have hstable : (prefixWord ++ tailWord_400539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400539).length < 2 ^ (prefixWord ++ tailWord_400539).sum := by decide
  have hdescent : baseEnd_400539 < baseStart_400539 := by decide
  rcases family_descends (prefixWord ++ tailWord_400539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400649 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 4]
def baseStart_400649 : Nat := 118140960795 + 400649 * 2 ^ 59
def prefixEnd_400649 : Nat := 4983230072969 + 3 ^ 40 * 400649 * 2
def baseEnd_400649 : Nat := 91433560330359196731091

theorem tailTrace_400649 : CollatzResearch.WordTrace tailWord_400649 prefixEnd_400649 91433560330359196731091 := by
  unfold tailWord_400649
  simp only [CollatzResearch.WordTrace]
  refine ⟨14612869525524573246685001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9741913017016382164456667 14612869525524573246685001)
  ·
    refine ⟨10959652144143429935013751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14612869525524573246685001 10959652144143429935013751)
    ·
      refine ⟨16439478216215144902520627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10959652144143429935013751 16439478216215144902520627)
      ·
        refine ⟨24659217324322717353780941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16439478216215144902520627 24659217324322717353780941)
        ·
          refine ⟨9247206496621019007667853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24659217324322717353780941 9247206496621019007667853)
          ·
            refine ⟨3467702436232882127875445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9247206496621019007667853 3467702436232882127875445)
            ·
              refine ⟨325097103396832699488323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3467702436232882127875445 325097103396832699488323)
              ·
                refine ⟨487645655095249049232485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325097103396832699488323 487645655095249049232485)
                ·
                  refine ⟨91433560330359196731091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 487645655095249049232485 91433560330359196731091)
                  ·
                    rfl

theorem cell21_400649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_400649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400649 prefixEnd_400649 := by exact prefixLift 400649
  have htrace : WordTrace (prefixWord ++ tailWord_400649) baseStart_400649 baseEnd_400649 := by
    simpa [prefixWord, tailWord_400649, baseEnd_400649] using wordTrace_append hprefix tailTrace_400649
  have hstable : (prefixWord ++ tailWord_400649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400649).length < 2 ^ (prefixWord ++ tailWord_400649).sum := by decide
  have hdescent : baseEnd_400649 < baseStart_400649 := by decide
  rcases family_descends (prefixWord ++ tailWord_400649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400829 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 5]
def baseStart_400829 : Nat := 118140960795 + 400829 * 2 ^ 59
def prefixEnd_400829 : Nat := 4983230072969 + 3 ^ 40 * 400829 * 2
def baseEnd_400829 : Nat := 91474638782718883730723

theorem tailTrace_400829 : CollatzResearch.WordTrace tailWord_400829 prefixEnd_400829 91474638782718883730723 := by
  unfold tailWord_400829
  simp only [CollatzResearch.WordTrace]
  refine ⟨14619434664872463988237541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9746289776581642658825027 14619434664872463988237541)
  ·
    refine ⟨2741143999663586997794539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14619434664872463988237541 2741143999663586997794539)
    ·
      refine ⟨4111715999495380496691809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2741143999663586997794539 4111715999495380496691809)
      ·
        refine ⟨3083786999621535372518857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4111715999495380496691809 3083786999621535372518857)
        ·
          refine ⟨2312840249716151529389143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3083786999621535372518857 2312840249716151529389143)
          ·
            refine ⟨3469260374574227294083715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312840249716151529389143 3469260374574227294083715)
            ·
              refine ⟨5203890561861340941125573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3469260374574227294083715 5203890561861340941125573)
              ·
                refine ⟨975729480349001426461045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5203890561861340941125573 975729480349001426461045)
                ·
                  refine ⟨91474638782718883730723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 975729480349001426461045 91474638782718883730723)
                  ·
                    rfl

theorem cell21_400829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_400829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400829 prefixEnd_400829 := by exact prefixLift 400829
  have htrace : WordTrace (prefixWord ++ tailWord_400829) baseStart_400829 baseEnd_400829 := by
    simpa [prefixWord, tailWord_400829, baseEnd_400829] using wordTrace_append hprefix tailTrace_400829
  have hstable : (prefixWord ++ tailWord_400829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400829).length < 2 ^ (prefixWord ++ tailWord_400829).sum := by decide
  have hdescent : baseEnd_400829 < baseStart_400829 := by decide
  rcases family_descends (prefixWord ++ tailWord_400829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400843 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 6]
def baseStart_400843 : Nat := 118140960795 + 400843 * 2 ^ 59
def prefixEnd_400843 : Nat := 4983230072969 + 3 ^ 40 * 400843 * 2
def baseEnd_400843 : Nat := 91477833773457970497361

theorem tailTrace_400843 : CollatzResearch.WordTrace tailWord_400843 prefixEnd_400843 91477833773457970497361 := by
  unfold tailWord_400843
  simp only [CollatzResearch.WordTrace]
  refine ⟨14619945286821744379247183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9746630191214496252831455 14619945286821744379247183)
  ·
    refine ⟨21929917930232616568870775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14619945286821744379247183 21929917930232616568870775)
    ·
      refine ⟨32894876895348924853306163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21929917930232616568870775 32894876895348924853306163)
      ·
        refine ⟨49342315343023387279959245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32894876895348924853306163 49342315343023387279959245)
        ·
          refine ⟨18503368253633770229984717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49342315343023387279959245 18503368253633770229984717)
          ·
            refine ⟨6938763095112663836244269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18503368253633770229984717 6938763095112663836244269)
            ·
              refine ⟨2602036160667248938591601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6938763095112663836244269 2602036160667248938591601)
              ·
                refine ⟨1951527120500436703943701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2602036160667248938591601 1951527120500436703943701)
                ·
                  refine ⟨91477833773457970497361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1951527120500436703943701 91477833773457970497361)
                  ·
                    rfl

theorem cell21_400843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_400843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400843 prefixEnd_400843 := by exact prefixLift 400843
  have htrace : WordTrace (prefixWord ++ tailWord_400843) baseStart_400843 baseEnd_400843 := by
    simpa [prefixWord, tailWord_400843, baseEnd_400843] using wordTrace_append hprefix tailTrace_400843
  have hstable : (prefixWord ++ tailWord_400843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400843).length < 2 ^ (prefixWord ++ tailWord_400843).sum := by decide
  have hdescent : baseEnd_400843 < baseStart_400843 := by decide
  rcases family_descends (prefixWord ++ tailWord_400843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400863 : List Nat := [1, 1, 2, 3, 3, 1, 5, 2, 3]
def baseStart_400863 : Nat := 118140960795 + 400863 * 2 ^ 59
def prefixEnd_400863 : Nat := 4983230072969 + 3 ^ 40 * 400863 * 2
def baseEnd_400863 : Nat := 91482398045942380163987

theorem tailTrace_400863 : CollatzResearch.WordTrace tailWord_400863 prefixEnd_400863 91482398045942380163987 := by
  unfold tailWord_400863
  simp only [CollatzResearch.WordTrace]
  refine ⟨14620674746749287794975243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9747116497832858529983495 14620674746749287794975243)
  ·
    refine ⟨21931012120123931692462865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14620674746749287794975243 21931012120123931692462865)
    ·
      refine ⟨16448259090092948769347149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21931012120123931692462865 16448259090092948769347149)
      ·
        refine ⟨6168097158784855788505181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16448259090092948769347149 6168097158784855788505181)
        ·
          refine ⟨2313036434544320920689443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6168097158784855788505181 2313036434544320920689443)
          ·
            refine ⟨3469554651816481381034165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313036434544320920689443 3469554651816481381034165)
            ·
              refine ⟨325270748607795129471953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3469554651816481381034165 325270748607795129471953)
              ·
                refine ⟨243953061455846347103965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325270748607795129471953 243953061455846347103965)
                ·
                  refine ⟨91482398045942380163987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243953061455846347103965 91482398045942380163987)
                  ·
                    rfl

theorem cell21_400863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 3].length) (baseStart_400863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_400863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_400863 prefixEnd_400863 := by exact prefixLift 400863
  have htrace : WordTrace (prefixWord ++ tailWord_400863) baseStart_400863 baseEnd_400863 := by
    simpa [prefixWord, tailWord_400863, baseEnd_400863] using wordTrace_append hprefix tailTrace_400863
  have hstable : (prefixWord ++ tailWord_400863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400863).length < 2 ^ (prefixWord ++ tailWord_400863).sum := by decide
  have hdescent : baseEnd_400863 < baseStart_400863 := by decide
  rcases family_descends (prefixWord ++ tailWord_400863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401032 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 5]
def baseStart_401032 : Nat := 118140960795 + 401032 * 2 ^ 59
def prefixEnd_401032 : Nat := 4983230072969 + 3 ^ 40 * 401032 * 2
def baseEnd_401032 : Nat := 91520966148435641846975

theorem tailTrace_401032 : CollatzResearch.WordTrace tailWord_401032 prefixEnd_401032 91520966148435641846975 := by
  unfold tailWord_401032
  simp only [CollatzResearch.WordTrace]
  refine ⟨7313419341568514828938675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9751225788758019771918233 7313419341568514828938675)
  ·
    refine ⟨10970129012352772243408013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7313419341568514828938675 10970129012352772243408013)
    ·
      refine ⟨4113798379632289591278005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10970129012352772243408013 4113798379632289591278005)
      ·
        refine ⟨385668598090527149182313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4113798379632289591278005 385668598090527149182313)
        ·
          refine ⟨289251448567895361886735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385668598090527149182313 289251448567895361886735)
          ·
            refine ⟨433877172851843042830103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289251448567895361886735 433877172851843042830103)
            ·
              refine ⟨650815759277764564245155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433877172851843042830103 650815759277764564245155)
              ·
                refine ⟨976223638916646846367733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650815759277764564245155 976223638916646846367733)
                ·
                  refine ⟨91520966148435641846975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 976223638916646846367733 91520966148435641846975)
                  ·
                    rfl

theorem cell21_401032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 5].length) (baseStart_401032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401032 prefixEnd_401032 := by exact prefixLift 401032
  have htrace : WordTrace (prefixWord ++ tailWord_401032) baseStart_401032 baseEnd_401032 := by
    simpa [prefixWord, tailWord_401032, baseEnd_401032] using wordTrace_append hprefix tailTrace_401032
  have hstable : (prefixWord ++ tailWord_401032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401032).length < 2 ^ (prefixWord ++ tailWord_401032).sum := by decide
  have hdescent : baseEnd_401032 < baseStart_401032 := by decide
  rcases family_descends (prefixWord ++ tailWord_401032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401088 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 4]
def baseStart_401088 : Nat := 118140960795 + 401088 * 2 ^ 59
def prefixEnd_401088 : Nat := 4983230072969 + 3 ^ 40 * 401088 * 2
def baseEnd_401088 : Nat := 91533746111391988913527

theorem tailTrace_401088 : CollatzResearch.WordTrace tailWord_401088 prefixEnd_401088 91533746111391988913527 := by
  unfold tailWord_401088
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314440585467075610957959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9752587447289434147943945 7314440585467075610957959)
  ·
    refine ⟨10971660878200613416436939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7314440585467075610957959 10971660878200613416436939)
    ·
      refine ⟨16457491317300920124655409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10971660878200613416436939 16457491317300920124655409)
      ·
        refine ⟨12343118487975690093491557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16457491317300920124655409 12343118487975690093491557)
        ·
          refine ⟨2314334716495441892529667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12343118487975690093491557 2314334716495441892529667)
          ·
            refine ⟨3471502074743162838794501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314334716495441892529667 3471502074743162838794501)
            ·
              refine ⟨650906639014343032273969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3471502074743162838794501 650906639014343032273969)
              ·
                refine ⟨488179979260757274205477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650906639014343032273969 488179979260757274205477)
                ·
                  refine ⟨91533746111391988913527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488179979260757274205477 91533746111391988913527)
                  ·
                    rfl

theorem cell21_401088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_401088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401088 prefixEnd_401088 := by exact prefixLift 401088
  have htrace : WordTrace (prefixWord ++ tailWord_401088) baseStart_401088 baseEnd_401088 := by
    simpa [prefixWord, tailWord_401088, baseEnd_401088] using wordTrace_append hprefix tailTrace_401088
  have hstable : (prefixWord ++ tailWord_401088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401088).length < 2 ^ (prefixWord ++ tailWord_401088).sum := by decide
  have hdescent : baseEnd_401088 < baseStart_401088 := by decide
  rcases family_descends (prefixWord ++ tailWord_401088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401147 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 4]
def baseStart_401147 : Nat := 118140960795 + 401147 * 2 ^ 59
def prefixEnd_401147 : Nat := 4983230072969 + 3 ^ 40 * 401147 * 2
def baseEnd_401147 : Nat := 91547210715220997430073

theorem tailTrace_401147 : CollatzResearch.WordTrace tailWord_401147 prefixEnd_401147 91547210715220997430073 := by
  unfold tailWord_401147
  simp only [CollatzResearch.WordTrace]
  refine ⟨14631033077720404298313695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9754022051813602865542463 14631033077720404298313695)
  ·
    refine ⟨21946549616580606447470543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14631033077720404298313695 21946549616580606447470543)
    ·
      refine ⟨32919824424870909671205815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21946549616580606447470543 32919824424870909671205815)
      ·
        refine ⟨49379736637306364506808723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32919824424870909671205815 49379736637306364506808723)
        ·
          refine ⟨74069604955959546760213085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49379736637306364506808723 74069604955959546760213085)
          ·
            refine ⟨27776101858484830035079907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74069604955959546760213085 27776101858484830035079907)
            ·
              refine ⟨41664152787727245052619861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27776101858484830035079907 41664152787727245052619861)
              ·
                refine ⟨488251790481178652960389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 41664152787727245052619861 488251790481178652960389)
                ·
                  refine ⟨91547210715220997430073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488251790481178652960389 91547210715220997430073)
                  ·
                    rfl

theorem cell21_401147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 4].length) (baseStart_401147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401147 prefixEnd_401147 := by exact prefixLift 401147
  have htrace : WordTrace (prefixWord ++ tailWord_401147) baseStart_401147 baseEnd_401147 := by
    simpa [prefixWord, tailWord_401147, baseEnd_401147] using wordTrace_append hprefix tailTrace_401147
  have hstable : (prefixWord ++ tailWord_401147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401147).length < 2 ^ (prefixWord ++ tailWord_401147).sum := by decide
  have hdescent : baseEnd_401147 < baseStart_401147 := by decide
  rcases family_descends (prefixWord ++ tailWord_401147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401161 : List Nat := [1, 2, 1, 1, 3, 2, 1, 10]
def baseStart_401161 : Nat := 118140960795 + 401161 * 2 ^ 59
def prefixEnd_401161 : Nat := 4983230072969 + 3 ^ 40 * 401161 * 2
def baseEnd_401161 : Nat := 30516801901986694732237

theorem tailTrace_401161 : CollatzResearch.WordTrace tailWord_401161 prefixEnd_401161 30516801901986694732237 := by
  unfold tailWord_401161
  simp only [CollatzResearch.WordTrace]
  refine ⟨14631543699669684689323337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9754362466446456459548891 14631543699669684689323337)
  ·
    refine ⟨10973657774752263516992503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14631543699669684689323337 10973657774752263516992503)
    ·
      refine ⟨16460486662128395275488755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10973657774752263516992503 16460486662128395275488755)
      ·
        refine ⟨24690729993192592913233133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16460486662128395275488755 24690729993192592913233133)
        ·
          refine ⟨9259023747447222342462425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24690729993192592913233133 9259023747447222342462425)
          ·
            refine ⟨6944267810585416756846819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9259023747447222342462425 6944267810585416756846819)
            ·
              refine ⟨10416401715878125135270229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6944267810585416756846819 10416401715878125135270229)
              ·
                refine ⟨30516801901986694732237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10416401715878125135270229 30516801901986694732237)
                ·
                  rfl

theorem cell21_401161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 10].length) (baseStart_401161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401161 prefixEnd_401161 := by exact prefixLift 401161
  have htrace : WordTrace (prefixWord ++ tailWord_401161) baseStart_401161 baseEnd_401161 := by
    simpa [prefixWord, tailWord_401161, baseEnd_401161] using wordTrace_append hprefix tailTrace_401161
  have hstable : (prefixWord ++ tailWord_401161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401161).length < 2 ^ (prefixWord ++ tailWord_401161).sum := by decide
  have hdescent : baseEnd_401161 < baseStart_401161 := by decide
  rcases family_descends (prefixWord ++ tailWord_401161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401178 : List Nat := [3, 1, 1, 3, 2, 3, 1, 7]
def baseStart_401178 : Nat := 118140960795 + 401178 * 2 ^ 59
def prefixEnd_401178 : Nat := 4983230072969 + 3 ^ 40 * 401178 * 2
def baseEnd_401178 : Nat := 30518095112523944137781

theorem tailTrace_401178 : CollatzResearch.WordTrace tailWord_401178 prefixEnd_401178 30518095112523944137781 := by
  unfold tailWord_401178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3658040935152024148173047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9754775827072064395128125 3658040935152024148173047)
  ·
    refine ⟨5487061402728036222259571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3658040935152024148173047 5487061402728036222259571)
    ·
      refine ⟨8230592104092054333389357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5487061402728036222259571 8230592104092054333389357)
      ·
        refine ⟨3086472039034520375021009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8230592104092054333389357 3086472039034520375021009)
        ·
          refine ⟨2314854029275890281265757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3086472039034520375021009 2314854029275890281265757)
          ·
            refine ⟨868070260978458855474659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2314854029275890281265757 868070260978458855474659)
            ·
              refine ⟨1302105391467688283211989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868070260978458855474659 1302105391467688283211989)
              ·
                refine ⟨30518095112523944137781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1302105391467688283211989 30518095112523944137781)
                ·
                  rfl

theorem cell21_401178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_401178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401178 prefixEnd_401178 := by exact prefixLift 401178
  have htrace : WordTrace (prefixWord ++ tailWord_401178) baseStart_401178 baseEnd_401178 := by
    simpa [prefixWord, tailWord_401178, baseEnd_401178] using wordTrace_append hprefix tailTrace_401178
  have hstable : (prefixWord ++ tailWord_401178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401178).length < 2 ^ (prefixWord ++ tailWord_401178).sum := by decide
  have hdescent : baseEnd_401178 < baseStart_401178 := by decide
  rcases family_descends (prefixWord ++ tailWord_401178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401316 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 4]
def baseStart_401316 : Nat := 118140960795 + 401316 * 2 ^ 59
def prefixEnd_401316 : Nat := 4983230072969 + 3 ^ 40 * 401316 * 2
def baseEnd_401316 : Nat := 91585778817714259113061

theorem tailTrace_401316 : CollatzResearch.WordTrace tailWord_401316 prefixEnd_401316 91585778817714259113061 := by
  unfold tailWord_401316
  simp only [CollatzResearch.WordTrace]
  refine ⟨7318598507054073080607901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9758131342738764107477201 7318598507054073080607901)
  ·
    refine ⟨2744474440145277405227963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7318598507054073080607901 2744474440145277405227963)
    ·
      refine ⟨4116711660217916107841945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744474440145277405227963 4116711660217916107841945)
      ·
        refine ⟨3087533745163437080881459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4116711660217916107841945 3087533745163437080881459)
        ·
          refine ⟨4631300617745155621322189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3087533745163437080881459 4631300617745155621322189)
          ·
            refine ⟨1736737731654433357995821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4631300617745155621322189 1736737731654433357995821)
            ·
              refine ⟨651276649370412509248433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1736737731654433357995821 651276649370412509248433)
              ·
                refine ⟨488457487027809381936325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651276649370412509248433 488457487027809381936325)
                ·
                  refine ⟨91585778817714259113061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488457487027809381936325 91585778817714259113061)
                  ·
                    rfl

theorem cell21_401316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_401316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401316 prefixEnd_401316 := by exact prefixLift 401316
  have htrace : WordTrace (prefixWord ++ tailWord_401316) baseStart_401316 baseEnd_401316 := by
    simpa [prefixWord, tailWord_401316, baseEnd_401316] using wordTrace_append hprefix tailTrace_401316
  have hstable : (prefixWord ++ tailWord_401316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401316).length < 2 ^ (prefixWord ++ tailWord_401316).sum := by decide
  have hdescent : baseEnd_401316 < baseStart_401316 := by decide
  rcases family_descends (prefixWord ++ tailWord_401316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401333 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 4]
def baseStart_401333 : Nat := 118140960795 + 401333 * 2 ^ 59
def prefixEnd_401333 : Nat := 4983230072969 + 3 ^ 40 * 401333 * 2
def baseEnd_401333 : Nat := 91589658449326007329693

theorem tailTrace_401333 : CollatzResearch.WordTrace tailWord_401333 prefixEnd_401333 91589658449326007329693 := by
  unfold tailWord_401333
  simp only [CollatzResearch.WordTrace]
  refine ⟨14637817055046558064584653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9758544703364372043056435 14637817055046558064584653)
  ·
    refine ⟨5489181395642459274219245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14637817055046558064584653 5489181395642459274219245)
    ·
      refine ⟨2058443023365922227832217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5489181395642459274219245 2058443023365922227832217)
      ·
        refine ⟨1543832267524441670874163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2058443023365922227832217 1543832267524441670874163)
        ·
          refine ⟨2315748401286662506311245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543832267524441670874163 2315748401286662506311245)
          ·
            refine ⟨868405650482498439866717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2315748401286662506311245 868405650482498439866717)
            ·
              refine ⟨325652118930936914950019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 868405650482498439866717 325652118930936914950019)
              ·
                refine ⟨488478178396405372425029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325652118930936914950019 488478178396405372425029)
                ·
                  refine ⟨91589658449326007329693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488478178396405372425029 91589658449326007329693)
                  ·
                    rfl

theorem cell21_401333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_401333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401333 prefixEnd_401333 := by exact prefixLift 401333
  have htrace : WordTrace (prefixWord ++ tailWord_401333) baseStart_401333 baseEnd_401333 := by
    simpa [prefixWord, tailWord_401333, baseEnd_401333] using wordTrace_append hprefix tailTrace_401333
  have hstable : (prefixWord ++ tailWord_401333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401333).length < 2 ^ (prefixWord ++ tailWord_401333).sum := by decide
  have hdescent : baseEnd_401333 < baseStart_401333 := by decide
  rcases family_descends (prefixWord ++ tailWord_401333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401344 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_401344 : Nat := 118140960795 + 401344 * 2 ^ 59
def prefixEnd_401344 : Nat := 4983230072969 + 3 ^ 40 * 401344 * 2
def baseEnd_401344 : Nat := 91592168799192432646337

theorem tailTrace_401344 : CollatzResearch.WordTrace tailWord_401344 prefixEnd_401344 91592168799192432646337 := by
  unfold tailWord_401344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7319109129003353471617543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9758812172004471295490057 7319109129003353471617543)
  ·
    refine ⟨10978663693505030207426315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7319109129003353471617543 10978663693505030207426315)
    ·
      refine ⟨16467995540257545311139473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10978663693505030207426315 16467995540257545311139473)
      ·
        refine ⟨12350996655193158983354605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16467995540257545311139473 12350996655193158983354605)
        ·
          refine ⟨4631623745697434618757977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12350996655193158983354605 4631623745697434618757977)
          ·
            refine ⟨3473717809273075964068483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4631623745697434618757977 3473717809273075964068483)
            ·
              refine ⟨5210576713909613946102725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473717809273075964068483 5210576713909613946102725)
              ·
                refine ⟨976983133858052614894261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5210576713909613946102725 976983133858052614894261)
                ·
                  refine ⟨91592168799192432646337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 976983133858052614894261 91592168799192432646337)
                  ·
                    rfl

theorem cell21_401344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_401344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401344 prefixEnd_401344 := by exact prefixLift 401344
  have htrace : WordTrace (prefixWord ++ tailWord_401344) baseStart_401344 baseEnd_401344 := by
    simpa [prefixWord, tailWord_401344, baseEnd_401344] using wordTrace_append hprefix tailTrace_401344
  have hstable : (prefixWord ++ tailWord_401344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401344).length < 2 ^ (prefixWord ++ tailWord_401344).sum := by decide
  have hdescent : baseEnd_401344 < baseStart_401344 := by decide
  rcases family_descends (prefixWord ++ tailWord_401344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401361 : List Nat := [1, 2, 2, 1, 2, 1, 2, 7, 3]
def baseStart_401361 : Nat := 118140960795 + 401361 * 2 ^ 59
def prefixEnd_401361 : Nat := 4983230072969 + 3 ^ 40 * 401361 * 2
def baseEnd_401361 : Nat := 91596048430804180862969

theorem tailTrace_401361 : CollatzResearch.WordTrace tailWord_401361 prefixEnd_401361 91596048430804180862969 := by
  unfold tailWord_401361
  simp only [CollatzResearch.WordTrace]
  refine ⟨14638838298945118846603937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9759225532630079231069291 14638838298945118846603937)
  ·
    refine ⟨10979128724208839134952953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14638838298945118846603937 10979128724208839134952953)
    ·
      refine ⟨8234346543156629351214715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10979128724208839134952953 8234346543156629351214715)
      ·
        refine ⟨12351519814734944026822073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8234346543156629351214715 12351519814734944026822073)
        ·
          refine ⟨9263639861051208020116555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12351519814734944026822073 9263639861051208020116555)
          ·
            refine ⟨13895459791576812030174833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9263639861051208020116555 13895459791576812030174833)
            ·
              refine ⟨10421594843682609022631125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13895459791576812030174833 10421594843682609022631125)
              ·
                refine ⟨244256129148811148967917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10421594843682609022631125 244256129148811148967917)
                ·
                  refine ⟨91596048430804180862969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244256129148811148967917 91596048430804180862969)
                  ·
                    rfl

theorem cell21_401361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 3].length) (baseStart_401361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401361 prefixEnd_401361 := by exact prefixLift 401361
  have htrace : WordTrace (prefixWord ++ tailWord_401361) baseStart_401361 baseEnd_401361 := by
    simpa [prefixWord, tailWord_401361, baseEnd_401361] using wordTrace_append hprefix tailTrace_401361
  have hstable : (prefixWord ++ tailWord_401361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401361).length < 2 ^ (prefixWord ++ tailWord_401361).sum := by decide
  have hdescent : baseEnd_401361 < baseStart_401361 := by decide
  rcases family_descends (prefixWord ++ tailWord_401361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401375 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 6]
def baseStart_401375 : Nat := 118140960795 + 401375 * 2 ^ 59
def prefixEnd_401375 : Nat := 4983230072969 + 3 ^ 40 * 401375 * 2
def baseEnd_401375 : Nat := 91599243421543267629607

theorem tailTrace_401375 : CollatzResearch.WordTrace tailWord_401375 prefixEnd_401375 91599243421543267629607 := by
  unfold tailWord_401375
  simp only [CollatzResearch.WordTrace]
  refine ⟨14639348920894399237613579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9759565947262932825075719 14639348920894399237613579)
  ·
    refine ⟨21959023381341598856420369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14639348920894399237613579 21959023381341598856420369)
    ·
      refine ⟨16469267536006199142315277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21959023381341598856420369 16469267536006199142315277)
      ·
        refine ⟨6175975326002324678368229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16469267536006199142315277 6175975326002324678368229)
        ·
          refine ⟨1157995373625435877194043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6175975326002324678368229 1157995373625435877194043)
          ·
            refine ⟨1736993060438153815791065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157995373625435877194043 1736993060438153815791065)
            ·
              refine ⟨1302744795328615361843299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736993060438153815791065 1302744795328615361843299)
              ·
                refine ⟨1954117192992923042764949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302744795328615361843299 1954117192992923042764949)
                ·
                  refine ⟨91599243421543267629607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1954117192992923042764949 91599243421543267629607)
                  ·
                    rfl

theorem cell21_401375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_401375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401375 prefixEnd_401375 := by exact prefixLift 401375
  have htrace : WordTrace (prefixWord ++ tailWord_401375) baseStart_401375 baseEnd_401375 := by
    simpa [prefixWord, tailWord_401375, baseEnd_401375] using wordTrace_append hprefix tailTrace_401375
  have hstable : (prefixWord ++ tailWord_401375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401375).length < 2 ^ (prefixWord ++ tailWord_401375).sum := by decide
  have hdescent : baseEnd_401375 < baseStart_401375 := by decide
  rcases family_descends (prefixWord ++ tailWord_401375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401392 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 4]
def baseStart_401392 : Nat := 118140960795 + 401392 * 2 ^ 59
def prefixEnd_401392 : Nat := 4983230072969 + 3 ^ 40 * 401392 * 2
def baseEnd_401392 : Nat := 91603123053155015846239

theorem tailTrace_401392 : CollatzResearch.WordTrace tailWord_401392 prefixEnd_401392 91603123053155015846239 := by
  unfold tailWord_401392
  simp only [CollatzResearch.WordTrace]
  refine ⟨7319984480916405570491215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9759979307888540760654953 7319984480916405570491215)
  ·
    refine ⟨10979976721374608355736823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7319984480916405570491215 10979976721374608355736823)
    ·
      refine ⟨16469965082061912533605235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10979976721374608355736823 16469965082061912533605235)
      ·
        refine ⟨24704947623092868800407853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16469965082061912533605235 24704947623092868800407853)
        ·
          refine ⟨9264355358659825800152945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24704947623092868800407853 9264355358659825800152945)
          ·
            refine ⟨6948266518994869350114709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9264355358659825800152945 6948266518994869350114709)
            ·
              refine ⟨325699993077884500786627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6948266518994869350114709 325699993077884500786627)
              ·
                refine ⟨488549989616826751179941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325699993077884500786627 488549989616826751179941)
                ·
                  refine ⟨91603123053155015846239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488549989616826751179941 91603123053155015846239)
                  ·
                    rfl

theorem cell21_401392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_401392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401392 prefixEnd_401392 := by exact prefixLift 401392
  have htrace : WordTrace (prefixWord ++ tailWord_401392) baseStart_401392 baseEnd_401392 := by
    simpa [prefixWord, tailWord_401392, baseEnd_401392] using wordTrace_append hprefix tailTrace_401392
  have hstable : (prefixWord ++ tailWord_401392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401392).length < 2 ^ (prefixWord ++ tailWord_401392).sum := by decide
  have hdescent : baseEnd_401392 < baseStart_401392 := by decide
  rcases family_descends (prefixWord ++ tailWord_401392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401496 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_401496 : Nat := 118140960795 + 401496 * 2 ^ 59
def prefixEnd_401496 : Nat := 4983230072969 + 3 ^ 40 * 401496 * 2
def baseEnd_401496 : Nat := 91626857270073946112693

theorem tailTrace_401496 : CollatzResearch.WordTrace tailWord_401496 prefixEnd_401496 91626857270073946112693 := by
  unfold tailWord_401496
  simp only [CollatzResearch.WordTrace]
  refine ⟨7321881076728018451384171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9762508102304024601845561 7321881076728018451384171)
  ·
    refine ⟨10982821615092027677076257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7321881076728018451384171 10982821615092027677076257)
    ·
      refine ⟨8237116211319020757807193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10982821615092027677076257 8237116211319020757807193)
      ·
        refine ⟨6177837158489265568355395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8237116211319020757807193 6177837158489265568355395)
        ·
          refine ⟨9266755737733898352533093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6177837158489265568355395 9266755737733898352533093)
          ·
            refine ⟨1737516700825105941099955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9266755737733898352533093 1737516700825105941099955)
            ·
              refine ⟨2606275051237658911649933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737516700825105941099955 2606275051237658911649933)
              ·
                refine ⟨977353144214122091868725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2606275051237658911649933 977353144214122091868725)
                ·
                  refine ⟨91626857270073946112693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 977353144214122091868725 91626857270073946112693)
                  ·
                    rfl

theorem cell21_401496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_401496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401496 prefixEnd_401496 := by exact prefixLift 401496
  have htrace : WordTrace (prefixWord ++ tailWord_401496) baseStart_401496 baseEnd_401496 := by
    simpa [prefixWord, tailWord_401496, baseEnd_401496] using wordTrace_append hprefix tailTrace_401496
  have hstable : (prefixWord ++ tailWord_401496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401496).length < 2 ^ (prefixWord ++ tailWord_401496).sum := by decide
  have hdescent : baseEnd_401496 < baseStart_401496 := by decide
  rcases family_descends (prefixWord ++ tailWord_401496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401541 : List Nat := [1, 3, 1, 1, 5, 1, 9]
def baseStart_401541 : Nat := 118140960795 + 401541 * 2 ^ 59
def prefixEnd_401541 : Nat := 4983230072969 + 3 ^ 40 * 401541 * 2
def baseEnd_401541 : Nat := 10181902987018207540289

theorem tailTrace_401541 : CollatzResearch.WordTrace tailWord_401541 prefixEnd_401541 10181902987018207540289 := by
  unfold tailWord_401541
  simp only [CollatzResearch.WordTrace]
  refine ⟨14645403438293009588156477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9763602292195339725437651 14645403438293009588156477)
  ·
    refine ⟨5492026289359878595558679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14645403438293009588156477 5492026289359878595558679)
    ·
      refine ⟨8238039434039817893338019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5492026289359878595558679 8238039434039817893338019)
      ·
        refine ⟨12357059151059726840007029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8238039434039817893338019 12357059151059726840007029)
        ·
          refine ⟨1158474295411849391250659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12357059151059726840007029 1158474295411849391250659)
          ·
            refine ⟨1737711443117774086875989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158474295411849391250659 1737711443117774086875989)
            ·
              refine ⟨10181902987018207540289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1737711443117774086875989 10181902987018207540289)
              ·
                rfl

theorem cell21_401541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 9].length) (baseStart_401541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401541 prefixEnd_401541 := by exact prefixLift 401541
  have htrace : WordTrace (prefixWord ++ tailWord_401541) baseStart_401541 baseEnd_401541 := by
    simpa [prefixWord, tailWord_401541, baseEnd_401541] using wordTrace_append hprefix tailTrace_401541
  have hstable : (prefixWord ++ tailWord_401541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401541).length < 2 ^ (prefixWord ++ tailWord_401541).sum := by decide
  have hdescent : baseEnd_401541 < baseStart_401541 := by decide
  rcases family_descends (prefixWord ++ tailWord_401541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401617 : List Nat := [1, 2, 2, 1, 2, 2, 5, 6]
def baseStart_401617 : Nat := 118140960795 + 401617 * 2 ^ 59
def prefixEnd_401617 : Nat := 4983230072969 + 3 ^ 40 * 401617 * 2
def baseEnd_401617 : Nat := 30551490372868208198593

theorem tailTrace_401617 : CollatzResearch.WordTrace tailWord_401617 prefixEnd_401617 30551490372868208198593 := by
  unfold tailWord_401617
  simp only [CollatzResearch.WordTrace]
  refine ⟨14648175386017674567923105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9765450257345116378615403 14648175386017674567923105)
  ·
    refine ⟨10986131539513255925942329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14648175386017674567923105 10986131539513255925942329)
    ·
      refine ⟨8239598654634941944456747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10986131539513255925942329 8239598654634941944456747)
      ·
        refine ⟨12359397981952412916685121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8239598654634941944456747 12359397981952412916685121)
        ·
          refine ⟨9269548486464309687513841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12359397981952412916685121 9269548486464309687513841)
          ·
            refine ⟨6952161364848232265635381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9269548486464309687513841 6952161364848232265635381)
            ·
              refine ⟨651765127954521774903317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6952161364848232265635381 651765127954521774903317)
              ·
                refine ⟨30551490372868208198593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 651765127954521774903317 30551490372868208198593)
                ·
                  rfl

theorem cell21_401617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 6].length) (baseStart_401617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401617 prefixEnd_401617 := by exact prefixLift 401617
  have htrace : WordTrace (prefixWord ++ tailWord_401617) baseStart_401617 baseEnd_401617 := by
    simpa [prefixWord, tailWord_401617, baseEnd_401617] using wordTrace_append hprefix tailTrace_401617
  have hstable : (prefixWord ++ tailWord_401617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401617).length < 2 ^ (prefixWord ++ tailWord_401617).sum := by decide
  have hdescent : baseEnd_401617 < baseStart_401617 := by decide
  rcases family_descends (prefixWord ++ tailWord_401617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401665 : List Nat := [1, 2, 4, 1, 1, 2, 1, 6, 3]
def baseStart_401665 : Nat := 118140960795 + 401665 * 2 ^ 59
def prefixEnd_401665 : Nat := 4983230072969 + 3 ^ 40 * 401665 * 2
def baseEnd_401665 : Nat := 91665425372567207795681

theorem tailTrace_401665 : CollatzResearch.WordTrace tailWord_401665 prefixEnd_401665 91665425372567207795681 := by
  unfold tailWord_401665
  simp only [CollatzResearch.WordTrace]
  refine ⟨14649926089843778765670449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9766617393229185843780299 14649926089843778765670449)
  ·
    refine ⟨10987444567382834074252837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14649926089843778765670449 10987444567382834074252837)
    ·
      refine ⟨2060145856384281388922407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10987444567382834074252837 2060145856384281388922407)
      ·
        refine ⟨3090218784576422083383611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060145856384281388922407 3090218784576422083383611)
        ·
          refine ⟨4635328176864633125075417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090218784576422083383611 4635328176864633125075417)
          ·
            refine ⟨3476496132648474843806563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4635328176864633125075417 3476496132648474843806563)
            ·
              refine ⟨5214744198972712265709845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3476496132648474843806563 5214744198972712265709845)
              ·
                refine ⟨244441134326845887455149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5214744198972712265709845 244441134326845887455149)
                ·
                  refine ⟨91665425372567207795681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244441134326845887455149 91665425372567207795681)
                  ·
                    rfl

theorem cell21_401665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 3].length) (baseStart_401665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401665 prefixEnd_401665 := by exact prefixLift 401665
  have htrace : WordTrace (prefixWord ++ tailWord_401665) baseStart_401665 baseEnd_401665 := by
    simpa [prefixWord, tailWord_401665, baseEnd_401665] using wordTrace_append hprefix tailTrace_401665
  have hstable : (prefixWord ++ tailWord_401665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401665).length < 2 ^ (prefixWord ++ tailWord_401665).sum := by decide
  have hdescent : baseEnd_401665 < baseStart_401665 := by decide
  rcases family_descends (prefixWord ++ tailWord_401665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401772 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 4]
def baseStart_401772 : Nat := 118140960795 + 401772 * 2 ^ 59
def prefixEnd_401772 : Nat := 4983230072969 + 3 ^ 40 * 401772 * 2
def baseEnd_401772 : Nat := 91689844230358799512129

theorem tailTrace_401772 : CollatzResearch.WordTrace tailWord_401772 prefixEnd_401772 91689844230358799512129 := by
  unfold tailWord_401772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7326914350228068019907785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9769219133637424026543713 7326914350228068019907785)
  ·
    refine ⟨5495185762671051014930839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7326914350228068019907785 5495185762671051014930839)
    ·
      refine ⟨8242778644006576522396259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5495185762671051014930839 8242778644006576522396259)
      ·
        refine ⟨12364167966009864783594389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8242778644006576522396259 12364167966009864783594389)
        ·
          refine ⟨579570373406712411730987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12364167966009864783594389 579570373406712411730987)
          ·
            refine ⟨869355560110068617596481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579570373406712411730987 869355560110068617596481)
            ·
              refine ⟨652016670082551463197361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 869355560110068617596481 652016670082551463197361)
              ·
                refine ⟨489012502561913597398021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652016670082551463197361 489012502561913597398021)
                ·
                  refine ⟨91689844230358799512129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 489012502561913597398021 91689844230358799512129)
                  ·
                    rfl

theorem cell21_401772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_401772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401772 prefixEnd_401772 := by exact prefixLift 401772
  have htrace : WordTrace (prefixWord ++ tailWord_401772) baseStart_401772 baseEnd_401772 := by
    simpa [prefixWord, tailWord_401772, baseEnd_401772] using wordTrace_append hprefix tailTrace_401772
  have hstable : (prefixWord ++ tailWord_401772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401772).length < 2 ^ (prefixWord ++ tailWord_401772).sum := by decide
  have hdescent : baseEnd_401772 < baseStart_401772 := by decide
  rcases family_descends (prefixWord ++ tailWord_401772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401800 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_401800 : Nat := 118140960795 + 401800 * 2 ^ 59
def prefixEnd_401800 : Nat := 4983230072969 + 3 ^ 40 * 401800 * 2
def baseEnd_401800 : Nat := 91696234211836973045405

theorem tailTrace_401800 : CollatzResearch.WordTrace tailWord_401800 prefixEnd_401800 91696234211836973045405 := by
  unfold tailWord_401800
  simp only [CollatzResearch.WordTrace]
  refine ⟨7327424972177348410917427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9769899962903131214556569 7327424972177348410917427)
  ·
    refine ⟨10991137458266022616376141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7327424972177348410917427 10991137458266022616376141)
    ·
      refine ⟨4121676546849758481141053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10991137458266022616376141 4121676546849758481141053)
      ·
        refine ⟨1545628705068659430427895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4121676546849758481141053 1545628705068659430427895)
        ·
          refine ⟨2318443057602989145641843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545628705068659430427895 2318443057602989145641843)
          ·
            refine ⟨3477664586404483718462765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318443057602989145641843 3477664586404483718462765)
            ·
              refine ⟨1304124219901681394423537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3477664586404483718462765 1304124219901681394423537)
              ·
                refine ⟨978093164926261045817653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304124219901681394423537 978093164926261045817653)
                ·
                  refine ⟨91696234211836973045405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 978093164926261045817653 91696234211836973045405)
                  ·
                    rfl

theorem cell21_401800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_401800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401800 prefixEnd_401800 := by exact prefixLift 401800
  have htrace : WordTrace (prefixWord ++ tailWord_401800) baseStart_401800 baseEnd_401800 := by
    simpa [prefixWord, tailWord_401800, baseEnd_401800] using wordTrace_append hprefix tailTrace_401800
  have hstable : (prefixWord ++ tailWord_401800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401800).length < 2 ^ (prefixWord ++ tailWord_401800).sum := by decide
  have hdescent : baseEnd_401800 < baseStart_401800 := by decide
  rcases family_descends (prefixWord ++ tailWord_401800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401817 : List Nat := [1, 2, 1, 2, 1, 4, 4, 3, 3]
def baseStart_401817 : Nat := 118140960795 + 401817 * 2 ^ 59
def prefixEnd_401817 : Nat := 4983230072969 + 3 ^ 40 * 401817 * 2
def baseEnd_401817 : Nat := 91700113843448721262037

theorem tailTrace_401817 : CollatzResearch.WordTrace tailWord_401817 prefixEnd_401817 91700113843448721262037 := by
  unfold tailWord_401817
  simp only [CollatzResearch.WordTrace]
  refine ⟨14655469985293108725203705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9770313323528739150135803 14655469985293108725203705)
  ·
    refine ⟨10991602488969831543902779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14655469985293108725203705 10991602488969831543902779)
    ·
      refine ⟨16487403733454747315854169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10991602488969831543902779 16487403733454747315854169)
      ·
        refine ⟨12365552800091060486890627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16487403733454747315854169 12365552800091060486890627)
        ·
          refine ⟨18548329200136590730335941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12365552800091060486890627 18548329200136590730335941)
          ·
            refine ⟨3477811725025610761937989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18548329200136590730335941 3477811725025610761937989)
            ·
              refine ⟨652089698442302017863373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3477811725025610761937989 652089698442302017863373)
              ·
                refine ⟨244533636915863256698765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 652089698442302017863373 244533636915863256698765)
                ·
                  refine ⟨91700113843448721262037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244533636915863256698765 91700113843448721262037)
                  ·
                    rfl

theorem cell21_401817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 3].length) (baseStart_401817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401817 prefixEnd_401817 := by exact prefixLift 401817
  have htrace : WordTrace (prefixWord ++ tailWord_401817) baseStart_401817 baseEnd_401817 := by
    simpa [prefixWord, tailWord_401817, baseEnd_401817] using wordTrace_append hprefix tailTrace_401817
  have hstable : (prefixWord ++ tailWord_401817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401817).length < 2 ^ (prefixWord ++ tailWord_401817).sum := by decide
  have hdescent : baseEnd_401817 < baseStart_401817 := by decide
  rcases family_descends (prefixWord ++ tailWord_401817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401831 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 6]
def baseStart_401831 : Nat := 118140960795 + 401831 * 2 ^ 59
def prefixEnd_401831 : Nat := 4983230072969 + 3 ^ 40 * 401831 * 2
def baseEnd_401831 : Nat := 91703308834187808028675

theorem tailTrace_401831 : CollatzResearch.WordTrace tailWord_401831 prefixEnd_401831 91703308834187808028675 := by
  unfold tailWord_401831
  simp only [CollatzResearch.WordTrace]
  refine ⟨14655980607242389116213347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9770653738161592744142231 14655980607242389116213347)
  ·
    refine ⟨21983970910863583674320021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14655980607242389116213347 21983970910863583674320021)
    ·
      refine ⟨1030498636446730484733751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21983970910863583674320021 1030498636446730484733751)
      ·
        refine ⟨1545747954670095727100627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030498636446730484733751 1545747954670095727100627)
        ·
          refine ⟨2318621932005143590650941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545747954670095727100627 2318621932005143590650941)
          ·
            refine ⟨869483224501928846494103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2318621932005143590650941 869483224501928846494103)
            ·
              refine ⟨1304224836752893269741155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869483224501928846494103 1304224836752893269741155)
              ·
                refine ⟨1956337255129339904611733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304224836752893269741155 1956337255129339904611733)
                ·
                  refine ⟨91703308834187808028675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1956337255129339904611733 91703308834187808028675)
                  ·
                    rfl

theorem cell21_401831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 6].length) (baseStart_401831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401831 prefixEnd_401831 := by exact prefixLift 401831
  have htrace : WordTrace (prefixWord ++ tailWord_401831) baseStart_401831 baseEnd_401831 := by
    simpa [prefixWord, tailWord_401831, baseEnd_401831] using wordTrace_append hprefix tailTrace_401831
  have hstable : (prefixWord ++ tailWord_401831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401831).length < 2 ^ (prefixWord ++ tailWord_401831).sum := by decide
  have hdescent : baseEnd_401831 < baseStart_401831 := by decide
  rcases family_descends (prefixWord ++ tailWord_401831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401921 : List Nat := [1, 2, 4, 1, 3, 1, 2, 7]
def baseStart_401921 : Nat := 118140960795 + 401921 * 2 ^ 59
def prefixEnd_401921 : Nat := 4983230072969 + 3 ^ 40 * 401921 * 2
def baseEnd_401921 : Nat := 30574616020122550509497

theorem tailTrace_401921 : CollatzResearch.WordTrace tailWord_401921 prefixEnd_401921 30574616020122550509497 := by
  unfold tailWord_401921
  simp only [CollatzResearch.WordTrace]
  refine ⟨14659263176916334486989617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9772842117944222991326411 14659263176916334486989617)
  ·
    refine ⟨10994447382687250865242213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14659263176916334486989617 10994447382687250865242213)
    ·
      refine ⟨2061458884253859537232915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10994447382687250865242213 2061458884253859537232915)
      ·
        refine ⟨3092188326380789305849373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2061458884253859537232915 3092188326380789305849373)
        ·
          refine ⟨1159570622392795989693515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3092188326380789305849373 1159570622392795989693515)
          ·
            refine ⟨1739355933589193984540273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159570622392795989693515 1739355933589193984540273)
            ·
              refine ⟨1304516950191895488405205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1739355933589193984540273 1304516950191895488405205)
              ·
                refine ⟨30574616020122550509497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1304516950191895488405205 30574616020122550509497)
                ·
                  rfl

theorem cell21_401921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 7].length) (baseStart_401921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401921 prefixEnd_401921 := by exact prefixLift 401921
  have htrace : WordTrace (prefixWord ++ tailWord_401921) baseStart_401921 baseEnd_401921 := by
    simpa [prefixWord, tailWord_401921, baseEnd_401921] using wordTrace_append hprefix tailTrace_401921
  have hstable : (prefixWord ++ tailWord_401921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401921).length < 2 ^ (prefixWord ++ tailWord_401921).sum := by decide
  have hdescent : baseEnd_401921 < baseStart_401921 := by decide
  rcases family_descends (prefixWord ++ tailWord_401921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401972 : List Nat := [2, 5, 1, 3, 1, 1, 3, 5]
def baseStart_401972 : Nat := 118140960795 + 401972 * 2 ^ 59
def prefixEnd_401972 : Nat := 4983230072969 + 3 ^ 40 * 401972 * 2
def baseEnd_401972 : Nat := 30578495651734298726129

theorem tailTrace_401972 : CollatzResearch.WordTrace tailWord_401972 prefixEnd_401972 30578495651734298726129 := by
  unfold tailWord_401972
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330561649865785098548085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9774082199821046798064113 7330561649865785098548085)
  ·
    refine ⟨687240154674917352988883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7330561649865785098548085 687240154674917352988883)
    ·
      refine ⟨1030860232012376029483325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687240154674917352988883 1030860232012376029483325)
      ·
        refine ⟨386572587004641011056247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1030860232012376029483325 386572587004641011056247)
        ·
          refine ⟨579858880506961516584371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386572587004641011056247 579858880506961516584371)
          ·
            refine ⟨869788320760442274876557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579858880506961516584371 869788320760442274876557)
            ·
              refine ⟨326170620285165853078709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 869788320760442274876557 326170620285165853078709)
              ·
                refine ⟨30578495651734298726129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 326170620285165853078709 30578495651734298726129)
                ·
                  rfl

theorem cell21_401972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_401972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_401972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_401972 prefixEnd_401972 := by exact prefixLift 401972
  have htrace : WordTrace (prefixWord ++ tailWord_401972) baseStart_401972 baseEnd_401972 := by
    simpa [prefixWord, tailWord_401972, baseEnd_401972] using wordTrace_append hprefix tailTrace_401972
  have hstable : (prefixWord ++ tailWord_401972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401972).length < 2 ^ (prefixWord ++ tailWord_401972).sum := by decide
  have hdescent : baseEnd_401972 < baseStart_401972 := by decide
  rcases family_descends (prefixWord ++ tailWord_401972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402062 : List Nat := [4, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_402062 : Nat := 118140960795 + 402062 * 2 ^ 59
def prefixEnd_402062 : Nat := 4983230072969 + 3 ^ 40 * 402062 * 2
def baseEnd_402062 : Nat := 91756026181382739678203

theorem tailTrace_402062 : CollatzResearch.WordTrace tailWord_402062 prefixEnd_402062 91756026181382739678203 := by
  unfold tailWord_402062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1833050733675689445984055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9776270579603677045248293 1833050733675689445984055)
  ·
    refine ⟨2749576100513534168976083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1833050733675689445984055 2749576100513534168976083)
    ·
      refine ⟨4124364150770301253464125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2749576100513534168976083 4124364150770301253464125)
      ·
        refine ⟨1546636556538862970049047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4124364150770301253464125 1546636556538862970049047)
        ·
          refine ⟨2319954834808294455073571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546636556538862970049047 2319954834808294455073571)
          ·
            refine ⟨3479932252212441682610357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319954834808294455073571 3479932252212441682610357)
            ·
              refine ⟨326243648644916407744721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3479932252212441682610357 326243648644916407744721)
              ·
                refine ⟨244682736483687305808541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326243648644916407744721 244682736483687305808541)
                ·
                  refine ⟨91756026181382739678203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244682736483687305808541 91756026181382739678203)
                  ·
                    rfl

theorem cell21_402062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_402062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402062 prefixEnd_402062 := by exact prefixLift 402062
  have htrace : WordTrace (prefixWord ++ tailWord_402062) baseStart_402062 baseEnd_402062 := by
    simpa [prefixWord, tailWord_402062, baseEnd_402062] using wordTrace_append hprefix tailTrace_402062
  have hstable : (prefixWord ++ tailWord_402062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402062).length < 2 ^ (prefixWord ++ tailWord_402062).sum := by decide
  have hdescent : baseEnd_402062 < baseStart_402062 := by decide
  rcases family_descends (prefixWord ++ tailWord_402062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402076 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 4]
def baseStart_402076 : Nat := 118140960795 + 402076 * 2 ^ 59
def prefixEnd_402076 : Nat := 4983230072969 + 3 ^ 40 * 402076 * 2
def baseEnd_402076 : Nat := 91759221172121826444841

theorem tailTrace_402076 : CollatzResearch.WordTrace tailWord_402076 prefixEnd_402076 91759221172121826444841 := by
  unfold tailWord_402076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7332458245677397979441041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9776610994236530639254721 7332458245677397979441041)
  ·
    refine ⟨5499343684258048484580781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7332458245677397979441041 5499343684258048484580781)
    ·
      refine ⟨2062253881596768181717793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5499343684258048484580781 2062253881596768181717793)
      ·
        refine ⟨1546690411197576136288345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2062253881596768181717793 1546690411197576136288345)
        ·
          refine ⟨1160017808398182102216259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1546690411197576136288345 1160017808398182102216259)
          ·
            refine ⟨1740026712597273153324389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160017808398182102216259 1740026712597273153324389)
            ·
              refine ⟨326255008611988716248323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1740026712597273153324389 326255008611988716248323)
              ·
                refine ⟨489382512917983074372485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326255008611988716248323 489382512917983074372485)
                ·
                  refine ⟨91759221172121826444841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 489382512917983074372485 91759221172121826444841)
                  ·
                    rfl

theorem cell21_402076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_402076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402076 prefixEnd_402076 := by exact prefixLift 402076
  have htrace : WordTrace (prefixWord ++ tailWord_402076) baseStart_402076 baseEnd_402076 := by
    simpa [prefixWord, tailWord_402076, baseEnd_402076] using wordTrace_append hprefix tailTrace_402076
  have hstable : (prefixWord ++ tailWord_402076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402076).length < 2 ^ (prefixWord ++ tailWord_402076).sum := by decide
  have hdescent : baseEnd_402076 < baseStart_402076 := by decide
  rcases family_descends (prefixWord ++ tailWord_402076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402113 : List Nat := [1, 2, 6, 2, 2, 1, 2, 2, 3]
def baseStart_402113 : Nat := 118140960795 + 402113 * 2 ^ 59
def prefixEnd_402113 : Nat := 4983230072969 + 3 ^ 40 * 402113 * 2
def baseEnd_402113 : Nat := 91767665076217984328099

theorem tailTrace_402113 : CollatzResearch.WordTrace tailWord_402113 prefixEnd_402113 91767665076217984328099 := by
  unfold tailWord_402113
  simp only [CollatzResearch.WordTrace]
  refine ⟨14666265992220751277978993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9777510661480500851985995 14666265992220751277978993)
  ·
    refine ⟨10999699494165563458484245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14666265992220751277978993 10999699494165563458484245)
    ·
      refine ⟨515610913789010787116449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10999699494165563458484245 515610913789010787116449)
      ·
        refine ⟨386708185341758090337337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 515610913789010787116449 386708185341758090337337)
        ·
          refine ⟨290031139006318567753003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386708185341758090337337 290031139006318567753003)
          ·
            refine ⟨435046708509477851629505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290031139006318567753003 435046708509477851629505)
            ·
              refine ⟨326285031382108388722129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435046708509477851629505 326285031382108388722129)
              ·
                refine ⟨244713773536581291541597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326285031382108388722129 244713773536581291541597)
                ·
                  refine ⟨91767665076217984328099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244713773536581291541597 91767665076217984328099)
                  ·
                    rfl

theorem cell21_402113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 3].length) (baseStart_402113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402113 prefixEnd_402113 := by exact prefixLift 402113
  have htrace : WordTrace (prefixWord ++ tailWord_402113) baseStart_402113 baseEnd_402113 := by
    simpa [prefixWord, tailWord_402113, baseEnd_402113] using wordTrace_append hprefix tailTrace_402113
  have hstable : (prefixWord ++ tailWord_402113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402113).length < 2 ^ (prefixWord ++ tailWord_402113).sum := by decide
  have hdescent : baseEnd_402113 < baseStart_402113 := by decide
  rcases family_descends (prefixWord ++ tailWord_402113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402180 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 5]
def baseStart_402180 : Nat := 118140960795 + 402180 * 2 ^ 59
def prefixEnd_402180 : Nat := 4983230072969 + 3 ^ 40 * 402180 * 2
def baseEnd_402180 : Nat := 91782955389040756711295

theorem tailTrace_402180 : CollatzResearch.WordTrace tailWord_402180 prefixEnd_402180 91782955389040756711295 := by
  unfold tailWord_402180
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334354841489010860333997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9779139788652014480445329 7334354841489010860333997)
  ·
    refine ⟨2750383065558379072625249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7334354841489010860333997 2750383065558379072625249)
    ·
      refine ⟨2062787299168784304468937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2750383065558379072625249 2062787299168784304468937)
      ·
        refine ⟨1547090474376588228351703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2062787299168784304468937 1547090474376588228351703)
        ·
          refine ⟨2320635711564882342527555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547090474376588228351703 2320635711564882342527555)
          ·
            refine ⟨3480953567347323513791333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320635711564882342527555 3480953567347323513791333)
            ·
              refine ⟨652678793877623158835875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3480953567347323513791333 652678793877623158835875)
              ·
                refine ⟨979018190816434738253813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652678793877623158835875 979018190816434738253813)
                ·
                  refine ⟨91782955389040756711295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 979018190816434738253813 91782955389040756711295)
                  ·
                    rfl

theorem cell21_402180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_402180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402180 prefixEnd_402180 := by exact prefixLift 402180
  have htrace : WordTrace (prefixWord ++ tailWord_402180) baseStart_402180 baseEnd_402180 := by
    simpa [prefixWord, tailWord_402180, baseEnd_402180] using wordTrace_append hprefix tailTrace_402180
  have hstable : (prefixWord ++ tailWord_402180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402180).length < 2 ^ (prefixWord ++ tailWord_402180).sum := by decide
  have hdescent : baseEnd_402180 < baseStart_402180 := by decide
  rcases family_descends (prefixWord ++ tailWord_402180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402329 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 6]
def baseStart_402329 : Nat := 118140960795 + 402329 * 2 ^ 59
def prefixEnd_402329 : Nat := 4983230072969 + 3 ^ 40 * 402329 * 2
def baseEnd_402329 : Nat := 91816959219049608727657

theorem tailTrace_402329 : CollatzResearch.WordTrace tailWord_402329 prefixEnd_402329 91816959219049608727657 := by
  unfold tailWord_402329
  simp only [CollatzResearch.WordTrace]
  refine ⟨14674144159438220167842041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9782762772958813445228027 14674144159438220167842041)
  ·
    refine ⟨11005608119578665125881531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14674144159438220167842041 11005608119578665125881531)
    ·
      refine ⟨16508412179367997688822297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11005608119578665125881531 16508412179367997688822297)
      ·
        refine ⟨12381309134525998266616723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16508412179367997688822297 12381309134525998266616723)
        ·
          refine ⟨18571963701788997399925085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12381309134525998266616723 18571963701788997399925085)
          ·
            refine ⟨6964486388170874024971907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18571963701788997399925085 6964486388170874024971907)
            ·
              refine ⟨10446729582256311037457861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6964486388170874024971907 10446729582256311037457861)
              ·
                refine ⟨1958761796673058319523349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10446729582256311037457861 1958761796673058319523349)
                ·
                  refine ⟨91816959219049608727657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1958761796673058319523349 91816959219049608727657)
                  ·
                    rfl

theorem cell21_402329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_402329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402329 prefixEnd_402329 := by exact prefixLift 402329
  have htrace : WordTrace (prefixWord ++ tailWord_402329) baseStart_402329 baseEnd_402329 := by
    simpa [prefixWord, tailWord_402329, baseEnd_402329] using wordTrace_append hprefix tailTrace_402329
  have hstable : (prefixWord ++ tailWord_402329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402329).length < 2 ^ (prefixWord ++ tailWord_402329).sum := by decide
  have hdescent : baseEnd_402329 < baseStart_402329 := by decide
  rcases family_descends (prefixWord ++ tailWord_402329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402408 : List Nat := [2, 1, 4, 1, 1, 1, 2, 6, 3]
def baseStart_402408 : Nat := 118140960795 + 402408 * 2 ^ 59
def prefixEnd_402408 : Nat := 4983230072969 + 3 ^ 40 * 402408 * 2
def baseEnd_402408 : Nat := 91834988095363026910829

theorem tailTrace_402408 : CollatzResearch.WordTrace tailWord_402408 prefixEnd_402408 91834988095363026910829 := by
  unfold tailWord_402408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7338512763076008329983939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9784683684101344439978585 7338512763076008329983939)
  ·
    refine ⟨11007769144614012494975909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7338512763076008329983939 11007769144614012494975909)
    ·
      refine ⟨2063956714615127342807983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11007769144614012494975909 2063956714615127342807983)
      ·
        refine ⟨3095935071922691014211975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063956714615127342807983 3095935071922691014211975)
        ·
          refine ⟨4643902607884036521317963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3095935071922691014211975 4643902607884036521317963)
          ·
            refine ⟨6965853911826054781976945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4643902607884036521317963 6965853911826054781976945)
            ·
              refine ⟨5224390433869541086482709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6965853911826054781976945 5224390433869541086482709)
              ·
                refine ⟨244893301587634738428877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5224390433869541086482709 244893301587634738428877)
                ·
                  refine ⟨91834988095363026910829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244893301587634738428877 91834988095363026910829)
                  ·
                    rfl

theorem cell21_402408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 3].length) (baseStart_402408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402408 prefixEnd_402408 := by exact prefixLift 402408
  have htrace : WordTrace (prefixWord ++ tailWord_402408) baseStart_402408 baseEnd_402408 := by
    simpa [prefixWord, tailWord_402408, baseEnd_402408] using wordTrace_append hprefix tailTrace_402408
  have hstable : (prefixWord ++ tailWord_402408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402408).length < 2 ^ (prefixWord ++ tailWord_402408).sum := by decide
  have hdescent : baseEnd_402408 < baseStart_402408 := by decide
  rcases family_descends (prefixWord ++ tailWord_402408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402484 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 7]
def baseStart_402484 : Nat := 118140960795 + 402484 * 2 ^ 59
def prefixEnd_402484 : Nat := 4983230072969 + 3 ^ 40 * 402484 * 2
def baseEnd_402484 : Nat := 91852332330803783644007

theorem tailTrace_402484 : CollatzResearch.WordTrace tailWord_402484 prefixEnd_402484 91852332330803783644007 := by
  unfold tailWord_402484
  simp only [CollatzResearch.WordTrace]
  refine ⟨7339898736938340819867253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9786531649251121093156337 7339898736938340819867253)
  ·
    refine ⟨688115506587969451862555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7339898736938340819867253 688115506587969451862555)
    ·
      refine ⟨1032173259881954177793833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 688115506587969451862555 1032173259881954177793833)
      ·
        refine ⟨774129944911465633345375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1032173259881954177793833 774129944911465633345375)
        ·
          refine ⟨1161194917367198450018063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774129944911465633345375 1161194917367198450018063)
          ·
            refine ⟨1741792376050797675027095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161194917367198450018063 1741792376050797675027095)
            ·
              refine ⟨2612688564076196512540643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741792376050797675027095 2612688564076196512540643)
              ·
                refine ⟨3919032846114294768810965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612688564076196512540643 3919032846114294768810965)
                ·
                  refine ⟨91852332330803783644007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3919032846114294768810965 91852332330803783644007)
                  ·
                    rfl

theorem cell21_402484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_402484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402484 prefixEnd_402484 := by exact prefixLift 402484
  have htrace : WordTrace (prefixWord ++ tailWord_402484) baseStart_402484 baseEnd_402484 := by
    simpa [prefixWord, tailWord_402484, baseEnd_402484] using wordTrace_append hprefix tailTrace_402484
  have hstable : (prefixWord ++ tailWord_402484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402484).length < 2 ^ (prefixWord ++ tailWord_402484).sum := by decide
  have hdescent : baseEnd_402484 < baseStart_402484 := by decide
  rcases family_descends (prefixWord ++ tailWord_402484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402518 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_402518 : Nat := 118140960795 + 402518 * 2 ^ 59
def prefixEnd_402518 : Nat := 4983230072969 + 3 ^ 40 * 402518 * 2
def baseEnd_402518 : Nat := 91860091594027280077271

theorem tailTrace_402518 : CollatzResearch.WordTrace tailWord_402518 prefixEnd_402518 91860091594027280077271 := by
  unfold tailWord_402518
  simp only [CollatzResearch.WordTrace]
  refine ⟨917564847234594090404513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9787358370502336964314805 917564847234594090404513)
  ·
    refine ⟨688173635425945567803385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 917564847234594090404513 688173635425945567803385)
    ·
      refine ⟨516130226569459175852539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 688173635425945567803385 516130226569459175852539)
      ·
        refine ⟨774195339854188763778809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516130226569459175852539 774195339854188763778809)
        ·
          refine ⟨580646504890641572834107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 774195339854188763778809 580646504890641572834107)
          ·
            refine ⟨870969757335962359251161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580646504890641572834107 870969757335962359251161)
            ·
              refine ⟨653227318001971769438371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870969757335962359251161 653227318001971769438371)
              ·
                refine ⟨979840977002957654157557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653227318001971769438371 979840977002957654157557)
                ·
                  refine ⟨91860091594027280077271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 979840977002957654157557 91860091594027280077271)
                  ·
                    rfl

theorem cell21_402518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_402518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402518 prefixEnd_402518 := by exact prefixLift 402518
  have htrace : WordTrace (prefixWord ++ tailWord_402518) baseStart_402518 baseEnd_402518 := by
    simpa [prefixWord, tailWord_402518, baseEnd_402518] using wordTrace_append hprefix tailTrace_402518
  have hstable : (prefixWord ++ tailWord_402518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402518).length < 2 ^ (prefixWord ++ tailWord_402518).sum := by decide
  have hdescent : baseEnd_402518 < baseStart_402518 := by decide
  rcases family_descends (prefixWord ++ tailWord_402518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402557 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 8]
def baseStart_402557 : Nat := 118140960795 + 402557 * 2 ^ 59
def prefixEnd_402557 : Nat := 4983230072969 + 3 ^ 40 * 402557 * 2
def baseEnd_402557 : Nat := 91868991925371878927191

theorem tailTrace_402557 : CollatzResearch.WordTrace tailWord_402557 prefixEnd_402557 91868991925371878927191 := by
  unfold tailWord_402557
  simp only [CollatzResearch.WordTrace]
  refine ⟨14682460002612215107141925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9788306668408143404761283 14682460002612215107141925)
  ·
    refine ⟨2752961250489790332589111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14682460002612215107141925 2752961250489790332589111)
    ·
      refine ⟨4129441875734685498883667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2752961250489790332589111 4129441875734685498883667)
      ·
        refine ⟨6194162813602028248325501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4129441875734685498883667 6194162813602028248325501)
        ·
          refine ⟨2322811055100760593122063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6194162813602028248325501 2322811055100760593122063)
          ·
            refine ⟨3484216582651140889683095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322811055100760593122063 3484216582651140889683095)
            ·
              refine ⟨5226324873976711334524643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484216582651140889683095 5226324873976711334524643)
              ·
                refine ⟨7839487310965067001786965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226324873976711334524643 7839487310965067001786965)
                ·
                  refine ⟨91868991925371878927191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7839487310965067001786965 91868991925371878927191)
                  ·
                    rfl

theorem cell21_402557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_402557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402557 prefixEnd_402557 := by exact prefixLift 402557
  have htrace : WordTrace (prefixWord ++ tailWord_402557) baseStart_402557 baseEnd_402557 := by
    simpa [prefixWord, tailWord_402557, baseEnd_402557] using wordTrace_append hprefix tailTrace_402557
  have hstable : (prefixWord ++ tailWord_402557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402557).length < 2 ^ (prefixWord ++ tailWord_402557).sum := by decide
  have hdescent : baseEnd_402557 < baseStart_402557 := by decide
  rcases family_descends (prefixWord ++ tailWord_402557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402560 : List Nat := [2, 1, 1, 2, 1, 3, 5, 3, 3]
def baseStart_402560 : Nat := 118140960795 + 402560 * 2 ^ 59
def prefixEnd_402560 : Nat := 4983230072969 + 3 ^ 40 * 402560 * 2
def baseEnd_402560 : Nat := 91869676566244540377185

theorem tailTrace_402560 : CollatzResearch.WordTrace tailWord_402560 prefixEnd_402560 91869676566244540377185 := by
  unfold tailWord_402560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341284710800673309750567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9788379614400897746334089 7341284710800673309750567)
  ·
    refine ⟨11011927066201009964625851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7341284710800673309750567 11011927066201009964625851)
    ·
      refine ⟨16517890599301514946938777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11011927066201009964625851 16517890599301514946938777)
      ·
        refine ⟨12388417949476136210204083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16517890599301514946938777 12388417949476136210204083)
        ·
          refine ⟨18582626924214204315306125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12388417949476136210204083 18582626924214204315306125)
          ·
            refine ⟨6968485096580326618239797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18582626924214204315306125 6968485096580326618239797)
            ·
              refine ⟨653295477804405620459981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6968485096580326618239797 653295477804405620459981)
              ·
                refine ⟨244985804176652107672493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 653295477804405620459981 244985804176652107672493)
                ·
                  refine ⟨91869676566244540377185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244985804176652107672493 91869676566244540377185)
                  ·
                    rfl

theorem cell21_402560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 3].length) (baseStart_402560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402560 prefixEnd_402560 := by exact prefixLift 402560
  have htrace : WordTrace (prefixWord ++ tailWord_402560) baseStart_402560 baseEnd_402560 := by
    simpa [prefixWord, tailWord_402560, baseEnd_402560] using wordTrace_append hprefix tailTrace_402560
  have hstable : (prefixWord ++ tailWord_402560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402560).length < 2 ^ (prefixWord ++ tailWord_402560).sum := by decide
  have hdescent : baseEnd_402560 < baseStart_402560 := by decide
  rcases family_descends (prefixWord ++ tailWord_402560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402574 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_402574 : Nat := 118140960795 + 402574 * 2 ^ 59
def prefixEnd_402574 : Nat := 4983230072969 + 3 ^ 40 * 402574 * 2
def baseEnd_402574 : Nat := 91872871556983627143823

theorem tailTrace_402574 : CollatzResearch.WordTrace tailWord_402574 prefixEnd_402574 91872871556983627143823 := by
  unfold tailWord_402574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1835385005443828376313847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9788720029033751340340517 1835385005443828376313847)
  ·
    refine ⟨2753077508165742564470771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1835385005443828376313847 2753077508165742564470771)
    ·
      refine ⟨4129616262248613846706157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2753077508165742564470771 4129616262248613846706157)
      ·
        refine ⟨1548606098343230192514809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4129616262248613846706157 1548606098343230192514809)
        ·
          refine ⟨1161454573757422644386107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1548606098343230192514809 1161454573757422644386107)
          ·
            refine ⟨1742181860636133966579161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161454573757422644386107 1742181860636133966579161)
            ·
              refine ⟨1306636395477100474934371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742181860636133966579161 1306636395477100474934371)
              ·
                refine ⟨1959954593215650712401557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1306636395477100474934371 1959954593215650712401557)
                ·
                  refine ⟨91872871556983627143823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1959954593215650712401557 91872871556983627143823)
                  ·
                    rfl

theorem cell21_402574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_402574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402574 prefixEnd_402574 := by exact prefixLift 402574
  have htrace : WordTrace (prefixWord ++ tailWord_402574) baseStart_402574 baseEnd_402574 := by
    simpa [prefixWord, tailWord_402574, baseEnd_402574] using wordTrace_append hprefix tailTrace_402574
  have hstable : (prefixWord ++ tailWord_402574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402574).length < 2 ^ (prefixWord ++ tailWord_402574).sum := by decide
  have hdescent : baseEnd_402574 < baseStart_402574 := by decide
  rcases family_descends (prefixWord ++ tailWord_402574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402588 : List Nat := [2, 2, 3, 2, 1, 2, 1, 8]
def baseStart_402588 : Nat := 118140960795 + 402588 * 2 ^ 59
def prefixEnd_402588 : Nat := 4983230072969 + 3 ^ 40 * 402588 * 2
def baseEnd_402588 : Nat := 30625355515907571303487

theorem tailTrace_402588 : CollatzResearch.WordTrace tailWord_402588 prefixEnd_402588 30625355515907571303487 := by
  unfold tailWord_402588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341795332749953700760209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9789060443666604934346945 7341795332749953700760209)
  ·
    refine ⟨5506346499562465275570157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7341795332749953700760209 5506346499562465275570157)
    ·
      refine ⟨2064879937335924478338809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5506346499562465275570157 2064879937335924478338809)
      ·
        refine ⟨1548659953001943358754107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2064879937335924478338809 1548659953001943358754107)
        ·
          refine ⟨2322989929502915038131161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548659953001943358754107 2322989929502915038131161)
          ·
            refine ⟨1742242447127186278598371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2322989929502915038131161 1742242447127186278598371)
            ·
              refine ⟨2613363670690779417897557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742242447127186278598371 2613363670690779417897557)
              ·
                refine ⟨30625355515907571303487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2613363670690779417897557 30625355515907571303487)
                ·
                  rfl

theorem cell21_402588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_402588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402588 prefixEnd_402588 := by exact prefixLift 402588
  have htrace : WordTrace (prefixWord ++ tailWord_402588) baseStart_402588 baseEnd_402588 := by
    simpa [prefixWord, tailWord_402588, baseEnd_402588] using wordTrace_append hprefix tailTrace_402588
  have hstable : (prefixWord ++ tailWord_402588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402588).length < 2 ^ (prefixWord ++ tailWord_402588).sum := by decide
  have hdescent : baseEnd_402588 < baseStart_402588 := by decide
  rcases family_descends (prefixWord ++ tailWord_402588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402591 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 4]
def baseStart_402591 : Nat := 118140960795 + 402591 * 2 ^ 59
def prefixEnd_402591 : Nat := 4983230072969 + 3 ^ 40 * 402591 * 2
def baseEnd_402591 : Nat := 91876751188595375360455

theorem tailTrace_402591 : CollatzResearch.WordTrace tailWord_402591 prefixEnd_402591 91876751188595375360455 := by
  unfold tailWord_402591
  simp only [CollatzResearch.WordTrace]
  refine ⟨14683700084489038913879627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9789133389659359275919751 14683700084489038913879627)
  ·
    refine ⟨22025550126733558370819441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14683700084489038913879627 22025550126733558370819441)
    ·
      refine ⟨16519162595050168778114581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22025550126733558370819441 16519162595050168778114581)
      ·
        refine ⟨774335746642976661474121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16519162595050168778114581 774335746642976661474121)
        ·
          refine ⟨580751809982232496105591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 774335746642976661474121 580751809982232496105591)
          ·
            refine ⟨871127714973348744158387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580751809982232496105591 871127714973348744158387)
            ·
              refine ⟨1306691572460023116237581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871127714973348744158387 1306691572460023116237581)
              ·
                refine ⟨490009339672508668589093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1306691572460023116237581 490009339672508668589093)
                ·
                  refine ⟨91876751188595375360455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 490009339672508668589093 91876751188595375360455)
                  ·
                    rfl

theorem cell21_402591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 4].length) (baseStart_402591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402591 prefixEnd_402591 := by exact prefixLift 402591
  have htrace : WordTrace (prefixWord ++ tailWord_402591) baseStart_402591 baseEnd_402591 := by
    simpa [prefixWord, tailWord_402591, baseEnd_402591] using wordTrace_append hprefix tailTrace_402591
  have hstable : (prefixWord ++ tailWord_402591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402591).length < 2 ^ (prefixWord ++ tailWord_402591).sum := by decide
  have hdescent : baseEnd_402591 < baseStart_402591 := by decide
  rcases family_descends (prefixWord ++ tailWord_402591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402684 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 4]
def baseStart_402684 : Nat := 118140960795 + 402684 * 2 ^ 59
def prefixEnd_402684 : Nat := 4983230072969 + 3 ^ 40 * 402684 * 2
def baseEnd_402684 : Nat := 91897975055647880310265

theorem tailTrace_402684 : CollatzResearch.WordTrace tailWord_402684 prefixEnd_402684 91897975055647880310265 := by
  unfold tailWord_402684
  simp only [CollatzResearch.WordTrace]
  refine ⟨7343546036576057898507553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9791394715434743864676737 7343546036576057898507553)
  ·
    refine ⟨5507659527432043423880665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7343546036576057898507553 5507659527432043423880665)
    ·
      refine ⟨4130744645574032567910499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5507659527432043423880665 4130744645574032567910499)
      ·
        refine ⟨6196116968361048851865749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4130744645574032567910499 6196116968361048851865749)
        ·
          refine ⟨290442982891924164931207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6196116968361048851865749 290442982891924164931207)
          ·
            refine ⟨435664474337886247396811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290442982891924164931207 435664474337886247396811)
            ·
              refine ⟨653496711506829371095217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435664474337886247396811 653496711506829371095217)
              ·
                refine ⟨490122533630122028321413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653496711506829371095217 490122533630122028321413)
                ·
                  refine ⟨91897975055647880310265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 490122533630122028321413 91897975055647880310265)
                  ·
                    rfl

theorem cell21_402684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_402684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402684 prefixEnd_402684 := by exact prefixLift 402684
  have htrace : WordTrace (prefixWord ++ tailWord_402684) baseStart_402684 baseEnd_402684 := by
    simpa [prefixWord, tailWord_402684, baseEnd_402684] using wordTrace_append hprefix tailTrace_402684
  have hstable : (prefixWord ++ tailWord_402684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402684).length < 2 ^ (prefixWord ++ tailWord_402684).sum := by decide
  have hdescent : baseEnd_402684 < baseStart_402684 := by decide
  rcases family_descends (prefixWord ++ tailWord_402684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402802 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_402802 : Nat := 118140960795 + 402802 * 2 ^ 59
def prefixEnd_402802 : Nat := 4983230072969 + 3 ^ 40 * 402802 * 2
def baseEnd_402802 : Nat := 91924904263305897343357

theorem tailTrace_402802 : CollatzResearch.WordTrace tailWord_402802 prefixEnd_402802 91924904263305897343357 := by
  unfold tailWord_402802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3672848971681155487452665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9794263924483081299873773 3672848971681155487452665)
  ·
    refine ⟨2754636728760866615589499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3672848971681155487452665 2754636728760866615589499)
    ·
      refine ⟨4131955093141299923384249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2754636728760866615589499 4131955093141299923384249)
      ·
        refine ⟨3098966319855974942538187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4131955093141299923384249 3098966319855974942538187)
        ·
          refine ⟨4648449479783962413807281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3098966319855974942538187 4648449479783962413807281)
          ·
            refine ⟨3486337109837971810355461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4648449479783962413807281 3486337109837971810355461)
            ·
              refine ⟨653688208094619714441649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3486337109837971810355461 653688208094619714441649)
              ·
                refine ⟨490266156070964785831237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653688208094619714441649 490266156070964785831237)
                ·
                  refine ⟨91924904263305897343357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 490266156070964785831237 91924904263305897343357)
                  ·
                    rfl

theorem cell21_402802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_402802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402802 prefixEnd_402802 := by exact prefixLift 402802
  have htrace : WordTrace (prefixWord ++ tailWord_402802) baseStart_402802 baseEnd_402802 := by
    simpa [prefixWord, tailWord_402802, baseEnd_402802] using wordTrace_append hprefix tailTrace_402802
  have hstable : (prefixWord ++ tailWord_402802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402802).length < 2 ^ (prefixWord ++ tailWord_402802).sum := by decide
  have hdescent : baseEnd_402802 < baseStart_402802 := by decide
  rcases family_descends (prefixWord ++ tailWord_402802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402805 : List Nat := [1, 3, 4, 1, 3, 1, 1, 4, 3]
def baseStart_402805 : Nat := 118140960795 + 402805 * 2 ^ 59
def prefixEnd_402805 : Nat := 4983230072969 + 3 ^ 40 * 402805 * 2
def baseEnd_402805 : Nat := 91925588904178558793351

theorem tailTrace_402805 : CollatzResearch.WordTrace tailWord_402805 prefixEnd_402805 91925588904178558793351 := by
  unfold tailWord_402805
  simp only [CollatzResearch.WordTrace]
  refine ⟨14691505305713753462169869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9794336870475835641446579 14691505305713753462169869)
  ·
    refine ⟨5509314489642657548313701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14691505305713753462169869 5509314489642657548313701)
    ·
      refine ⟨1032996466807998290308819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5509314489642657548313701 1032996466807998290308819)
      ·
        refine ⟨1549494700211997435463229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032996466807998290308819 1549494700211997435463229)
        ·
          refine ⟨581060512579499038298711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1549494700211997435463229 581060512579499038298711)
          ·
            refine ⟨871590768869248557448067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581060512579499038298711 871590768869248557448067)
            ·
              refine ⟨1307386153303872836172101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871590768869248557448067 1307386153303872836172101)
              ·
                refine ⟨245134903744476156782269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1307386153303872836172101 245134903744476156782269)
                ·
                  refine ⟨91925588904178558793351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245134903744476156782269 91925588904178558793351)
                  ·
                    rfl

theorem cell21_402805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_402805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402805 prefixEnd_402805 := by exact prefixLift 402805
  have htrace : WordTrace (prefixWord ++ tailWord_402805) baseStart_402805 baseEnd_402805 := by
    simpa [prefixWord, tailWord_402805, baseEnd_402805] using wordTrace_append hprefix tailTrace_402805
  have hstable : (prefixWord ++ tailWord_402805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402805).length < 2 ^ (prefixWord ++ tailWord_402805).sum := by decide
  have hdescent : baseEnd_402805 < baseStart_402805 := by decide
  rcases family_descends (prefixWord ++ tailWord_402805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402892 : List Nat := [2, 2, 1, 4, 2, 2, 1, 7]
def baseStart_402892 : Nat := 118140960795 + 402892 * 2 ^ 59
def prefixEnd_402892 : Nat := 4983230072969 + 3 ^ 40 * 402892 * 2
def baseEnd_402892 : Nat := 30648481163161913614391

theorem tailTrace_402892 : CollatzResearch.WordTrace tailWord_402892 prefixEnd_402892 30648481163161913614391 := by
  unfold tailWord_402892
  simp only [CollatzResearch.WordTrace]
  refine ⟨7347339228199283660293465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9796452304265711547057953 7347339228199283660293465)
  ·
    refine ⟨5510504421149462745220099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7347339228199283660293465 5510504421149462745220099)
    ·
      refine ⟨8265756631724194117830149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5510504421149462745220099 8265756631724194117830149)
      ·
        refine ⟨1549829368448286397093153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8265756631724194117830149 1549829368448286397093153)
        ·
          refine ⟨1162372026336214797819865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1549829368448286397093153 1162372026336214797819865)
          ·
            refine ⟨871779019752161098364899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1162372026336214797819865 871779019752161098364899)
            ·
              refine ⟨1307668529628241647547349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871779019752161098364899 1307668529628241647547349)
              ·
                refine ⟨30648481163161913614391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1307668529628241647547349 30648481163161913614391)
                ·
                  rfl

theorem cell21_402892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_402892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402892 prefixEnd_402892 := by exact prefixLift 402892
  have htrace : WordTrace (prefixWord ++ tailWord_402892) baseStart_402892 baseEnd_402892 := by
    simpa [prefixWord, tailWord_402892, baseEnd_402892] using wordTrace_append hprefix tailTrace_402892
  have hstable : (prefixWord ++ tailWord_402892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402892).length < 2 ^ (prefixWord ++ tailWord_402892).sum := by decide
  have hdescent : baseEnd_402892 < baseStart_402892 := by decide
  rcases family_descends (prefixWord ++ tailWord_402892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402968 : List Nat := [2, 1, 2, 3, 5, 8]
def baseStart_402968 : Nat := 118140960795 + 402968 * 2 ^ 59
def prefixEnd_402968 : Nat := 4983230072969 + 3 ^ 40 * 402968 * 2
def baseEnd_402968 : Nat := 3406029174997277688013

theorem tailTrace_402968 : CollatzResearch.WordTrace tailWord_402968 prefixEnd_402968 3406029174997277688013 := by
  unfold tailWord_402968
  simp only [CollatzResearch.WordTrace]
  refine ⟨7348725202061616150176779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9798300269415488200235705 7348725202061616150176779)
  ·
    refine ⟨11023087803092424225265169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7348725202061616150176779 11023087803092424225265169)
    ·
      refine ⟨8267315852319318168948877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11023087803092424225265169 8267315852319318168948877)
      ·
        refine ⟨3100243444619744313355829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8267315852319318168948877 3100243444619744313355829)
        ·
          refine ⟨290647822933101029377109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3100243444619744313355829 290647822933101029377109)
          ·
            refine ⟨3406029174997277688013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 290647822933101029377109 3406029174997277688013)
            ·
              rfl

theorem cell21_402968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 8].length) (baseStart_402968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_402968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_402968 prefixEnd_402968 := by exact prefixLift 402968
  have htrace : WordTrace (prefixWord ++ tailWord_402968) baseStart_402968 baseEnd_402968 := by
    simpa [prefixWord, tailWord_402968, baseEnd_402968] using wordTrace_append hprefix tailTrace_402968
  have hstable : (prefixWord ++ tailWord_402968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402968).length < 2 ^ (prefixWord ++ tailWord_402968).sum := by decide
  have hdescent : baseEnd_402968 < baseStart_402968 := by decide
  rcases family_descends (prefixWord ++ tailWord_402968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403061 : List Nat := [1, 3, 4, 2, 1, 1, 4, 5]
def baseStart_403061 : Nat := 118140960795 + 403061 * 2 ^ 59
def prefixEnd_403061 : Nat := 4983230072969 + 3 ^ 40 * 403061 * 2
def baseEnd_403061 : Nat := 30661337197326334175387

theorem tailTrace_403061 : CollatzResearch.WordTrace tailWord_403061 prefixEnd_403061 30661337197326334175387 := by
  unfold tailWord_403061
  simp only [CollatzResearch.WordTrace]
  refine ⟨14700842392786309183489037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9800561595190872788992691 14700842392786309183489037)
  ·
    refine ⟨5512815897294865943808389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14700842392786309183489037 5512815897294865943808389)
    ·
      refine ⟨1033652980742787364464073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5512815897294865943808389 1033652980742787364464073)
      ·
        refine ⟨775239735557090523348055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1033652980742787364464073 775239735557090523348055)
        ·
          refine ⟨1162859603335635785022083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775239735557090523348055 1162859603335635785022083)
          ·
            refine ⟨1744289405003453677533125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162859603335635785022083 1744289405003453677533125)
            ·
              refine ⟨327054263438147564537461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1744289405003453677533125 327054263438147564537461)
              ·
                refine ⟨30661337197326334175387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327054263438147564537461 30661337197326334175387)
                ·
                  rfl

theorem cell21_403061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 5].length) (baseStart_403061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403061 prefixEnd_403061 := by exact prefixLift 403061
  have htrace : WordTrace (prefixWord ++ tailWord_403061) baseStart_403061 baseEnd_403061 := by
    simpa [prefixWord, tailWord_403061, baseEnd_403061] using wordTrace_append hprefix tailTrace_403061
  have hstable : (prefixWord ++ tailWord_403061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403061).length < 2 ^ (prefixWord ++ tailWord_403061).sum := by decide
  have hdescent : baseEnd_403061 < baseStart_403061 := by decide
  rcases family_descends (prefixWord ++ tailWord_403061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403072 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_403072 : Nat := 118140960795 + 403072 * 2 ^ 59
def prefixEnd_403072 : Nat := 4983230072969 + 3 ^ 40 * 403072 * 2
def baseEnd_403072 : Nat := 91986521941845427842805

theorem tailTrace_403072 : CollatzResearch.WordTrace tailWord_403072 prefixEnd_403072 91986521941845427842805 := by
  unfold tailWord_403072
  simp only [CollatzResearch.WordTrace]
  refine ⟨7350621797873229031069735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9800829063830972041426313 7350621797873229031069735)
  ·
    refine ⟨11025932696809843546604603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7350621797873229031069735 11025932696809843546604603)
    ·
      refine ⟨16538899045214765319906905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11025932696809843546604603 16538899045214765319906905)
      ·
        refine ⟨12404174283911073989930179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16538899045214765319906905 12404174283911073989930179)
        ·
          refine ⟨18606261425866610984895269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12404174283911073989930179 18606261425866610984895269)
          ·
            refine ⟨3488674017349989559667863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18606261425866610984895269 3488674017349989559667863)
            ·
              refine ⟨5233011026024984339501795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488674017349989559667863 5233011026024984339501795)
              ·
                refine ⟨7849516539037476509252693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5233011026024984339501795 7849516539037476509252693)
                ·
                  refine ⟨91986521941845427842805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7849516539037476509252693 91986521941845427842805)
                  ·
                    rfl

theorem cell21_403072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_403072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403072 prefixEnd_403072 := by exact prefixLift 403072
  have htrace : WordTrace (prefixWord ++ tailWord_403072) baseStart_403072 baseEnd_403072 := by
    simpa [prefixWord, tailWord_403072, baseEnd_403072] using wordTrace_append hprefix tailTrace_403072
  have hstable : (prefixWord ++ tailWord_403072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403072).length < 2 ^ (prefixWord ++ tailWord_403072).sum := by decide
  have hdescent : baseEnd_403072 < baseStart_403072 := by decide
  rcases family_descends (prefixWord ++ tailWord_403072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403210 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_403210 : Nat := 118140960795 + 403210 * 2 ^ 59
def prefixEnd_403210 : Nat := 4983230072969 + 3 ^ 40 * 403210 * 2
def baseEnd_403210 : Nat := 92018015421987854542523

theorem tailTrace_403210 : CollatzResearch.WordTrace tailWord_403210 prefixEnd_403210 92018015421987854542523 := by
  unfold tailWord_403210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3676569217311626907665771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9804184579497671753775389 3676569217311626907665771)
  ·
    refine ⟨5514853825967440361498657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3676569217311626907665771 5514853825967440361498657)
    ·
      refine ⟨4136140369475580271123993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5514853825967440361498657 4136140369475580271123993)
      ·
        refine ⟨3102105277106685203342995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4136140369475580271123993 3102105277106685203342995)
        ·
          refine ⟨4653157915660027805014493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102105277106685203342995 4653157915660027805014493)
          ·
            refine ⟨1744934218372510426880435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4653157915660027805014493 1744934218372510426880435)
            ·
              refine ⟨2617401327558765640320653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744934218372510426880435 2617401327558765640320653)
              ·
                refine ⟨981525497834537115120245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2617401327558765640320653 981525497834537115120245)
                ·
                  refine ⟨92018015421987854542523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 981525497834537115120245 92018015421987854542523)
                  ·
                    rfl

theorem cell21_403210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_403210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403210 prefixEnd_403210 := by exact prefixLift 403210
  have htrace : WordTrace (prefixWord ++ tailWord_403210) baseStart_403210 baseEnd_403210 := by
    simpa [prefixWord, tailWord_403210, baseEnd_403210] using wordTrace_append hprefix tailTrace_403210
  have hstable : (prefixWord ++ tailWord_403210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403210).length < 2 ^ (prefixWord ++ tailWord_403210).sum := by decide
  have hdescent : baseEnd_403210 < baseStart_403210 := by decide
  rcases family_descends (prefixWord ++ tailWord_403210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403230 : List Nat := [4, 3, 2, 2, 1, 1, 1, 7]
def baseStart_403230 : Nat := 118140960795 + 403230 * 2 ^ 59
def prefixEnd_403230 : Nat := 4983230072969 + 3 ^ 40 * 403230 * 2
def baseEnd_403230 : Nat := 30674193231490754736383

theorem tailTrace_403230 : CollatzResearch.WordTrace tailWord_403230 prefixEnd_403230 30674193231490754736383 := by
  unfold tailWord_403230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1838375791146756380798893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9804670886116034030927429 1838375791146756380798893)
  ·
    refine ⟨689390921680033642799585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1838375791146756380798893 689390921680033642799585)
    ·
      refine ⟨517043191260025232099689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 689390921680033642799585 517043191260025232099689)
      ·
        refine ⟨387782393445018924074767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517043191260025232099689 387782393445018924074767)
        ·
          refine ⟨581673590167528386112151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387782393445018924074767 581673590167528386112151)
          ·
            refine ⟨872510385251292579168227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581673590167528386112151 872510385251292579168227)
            ·
              refine ⟨1308765577876938868752341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872510385251292579168227 1308765577876938868752341)
              ·
                refine ⟨30674193231490754736383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1308765577876938868752341 30674193231490754736383)
                ·
                  rfl

theorem cell21_403230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_403230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403230 prefixEnd_403230 := by exact prefixLift 403230
  have htrace : WordTrace (prefixWord ++ tailWord_403230) baseStart_403230 baseEnd_403230 := by
    simpa [prefixWord, tailWord_403230, baseEnd_403230] using wordTrace_append hprefix tailTrace_403230
  have hstable : (prefixWord ++ tailWord_403230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403230).length < 2 ^ (prefixWord ++ tailWord_403230).sum := by decide
  have hdescent : baseEnd_403230 < baseStart_403230 := by decide
  rcases family_descends (prefixWord ++ tailWord_403230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403244 : List Nat := [2, 2, 1, 1, 1, 7, 1, 3, 3]
def baseStart_403244 : Nat := 118140960795 + 403244 * 2 ^ 59
def prefixEnd_403244 : Nat := 4983230072969 + 3 ^ 40 * 403244 * 2
def baseEnd_403244 : Nat := 92025774685211350975787

theorem tailTrace_403244 : CollatzResearch.WordTrace tailWord_403244 prefixEnd_403244 92025774685211350975787 := by
  unfold tailWord_403244
  simp only [CollatzResearch.WordTrace]
  refine ⟨7353758475561665718700393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9805011300748887624933857 7353758475561665718700393)
  ·
    refine ⟨5515318856671249289025295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7353758475561665718700393 5515318856671249289025295)
    ·
      refine ⟨8272978285006873933537943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5515318856671249289025295 8272978285006873933537943)
      ·
        refine ⟨12409467427510310900306915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272978285006873933537943 12409467427510310900306915)
        ·
          refine ⟨18614201141265466350460373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12409467427510310900306915 18614201141265466350460373)
          ·
            refine ⟨436270339248409367588915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 18614201141265466350460373 436270339248409367588915)
            ·
              refine ⟨654405508872614051383373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436270339248409367588915 654405508872614051383373)
              ·
                refine ⟨245402065827230269268765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 654405508872614051383373 245402065827230269268765)
                ·
                  refine ⟨92025774685211350975787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245402065827230269268765 92025774685211350975787)
                  ·
                    rfl

theorem cell21_403244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_403244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403244 prefixEnd_403244 := by exact prefixLift 403244
  have htrace : WordTrace (prefixWord ++ tailWord_403244) baseStart_403244 baseEnd_403244 := by
    simpa [prefixWord, tailWord_403244, baseEnd_403244] using wordTrace_append hprefix tailTrace_403244
  have hstable : (prefixWord ++ tailWord_403244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403244).length < 2 ^ (prefixWord ++ tailWord_403244).sum := by decide
  have hdescent : baseEnd_403244 < baseStart_403244 := by decide
  rcases family_descends (prefixWord ++ tailWord_403244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403261 : List Nat := [1, 4, 1, 4, 1, 2, 3, 2, 3]
def baseStart_403261 : Nat := 118140960795 + 403261 * 2 ^ 59
def prefixEnd_403261 : Nat := 4983230072969 + 3 ^ 40 * 403261 * 2
def baseEnd_403261 : Nat := 92029654316823099192419

theorem tailTrace_403261 : CollatzResearch.WordTrace tailWord_403261 prefixEnd_403261 92029654316823099192419 := by
  unfold tailWord_403261
  simp only [CollatzResearch.WordTrace]
  refine ⟨14708136992061743340769637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9805424661374495560513091 14708136992061743340769637)
  ·
    refine ⟨2757775686011576876394307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14708136992061743340769637 2757775686011576876394307)
    ·
      refine ⟨4136663529017365314591461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757775686011576876394307 4136663529017365314591461)
      ·
        refine ⟨775624411690755996485899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4136663529017365314591461 775624411690755996485899)
        ·
          refine ⟨1163436617536133994728849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775624411690755996485899 1163436617536133994728849)
          ·
            refine ⟨872577463152100496046637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1163436617536133994728849 872577463152100496046637)
            ·
              refine ⟨327216548682037686017489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 872577463152100496046637 327216548682037686017489)
              ·
                refine ⟨245412411511528264513117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327216548682037686017489 245412411511528264513117)
                ·
                  refine ⟨92029654316823099192419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245412411511528264513117 92029654316823099192419)
                  ·
                    rfl

theorem cell21_403261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_403261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403261 prefixEnd_403261 := by exact prefixLift 403261
  have htrace : WordTrace (prefixWord ++ tailWord_403261) baseStart_403261 baseEnd_403261 := by
    simpa [prefixWord, tailWord_403261, baseEnd_403261] using wordTrace_append hprefix tailTrace_403261
  have hstable : (prefixWord ++ tailWord_403261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403261).length < 2 ^ (prefixWord ++ tailWord_403261).sum := by decide
  have hdescent : baseEnd_403261 < baseStart_403261 := by decide
  rcases family_descends (prefixWord ++ tailWord_403261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403303 : List Nat := [1, 1, 5, 1, 2, 1, 2, 5, 3]
def baseStart_403303 : Nat := 118140960795 + 403303 * 2 ^ 59
def prefixEnd_403303 : Nat := 4983230072969 + 3 ^ 40 * 403303 * 2
def baseEnd_403303 : Nat := 92039239289040359492333

theorem tailTrace_403303 : CollatzResearch.WordTrace tailWord_403303 prefixEnd_403303 92039239289040359492333 := by
  unfold tailWord_403303
  simp only [CollatzResearch.WordTrace]
  refine ⟨14709668857909584513798563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9806445905273056342532375 14709668857909584513798563)
  ·
    refine ⟨22064503286864376770697845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14709668857909584513798563 22064503286864376770697845)
    ·
      refine ⟨2068547183143535322252923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22064503286864376770697845 2068547183143535322252923)
      ·
        refine ⟨3102820774715302983379385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2068547183143535322252923 3102820774715302983379385)
        ·
          refine ⟨2327115581036477237534539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3102820774715302983379385 2327115581036477237534539)
          ·
            refine ⟨3490673371554715856301809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327115581036477237534539 3490673371554715856301809)
            ·
              refine ⟨2618005028666036892226357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3490673371554715856301809 2618005028666036892226357)
              ·
                refine ⟨245437971437440958646221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2618005028666036892226357 245437971437440958646221)
                ·
                  refine ⟨92039239289040359492333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245437971437440958646221 92039239289040359492333)
                  ·
                    rfl

theorem cell21_403303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 3].length) (baseStart_403303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403303 prefixEnd_403303 := by exact prefixLift 403303
  have htrace : WordTrace (prefixWord ++ tailWord_403303) baseStart_403303 baseEnd_403303 := by
    simpa [prefixWord, tailWord_403303, baseEnd_403303] using wordTrace_append hprefix tailTrace_403303
  have hstable : (prefixWord ++ tailWord_403303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403303).length < 2 ^ (prefixWord ++ tailWord_403303).sum := by decide
  have hdescent : baseEnd_403303 < baseStart_403303 := by decide
  rcases family_descends (prefixWord ++ tailWord_403303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403331 : List Nat := [1, 1, 1, 3, 4, 2, 3, 6]
def baseStart_403331 : Nat := 118140960795 + 403331 * 2 ^ 59
def prefixEnd_403331 : Nat := 4983230072969 + 3 ^ 40 * 403331 * 2
def baseEnd_403331 : Nat := 30681876423506177675203

theorem tailTrace_403331 : CollatzResearch.WordTrace tailWord_403331 prefixEnd_403331 30681876423506177675203 := by
  unfold tailWord_403331
  simp only [CollatzResearch.WordTrace]
  refine ⟨14710690101808145295817847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9807126734538763530545231 14710690101808145295817847)
  ·
    refine ⟨22066035152712217943726771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14710690101808145295817847 22066035152712217943726771)
    ·
      refine ⟨33099052729068326915590157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22066035152712217943726771 33099052729068326915590157)
      ·
        refine ⟨12412144773400622593346309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33099052729068326915590157 12412144773400622593346309)
        ·
          refine ⟨2327277145012616736252433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12412144773400622593346309 2327277145012616736252433)
          ·
            refine ⟨1745457858759462552189325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2327277145012616736252433 1745457858759462552189325)
            ·
              refine ⟨654546697034798457070997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1745457858759462552189325 654546697034798457070997)
              ·
                refine ⟨30681876423506177675203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 654546697034798457070997 30681876423506177675203)
                ·
                  rfl

theorem cell21_403331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 6].length) (baseStart_403331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403331 prefixEnd_403331 := by exact prefixLift 403331
  have htrace : WordTrace (prefixWord ++ tailWord_403331) baseStart_403331 baseEnd_403331 := by
    simpa [prefixWord, tailWord_403331, baseEnd_403331] using wordTrace_append hprefix tailTrace_403331
  have hstable : (prefixWord ++ tailWord_403331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403331).length < 2 ^ (prefixWord ++ tailWord_403331).sum := by decide
  have hdescent : baseEnd_403331 < baseStart_403331 := by decide
  rcases family_descends (prefixWord ++ tailWord_403331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403345 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 7]
def baseStart_403345 : Nat := 118140960795 + 403345 * 2 ^ 59
def prefixEnd_403345 : Nat := 4983230072969 + 3 ^ 40 * 403345 * 2
def baseEnd_403345 : Nat := 92048824261257619792247

theorem tailTrace_403345 : CollatzResearch.WordTrace tailWord_403345 prefixEnd_403345 92048824261257619792247 := by
  unfold tailWord_403345
  simp only [CollatzResearch.WordTrace]
  refine ⟨14711200723757425686827489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9807467149171617124551659 14711200723757425686827489)
  ·
    refine ⟨11033400542818069265120617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14711200723757425686827489 11033400542818069265120617)
    ·
      refine ⟨8275050407113551948840463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11033400542818069265120617 8275050407113551948840463)
      ·
        refine ⟨12412575610670327923260695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8275050407113551948840463 12412575610670327923260695)
        ·
          refine ⟨18618863416005491884891043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12412575610670327923260695 18618863416005491884891043)
          ·
            refine ⟨27928295124008237827336565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18618863416005491884891043 27928295124008237827336565)
            ·
              refine ⟨2618277667875772296312803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27928295124008237827336565 2618277667875772296312803)
              ·
                refine ⟨3927416501813658444469205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2618277667875772296312803 3927416501813658444469205)
                ·
                  refine ⟨92048824261257619792247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3927416501813658444469205 92048824261257619792247)
                  ·
                    rfl

theorem cell21_403345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_403345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403345 prefixEnd_403345 := by exact prefixLift 403345
  have htrace : WordTrace (prefixWord ++ tailWord_403345) baseStart_403345 baseEnd_403345 := by
    simpa [prefixWord, tailWord_403345, baseEnd_403345] using wordTrace_append hprefix tailTrace_403345
  have hstable : (prefixWord ++ tailWord_403345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403345).length < 2 ^ (prefixWord ++ tailWord_403345).sum := by decide
  have hdescent : baseEnd_403345 < baseStart_403345 := by decide
  rcases family_descends (prefixWord ++ tailWord_403345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403368 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 4]
def baseStart_403368 : Nat := 118140960795 + 403368 * 2 ^ 59
def prefixEnd_403368 : Nat := 4983230072969 + 3 ^ 40 * 403368 * 2
def baseEnd_403368 : Nat := 92054073174614690908867

theorem tailTrace_403368 : CollatzResearch.WordTrace tailWord_403368 prefixEnd_403368 92054073174614690908867 := by
  unfold tailWord_403368
  simp only [CollatzResearch.WordTrace]
  refine ⟨7356019801337050307457379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9808026401782733743276505 7356019801337050307457379)
  ·
    refine ⟨11034029702005575461186069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7356019801337050307457379 11034029702005575461186069)
    ·
      refine ⟨517220142281511349743097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11034029702005575461186069 517220142281511349743097)
      ·
        refine ⟨387915106711133512307323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517220142281511349743097 387915106711133512307323)
        ·
          refine ⟨581872660066700268460985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387915106711133512307323 581872660066700268460985)
          ·
            refine ⟨436404495050025201345739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581872660066700268460985 436404495050025201345739)
            ·
              refine ⟨654606742575037802018609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436404495050025201345739 654606742575037802018609)
              ·
                refine ⟨490955056931278351513957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654606742575037802018609 490955056931278351513957)
                ·
                  refine ⟨92054073174614690908867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 490955056931278351513957 92054073174614690908867)
                  ·
                    rfl

theorem cell21_403368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_403368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403368 prefixEnd_403368 := by exact prefixLift 403368
  have htrace : WordTrace (prefixWord ++ tailWord_403368) baseStart_403368 baseEnd_403368 := by
    simpa [prefixWord, tailWord_403368, baseEnd_403368] using wordTrace_append hprefix tailTrace_403368
  have hstable : (prefixWord ++ tailWord_403368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403368).length < 2 ^ (prefixWord ++ tailWord_403368).sum := by decide
  have hdescent : baseEnd_403368 < baseStart_403368 := by decide
  rcases family_descends (prefixWord ++ tailWord_403368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403489 : List Nat := [1, 2, 3, 2, 4, 2, 2, 2, 3]
def baseStart_403489 : Nat := 118140960795 + 403489 * 2 ^ 59
def prefixEnd_403489 : Nat := 4983230072969 + 3 ^ 40 * 403489 * 2
def baseEnd_403489 : Nat := 92081687023145369391953

theorem tailTrace_403489 : CollatzResearch.WordTrace tailWord_403489 prefixEnd_403489 92081687023145369391953 := by
  unfold tailWord_403489
  simp only [CollatzResearch.WordTrace]
  refine ⟨14716452835235738280069521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9810968556823825520046347 14716452835235738280069521)
  ·
    refine ⟨11037339626426803710052141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14716452835235738280069521 11037339626426803710052141)
    ·
      refine ⟨4139002359910051391269553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11037339626426803710052141 4139002359910051391269553)
      ·
        refine ⟨3104251769932538543452165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4139002359910051391269553 3104251769932538543452165)
        ·
          refine ⟨582047206862350976897281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3104251769932538543452165 582047206862350976897281)
          ·
            refine ⟨436535405146763232672961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582047206862350976897281 436535405146763232672961)
            ·
              refine ⟨327401553860072424504721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436535405146763232672961 327401553860072424504721)
              ·
                refine ⟨245551165395054318378541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327401553860072424504721 245551165395054318378541)
                ·
                  refine ⟨92081687023145369391953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245551165395054318378541 92081687023145369391953)
                  ·
                    rfl

theorem cell21_403489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 3].length) (baseStart_403489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403489 prefixEnd_403489 := by exact prefixLift 403489
  have htrace : WordTrace (prefixWord ++ tailWord_403489) baseStart_403489 baseEnd_403489 := by
    simpa [prefixWord, tailWord_403489, baseEnd_403489] using wordTrace_append hprefix tailTrace_403489
  have hstable : (prefixWord ++ tailWord_403489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403489).length < 2 ^ (prefixWord ++ tailWord_403489).sum := by decide
  have hdescent : baseEnd_403489 < baseStart_403489 := by decide
  rcases family_descends (prefixWord ++ tailWord_403489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403607 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 5]
def baseStart_403607 : Nat := 118140960795 + 403607 * 2 ^ 59
def prefixEnd_403607 : Nat := 4983230072969 + 3 ^ 40 * 403607 * 2
def baseEnd_403607 : Nat := 92108616230803386425045

theorem tailTrace_403607 : CollatzResearch.WordTrace tailWord_403607 prefixEnd_403607 92108616230803386425045 := by
  unfold tailWord_403607
  simp only [CollatzResearch.WordTrace]
  refine ⟨14720756648808244432865075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9813837765872162955243383 14720756648808244432865075)
  ·
    refine ⟨22081134973212366649297613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14720756648808244432865075 22081134973212366649297613)
    ·
      refine ⟨8280425614954637493486605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22081134973212366649297613 8280425614954637493486605)
      ·
        refine ⟨3105159605607989060057477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8280425614954637493486605 3105159605607989060057477)
        ·
          refine ⟨582217426051497948760777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3105159605607989060057477 582217426051497948760777)
          ·
            refine ⟨436663069538623461570583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582217426051497948760777 436663069538623461570583)
            ·
              refine ⟨654994604307935192355875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436663069538623461570583 654994604307935192355875)
              ·
                refine ⟨982491906461902788533813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654994604307935192355875 982491906461902788533813)
                ·
                  refine ⟨92108616230803386425045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 982491906461902788533813 92108616230803386425045)
                  ·
                    rfl

theorem cell21_403607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 5].length) (baseStart_403607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403607 prefixEnd_403607 := by exact prefixLift 403607
  have htrace : WordTrace (prefixWord ++ tailWord_403607) baseStart_403607 baseEnd_403607 := by
    simpa [prefixWord, tailWord_403607, baseEnd_403607] using wordTrace_append hprefix tailTrace_403607
  have hstable : (prefixWord ++ tailWord_403607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403607).length < 2 ^ (prefixWord ++ tailWord_403607).sum := by decide
  have hdescent : baseEnd_403607 < baseStart_403607 := by decide
  rcases family_descends (prefixWord ++ tailWord_403607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403669 : List Nat := [1, 3, 2, 4, 3, 1, 1, 6]
def baseStart_403669 : Nat := 118140960795 + 403669 * 2 ^ 59
def prefixEnd_403669 : Nat := 4983230072969 + 3 ^ 40 * 403669 * 2
def baseEnd_403669 : Nat := 30707588491835018797195

theorem tailTrace_403669 : CollatzResearch.WordTrace tailWord_403669 prefixEnd_403669 30707588491835018797195 := by
  unfold tailWord_403669
  simp only [CollatzResearch.WordTrace]
  refine ⟨14723017974583629021622061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9815345316389086014414707 14723017974583629021622061)
  ·
    refine ⟨5521131740468860883108273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14723017974583629021622061 5521131740468860883108273)
    ·
      refine ⟨4140848805351645662331205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5521131740468860883108273 4140848805351645662331205)
      ·
        refine ⟨776409151003433561687101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4140848805351645662331205 776409151003433561687101)
        ·
          refine ⟨291153431626287585632663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 776409151003433561687101 291153431626287585632663)
          ·
            refine ⟨436730147439431378448995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291153431626287585632663 436730147439431378448995)
            ·
              refine ⟨655095221159147067673493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436730147439431378448995 655095221159147067673493)
              ·
                refine ⟨30707588491835018797195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 655095221159147067673493 30707588491835018797195)
                ·
                  rfl

theorem cell21_403669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 6].length) (baseStart_403669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403669 prefixEnd_403669 := by exact prefixLift 403669
  have htrace : WordTrace (prefixWord ++ tailWord_403669) baseStart_403669 baseEnd_403669 := by
    simpa [prefixWord, tailWord_403669, baseEnd_403669] using wordTrace_append hprefix tailTrace_403669
  have hstable : (prefixWord ++ tailWord_403669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403669).length < 2 ^ (prefixWord ++ tailWord_403669).sum := by decide
  have hdescent : baseEnd_403669 < baseStart_403669 := by decide
  rcases family_descends (prefixWord ++ tailWord_403669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403680 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 4]
def baseStart_403680 : Nat := 118140960795 + 403680 * 2 ^ 59
def prefixEnd_403680 : Nat := 4983230072969 + 3 ^ 40 * 403680 * 2
def baseEnd_403680 : Nat := 92125275825371481708229

theorem tailTrace_403680 : CollatzResearch.WordTrace tailWord_403680 prefixEnd_403680 92125275825371481708229 := by
  unfold tailWord_403680
  simp only [CollatzResearch.WordTrace]
  refine ⟨7361709588771888950136247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9815612785029185266848329 7361709588771888950136247)
  ·
    refine ⟨11042564383157833425204371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7361709588771888950136247 11042564383157833425204371)
    ·
      refine ⟨16563846574736750137806557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11042564383157833425204371 16563846574736750137806557)
      ·
        refine ⟨6211442465526281301677459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16563846574736750137806557 6211442465526281301677459)
        ·
          refine ⟨9317163698289421952516189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6211442465526281301677459 9317163698289421952516189)
          ·
            refine ⟨3493936386858533232193571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9317163698289421952516189 3493936386858533232193571)
            ·
              refine ⟨5240904580287799848290357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493936386858533232193571 5240904580287799848290357)
              ·
                refine ⟨491334804401981235777221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5240904580287799848290357 491334804401981235777221)
                ·
                  refine ⟨92125275825371481708229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 491334804401981235777221 92125275825371481708229)
                  ·
                    rfl

theorem cell21_403680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_403680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403680 prefixEnd_403680 := by exact prefixLift 403680
  have htrace : WordTrace (prefixWord ++ tailWord_403680) baseStart_403680 baseEnd_403680 := by
    simpa [prefixWord, tailWord_403680, baseEnd_403680] using wordTrace_append hprefix tailTrace_403680
  have hstable : (prefixWord ++ tailWord_403680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403680).length < 2 ^ (prefixWord ++ tailWord_403680).sum := by decide
  have hdescent : baseEnd_403680 < baseStart_403680 := by decide
  rcases family_descends (prefixWord ++ tailWord_403680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403683 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 5]
def baseStart_403683 : Nat := 118140960795 + 403683 * 2 ^ 59
def prefixEnd_403683 : Nat := 4983230072969 + 3 ^ 40 * 403683 * 2
def baseEnd_403683 : Nat := 92125960466244143158223

theorem tailTrace_403683 : CollatzResearch.WordTrace tailWord_403683 prefixEnd_403683 92125960466244143158223 := by
  unfold tailWord_403683
  simp only [CollatzResearch.WordTrace]
  refine ⟨14723528596532909412631703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9815685731021939608421135 14723528596532909412631703)
  ·
    refine ⟨22085292894799364118947555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14723528596532909412631703 22085292894799364118947555)
    ·
      refine ⟨33127939342199046178421333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22085292894799364118947555 33127939342199046178421333)
      ·
        refine ⟨388218039166395072403375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 33127939342199046178421333 388218039166395072403375)
        ·
          refine ⟨582327058749592608605063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388218039166395072403375 582327058749592608605063)
          ·
            refine ⟨873490588124388912907595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582327058749592608605063 873490588124388912907595)
            ·
              refine ⟨1310235882186583369361393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873490588124388912907595 1310235882186583369361393)
              ·
                refine ⟨982676911639937527021045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310235882186583369361393 982676911639937527021045)
                ·
                  refine ⟨92125960466244143158223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 982676911639937527021045 92125960466244143158223)
                  ·
                    rfl

theorem cell21_403683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 5].length) (baseStart_403683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403683 prefixEnd_403683 := by exact prefixLift 403683
  have htrace : WordTrace (prefixWord ++ tailWord_403683) baseStart_403683 baseEnd_403683 := by
    simpa [prefixWord, tailWord_403683, baseEnd_403683] using wordTrace_append hprefix tailTrace_403683
  have hstable : (prefixWord ++ tailWord_403683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403683).length < 2 ^ (prefixWord ++ tailWord_403683).sum := by decide
  have hdescent : baseEnd_403683 < baseStart_403683 := by decide
  rcases family_descends (prefixWord ++ tailWord_403683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403714 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_403714 : Nat := 118140960795 + 403714 * 2 ^ 59
def prefixEnd_403714 : Nat := 4983230072969 + 3 ^ 40 * 403714 * 2
def baseEnd_403714 : Nat := 92133035088594978141493

theorem tailTrace_403714 : CollatzResearch.WordTrace tailWord_403714 prefixEnd_403714 92133035088594978141493 := by
  unfold tailWord_403714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681164814855150426752549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9816439506280401138006797 3681164814855150426752549)
  ·
    refine ⟨690218402785340705016103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3681164814855150426752549 690218402785340705016103)
    ·
      refine ⟨1035327604178011057524155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 690218402785340705016103 1035327604178011057524155)
      ·
        refine ⟨1552991406267016586286233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035327604178011057524155 1552991406267016586286233)
        ·
          refine ⟨1164743554700262439714675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552991406267016586286233 1164743554700262439714675)
          ·
            refine ⟨1747115332050393659572013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164743554700262439714675 1747115332050393659572013)
            ·
              refine ⟨655168249518897622339505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1747115332050393659572013 655168249518897622339505)
              ·
                refine ⟨491376187139173216754629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655168249518897622339505 491376187139173216754629)
                ·
                  refine ⟨92133035088594978141493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 491376187139173216754629 92133035088594978141493)
                  ·
                    rfl

theorem cell21_403714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_403714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403714 prefixEnd_403714 := by exact prefixLift 403714
  have htrace : WordTrace (prefixWord ++ tailWord_403714) baseStart_403714 baseEnd_403714 := by
    simpa [prefixWord, tailWord_403714, baseEnd_403714] using wordTrace_append hprefix tailTrace_403714
  have hstable : (prefixWord ++ tailWord_403714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403714).length < 2 ^ (prefixWord ++ tailWord_403714).sum := by decide
  have hdescent : baseEnd_403714 < baseStart_403714 := by decide
  rcases family_descends (prefixWord ++ tailWord_403714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403751 : List Nat := [1, 1, 8, 1, 2, 1, 1, 3, 3]
def baseStart_403751 : Nat := 118140960795 + 403751 * 2 ^ 59
def prefixEnd_403751 : Nat := 4983230072969 + 3 ^ 40 * 403751 * 2
def baseEnd_403751 : Nat := 92141478992691136024751

theorem tailTrace_403751 : CollatzResearch.WordTrace tailWord_403751 prefixEnd_403751 92141478992691136024751 := by
  unfold tailWord_403751
  simp only [CollatzResearch.WordTrace]
  refine ⟨14726008760286557026107107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9817339173524371350738071 14726008760286557026107107)
  ·
    refine ⟨22089013140429835539160661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14726008760286557026107107 22089013140429835539160661)
    ·
      refine ⟨258855622739412135224539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 22089013140429835539160661 258855622739412135224539)
      ·
        refine ⟨388283434109118202836809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258855622739412135224539 388283434109118202836809)
        ·
          refine ⟨291212575581838652127607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388283434109118202836809 291212575581838652127607)
          ·
            refine ⟨436818863372757978191411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291212575581838652127607 436818863372757978191411)
            ·
              refine ⟨655228295059136967287117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436818863372757978191411 655228295059136967287117)
              ·
                refine ⟨245710610647176362732669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 655228295059136967287117 245710610647176362732669)
                ·
                  refine ⟨92141478992691136024751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245710610647176362732669 92141478992691136024751)
                  ·
                    rfl

theorem cell21_403751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 3].length) (baseStart_403751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403751 prefixEnd_403751 := by exact prefixLift 403751
  have htrace : WordTrace (prefixWord ++ tailWord_403751) baseStart_403751 baseEnd_403751 := by
    simpa [prefixWord, tailWord_403751, baseEnd_403751] using wordTrace_append hprefix tailTrace_403751
  have hstable : (prefixWord ++ tailWord_403751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403751).length < 2 ^ (prefixWord ++ tailWord_403751).sum := by decide
  have hdescent : baseEnd_403751 < baseStart_403751 := by decide
  rcases family_descends (prefixWord ++ tailWord_403751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403770 : List Nat := [3, 1, 1, 1, 4, 2, 9]
def baseStart_403770 : Nat := 118140960795 + 403770 * 2 ^ 59
def prefixEnd_403770 : Nat := 4983230072969 + 3 ^ 40 * 403770 * 2
def baseEnd_403770 : Nat := 10238423894616813912005

theorem tailTrace_403770 : CollatzResearch.WordTrace tailWord_403770 prefixEnd_403770 10238423894616813912005 := by
  unfold tailWord_403770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681675436804430817762191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9817801164811815514032509 3681675436804430817762191)
  ·
    refine ⟨5522513155206646226643287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3681675436804430817762191 5522513155206646226643287)
    ·
      refine ⟨8283769732809969339964931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5522513155206646226643287 8283769732809969339964931)
      ·
        refine ⟨12425654599214954009947397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8283769732809969339964931 12425654599214954009947397)
        ·
          refine ⟨2329810237352803876865137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12425654599214954009947397 2329810237352803876865137)
          ·
            refine ⟨1747357678014602907648853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2329810237352803876865137 1747357678014602907648853)
            ·
              refine ⟨10238423894616813912005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1747357678014602907648853 10238423894616813912005)
              ·
                rfl

theorem cell21_403770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 9].length) (baseStart_403770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403770 prefixEnd_403770 := by exact prefixLift 403770
  have htrace : WordTrace (prefixWord ++ tailWord_403770) baseStart_403770 baseEnd_403770 := by
    simpa [prefixWord, tailWord_403770, baseEnd_403770] using wordTrace_append hprefix tailTrace_403770
  have hstable : (prefixWord ++ tailWord_403770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403770).length < 2 ^ (prefixWord ++ tailWord_403770).sum := by decide
  have hdescent : baseEnd_403770 < baseStart_403770 := by decide
  rcases family_descends (prefixWord ++ tailWord_403770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403835 : List Nat := [1, 1, 1, 1, 1, 7, 4, 2, 3]
def baseStart_403835 : Nat := 118140960795 + 403835 * 2 ^ 59
def prefixEnd_403835 : Nat := 4983230072969 + 3 ^ 40 * 403835 * 2
def baseEnd_403835 : Nat := 92160648937125656624579

theorem tailTrace_403835 : CollatzResearch.WordTrace tailWord_403835 prefixEnd_403835 92160648937125656624579 := by
  unfold tailWord_403835
  simp only [CollatzResearch.WordTrace]
  refine ⟨14729072491982239372164959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9819381661321492914776639 14729072491982239372164959)
  ·
    refine ⟨22093608737973359058247439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14729072491982239372164959 22093608737973359058247439)
    ·
      refine ⟨33140413106960038587371159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22093608737973359058247439 33140413106960038587371159)
      ·
        refine ⟨49710619660440057881056739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33140413106960038587371159 49710619660440057881056739)
        ·
          refine ⟨74565929490660086821585109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49710619660440057881056739 74565929490660086821585109)
          ·
            refine ⟨1747638972437345784880901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 74565929490660086821585109 1747638972437345784880901)
            ·
              refine ⟨327682307332002334665169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1747638972437345784880901 327682307332002334665169)
              ·
                refine ⟨245761730499001750998877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327682307332002334665169 245761730499001750998877)
                ·
                  refine ⟨92160648937125656624579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245761730499001750998877 92160648937125656624579)
                  ·
                    rfl

theorem cell21_403835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 3].length) (baseStart_403835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403835 prefixEnd_403835 := by exact prefixLift 403835
  have htrace : WordTrace (prefixWord ++ tailWord_403835) baseStart_403835 baseEnd_403835 := by
    simpa [prefixWord, tailWord_403835, baseEnd_403835] using wordTrace_append hprefix tailTrace_403835
  have hstable : (prefixWord ++ tailWord_403835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403835).length < 2 ^ (prefixWord ++ tailWord_403835).sum := by decide
  have hdescent : baseEnd_403835 < baseStart_403835 := by decide
  rcases family_descends (prefixWord ++ tailWord_403835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403939 : List Nat := [1, 1, 1, 6, 3, 2, 7]
def baseStart_403939 : Nat := 118140960795 + 403939 * 2 ^ 59
def prefixEnd_403939 : Nat := 4983230072969 + 3 ^ 40 * 403939 * 2
def baseEnd_403939 : Nat := 10242709239338287432337

theorem tailTrace_403939 : CollatzResearch.WordTrace tailWord_403939 prefixEnd_403939 10242709239338287432337 := by
  unfold tailWord_403939
  simp only [CollatzResearch.WordTrace]
  refine ⟨14732865683605465133950871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9821910455736976755967247 14732865683605465133950871)
  ·
    refine ⟨22099298525408197700926307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14732865683605465133950871 22099298525408197700926307)
    ·
      refine ⟨33148947788112296551389461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22099298525408197700926307 33148947788112296551389461)
      ·
        refine ⟨1553856927567763900846381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33148947788112296551389461 1553856927567763900846381)
        ·
          refine ⟨582696347837911462817393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1553856927567763900846381 582696347837911462817393)
          ·
            refine ⟨437022260878433597113045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582696347837911462817393 437022260878433597113045)
            ·
              refine ⟨10242709239338287432337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 437022260878433597113045 10242709239338287432337)
              ·
                rfl

theorem cell21_403939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 7].length) (baseStart_403939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_403939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_403939 prefixEnd_403939 := by exact prefixLift 403939
  have htrace : WordTrace (prefixWord ++ tailWord_403939) baseStart_403939 baseEnd_403939 := by
    simpa [prefixWord, tailWord_403939, baseEnd_403939] using wordTrace_append hprefix tailTrace_403939
  have hstable : (prefixWord ++ tailWord_403939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403939).length < 2 ^ (prefixWord ++ tailWord_403939).sum := by decide
  have hdescent : baseEnd_403939 < baseStart_403939 := by decide
  rcases family_descends (prefixWord ++ tailWord_403939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404004 : List Nat := [2, 3, 1, 5, 1, 1, 1, 4, 3]
def baseStart_404004 : Nat := 118140960795 + 404004 * 2 ^ 59
def prefixEnd_404004 : Nat := 4983230072969 + 3 ^ 40 * 404004 * 2
def baseEnd_404004 : Nat := 92199217039618918307567

theorem tailTrace_404004 : CollatzResearch.WordTrace tailWord_404004 prefixEnd_404004 92199217039618918307567 := by
  unfold tailWord_404004
  simp only [CollatzResearch.WordTrace]
  refine ⟨7367618214184990617533533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9823490952246654156711377 7367618214184990617533533)
  ·
    refine ⟨2762856830319371481575075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7367618214184990617533533 2762856830319371481575075)
    ·
      refine ⟨4144285245479057222362613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2762856830319371481575075 4144285245479057222362613)
      ·
        refine ⟨388526741763661614596495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4144285245479057222362613 388526741763661614596495)
        ·
          refine ⟨582790112645492421894743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388526741763661614596495 582790112645492421894743)
          ·
            refine ⟨874185168968238632842115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582790112645492421894743 874185168968238632842115)
            ·
              refine ⟨1311277753452357949263173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874185168968238632842115 1311277753452357949263173)
              ·
                refine ⟨245864578772317115486845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1311277753452357949263173 245864578772317115486845)
                ·
                  refine ⟨92199217039618918307567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245864578772317115486845 92199217039618918307567)
                  ·
                    rfl

theorem cell21_404004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_404004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404004 prefixEnd_404004 := by exact prefixLift 404004
  have htrace : WordTrace (prefixWord ++ tailWord_404004) baseStart_404004 baseEnd_404004 := by
    simpa [prefixWord, tailWord_404004, baseEnd_404004] using wordTrace_append hprefix tailTrace_404004
  have hstable : (prefixWord ++ tailWord_404004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404004).length < 2 ^ (prefixWord ++ tailWord_404004).sum := by decide
  have hdescent : baseEnd_404004 < baseStart_404004 := by decide
  rcases family_descends (prefixWord ++ tailWord_404004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404012 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_404012 : Nat := 118140960795 + 404012 * 2 ^ 59
def prefixEnd_404012 : Nat := 4983230072969 + 3 ^ 40 * 404012 * 2
def baseEnd_404012 : Nat := 92201042748612682174217

theorem tailTrace_404012 : CollatzResearch.WordTrace tailWord_404012 prefixEnd_404012 92201042748612682174217 := by
  unfold tailWord_404012
  simp only [CollatzResearch.WordTrace]
  refine ⟨7367764106170499300679145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9823685474893999067572193 7367764106170499300679145)
  ·
    refine ⟨5525823079627874475509359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7367764106170499300679145 5525823079627874475509359)
    ·
      refine ⟨8288734619441811713264039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5525823079627874475509359 8288734619441811713264039)
      ·
        refine ⟨12433101929162717569896059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8288734619441811713264039 12433101929162717569896059)
        ·
          refine ⟨18649652893744076354844089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12433101929162717569896059 18649652893744076354844089)
          ·
            refine ⟨13987239670308057266133067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18649652893744076354844089 13987239670308057266133067)
            ·
              refine ⟨20980859505462085899199601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13987239670308057266133067 20980859505462085899199601)
              ·
                refine ⟨15735644629096564424399701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20980859505462085899199601 15735644629096564424399701)
                ·
                  refine ⟨92201042748612682174217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15735644629096564424399701 92201042748612682174217)
                  ·
                    rfl

theorem cell21_404012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_404012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404012 prefixEnd_404012 := by exact prefixLift 404012
  have htrace : WordTrace (prefixWord ++ tailWord_404012) baseStart_404012 baseEnd_404012 := by
    simpa [prefixWord, tailWord_404012, baseEnd_404012] using wordTrace_append hprefix tailTrace_404012
  have hstable : (prefixWord ++ tailWord_404012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404012).length < 2 ^ (prefixWord ++ tailWord_404012).sum := by decide
  have hdescent : baseEnd_404012 < baseStart_404012 := by decide
  rcases family_descends (prefixWord ++ tailWord_404012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404029 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 7]
def baseStart_404029 : Nat := 118140960795 + 404029 * 2 ^ 59
def prefixEnd_404029 : Nat := 4983230072969 + 3 ^ 40 * 404029 * 2
def baseEnd_404029 : Nat := 92204922380224430390849

theorem tailTrace_404029 : CollatzResearch.WordTrace tailWord_404029 prefixEnd_404029 92204922380224430390849 := by
  unfold tailWord_404029
  simp only [CollatzResearch.WordTrace]
  refine ⟨14736148253279410504727141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9824098835519607003151427 14736148253279410504727141)
  ·
    refine ⟨2763027797489889469636339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14736148253279410504727141 2763027797489889469636339)
    ·
      refine ⟨4144541696234834204454509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2763027797489889469636339 4144541696234834204454509)
      ·
        refine ⟨1554203136088062826670441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4144541696234834204454509 1554203136088062826670441)
        ·
          refine ⟨1165652352066047120002831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1554203136088062826670441 1165652352066047120002831)
          ·
            refine ⟨1748478528099070680004247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165652352066047120002831 1748478528099070680004247)
            ·
              refine ⟨2622717792148606020006371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748478528099070680004247 2622717792148606020006371)
              ·
                refine ⟨3934076688222909030009557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622717792148606020006371 3934076688222909030009557)
                ·
                  refine ⟨92204922380224430390849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3934076688222909030009557 92204922380224430390849)
                  ·
                    rfl

theorem cell21_404029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_404029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404029 prefixEnd_404029 := by exact prefixLift 404029
  have htrace : WordTrace (prefixWord ++ tailWord_404029) baseStart_404029 baseEnd_404029 := by
    simpa [prefixWord, tailWord_404029, baseEnd_404029] using wordTrace_append hprefix tailTrace_404029
  have hstable : (prefixWord ++ tailWord_404029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404029).length < 2 ^ (prefixWord ++ tailWord_404029).sum := by decide
  have hdescent : baseEnd_404029 < baseStart_404029 := by decide
  rcases family_descends (prefixWord ++ tailWord_404029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404046 : List Nat := [4, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_404046 : Nat := 118140960795 + 404046 * 2 ^ 59
def prefixEnd_404046 : Nat := 4983230072969 + 3 ^ 40 * 404046 * 2
def baseEnd_404046 : Nat := 92208802011836178607481

theorem tailTrace_404046 : CollatzResearch.WordTrace tailWord_404046 prefixEnd_404046 92208802011836178607481 := by
  unfold tailWord_404046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1842096036777227801011999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9824512196145214938730661 1842096036777227801011999)
  ·
    refine ⟨2763144055165841701517999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1842096036777227801011999 2763144055165841701517999)
    ·
      refine ⟨4144716082748762552276999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2763144055165841701517999 4144716082748762552276999)
      ·
        refine ⟨6217074124123143828415499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144716082748762552276999 6217074124123143828415499)
        ·
          refine ⟨9325611186184715742623249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217074124123143828415499 9325611186184715742623249)
          ·
            refine ⟨6994208389638536806967437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9325611186184715742623249 6994208389638536806967437)
            ·
              refine ⟨2622828146114451302612789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6994208389638536806967437 2622828146114451302612789)
              ·
                refine ⟨245890138698229809619949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2622828146114451302612789 245890138698229809619949)
                ·
                  refine ⟨92208802011836178607481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 245890138698229809619949 92208802011836178607481)
                  ·
                    rfl

theorem cell21_404046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_404046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404046 prefixEnd_404046 := by exact prefixLift 404046
  have htrace : WordTrace (prefixWord ++ tailWord_404046) baseStart_404046 baseEnd_404046 := by
    simpa [prefixWord, tailWord_404046, baseEnd_404046] using wordTrace_append hprefix tailTrace_404046
  have hstable : (prefixWord ++ tailWord_404046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404046).length < 2 ^ (prefixWord ++ tailWord_404046).sum := by decide
  have hdescent : baseEnd_404046 < baseStart_404046 := by decide
  rcases family_descends (prefixWord ++ tailWord_404046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404074 : List Nat := [3, 1, 3, 2, 1, 1, 2, 8]
def baseStart_404074 : Nat := 118140960795 + 404074 * 2 ^ 59
def prefixEnd_404074 : Nat := 4983230072969 + 3 ^ 40 * 404074 * 2
def baseEnd_404074 : Nat := 30738397331104784046919

theorem tailTrace_404074 : CollatzResearch.WordTrace tailWord_404074 prefixEnd_404074 30738397331104784046919 := by
  unfold tailWord_404074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3684447384529095797528819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9825193025410922126743517 3684447384529095797528819)
  ·
    refine ⟨5526671076793643696293229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3684447384529095797528819 5526671076793643696293229)
    ·
      refine ⟨2072501653797616386109961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5526671076793643696293229 2072501653797616386109961)
      ·
        refine ⟨1554376240348212289582471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2072501653797616386109961 1554376240348212289582471)
        ·
          refine ⟨2331564360522318434373707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554376240348212289582471 2331564360522318434373707)
          ·
            refine ⟨3497346540783477651560561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331564360522318434373707 3497346540783477651560561)
            ·
              refine ⟨2623009905587608238670421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3497346540783477651560561 2623009905587608238670421)
              ·
                refine ⟨30738397331104784046919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2623009905587608238670421 30738397331104784046919)
                ·
                  rfl

theorem cell21_404074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_404074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404074 prefixEnd_404074 := by exact prefixLift 404074
  have htrace : WordTrace (prefixWord ++ tailWord_404074) baseStart_404074 baseEnd_404074 := by
    simpa [prefixWord, tailWord_404074, baseEnd_404074] using wordTrace_append hprefix tailTrace_404074
  have hstable : (prefixWord ++ tailWord_404074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404074).length < 2 ^ (prefixWord ++ tailWord_404074).sum := by decide
  have hdescent : baseEnd_404074 < baseStart_404074 := by decide
  rcases family_descends (prefixWord ++ tailWord_404074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404119 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 6]
def baseStart_404119 : Nat := 118140960795 + 404119 * 2 ^ 59
def prefixEnd_404119 : Nat := 4983230072969 + 3 ^ 40 * 404119 * 2
def baseEnd_404119 : Nat := 92225461606404273890665

theorem tailTrace_404119 : CollatzResearch.WordTrace tailWord_404119 prefixEnd_404119 92225461606404273890665 := by
  unfold tailWord_404119
  simp only [CollatzResearch.WordTrace]
  refine ⟨14739430822953355875503411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9826287215302237250335607 14739430822953355875503411)
  ·
    refine ⟨22109146234430033813255117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14739430822953355875503411 22109146234430033813255117)
    ·
      refine ⟨8290929837911262679970669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22109146234430033813255117 8290929837911262679970669)
      ·
        refine ⟨3109098689216723504989001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8290929837911262679970669 3109098689216723504989001)
        ·
          refine ⟨2331824016912542628741751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3109098689216723504989001 2331824016912542628741751)
          ·
            refine ⟨3497736025368813943112627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331824016912542628741751 3497736025368813943112627)
            ·
              refine ⟨5246604038053220914668941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497736025368813943112627 5246604038053220914668941)
              ·
                refine ⟨1967476514269957843000853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5246604038053220914668941 1967476514269957843000853)
                ·
                  refine ⟨92225461606404273890665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1967476514269957843000853 92225461606404273890665)
                  ·
                    rfl

theorem cell21_404119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_404119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404119 prefixEnd_404119 := by exact prefixLift 404119
  have htrace : WordTrace (prefixWord ++ tailWord_404119) baseStart_404119 baseEnd_404119 := by
    simpa [prefixWord, tailWord_404119, baseEnd_404119] using wordTrace_append hprefix tailTrace_404119
  have hstable : (prefixWord ++ tailWord_404119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404119).length < 2 ^ (prefixWord ++ tailWord_404119).sum := by decide
  have hdescent : baseEnd_404119 < baseStart_404119 := by decide
  rcases family_descends (prefixWord ++ tailWord_404119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404260 : List Nat := [2, 3, 1, 3, 3, 2, 2, 5]
def baseStart_404260 : Nat := 118140960795 + 404260 * 2 ^ 59
def prefixEnd_404260 : Nat := 4983230072969 + 3 ^ 40 * 404260 * 2
def baseEnd_404260 : Nat := 30752546575806454013459

theorem tailTrace_404260 : CollatzResearch.WordTrace tailWord_404260 prefixEnd_404260 30752546575806454013459 := by
  unfold tailWord_404260
  simp only [CollatzResearch.WordTrace]
  refine ⟨7372286757721268478193117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9829715676961691304257489 7372286757721268478193117)
  ·
    refine ⟨2764607534145475679322419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7372286757721268478193117 2764607534145475679322419)
    ·
      refine ⟨4146911301218213518983629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2764607534145475679322419 4146911301218213518983629)
      ·
        refine ⟨1555091737956830069618861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4146911301218213518983629 1555091737956830069618861)
        ·
          refine ⟨583159401733811276107073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1555091737956830069618861 583159401733811276107073)
          ·
            refine ⟨437369551300358457080305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583159401733811276107073 437369551300358457080305)
            ·
              refine ⟨328027163475268842810229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437369551300358457080305 328027163475268842810229)
              ·
                refine ⟨30752546575806454013459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 328027163475268842810229 30752546575806454013459)
                ·
                  rfl

theorem cell21_404260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_404260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404260 prefixEnd_404260 := by exact prefixLift 404260
  have htrace : WordTrace (prefixWord ++ tailWord_404260) baseStart_404260 baseEnd_404260 := by
    simpa [prefixWord, tailWord_404260, baseEnd_404260] using wordTrace_append hprefix tailTrace_404260
  have hstable : (prefixWord ++ tailWord_404260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404260).length < 2 ^ (prefixWord ++ tailWord_404260).sum := by decide
  have hdescent : baseEnd_404260 < baseStart_404260 := by decide
  rcases family_descends (prefixWord ++ tailWord_404260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404347 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 4]
def baseStart_404347 : Nat := 118140960795 + 404347 * 2 ^ 59
def prefixEnd_404347 : Nat := 4983230072969 + 3 ^ 40 * 404347 * 2
def baseEnd_404347 : Nat := 92277494312726544090199

theorem tailTrace_404347 : CollatzResearch.WordTrace tailWord_404347 prefixEnd_404347 92277494312726544090199 := by
  unfold tailWord_404347
  simp only [CollatzResearch.WordTrace]
  refine ⟨14747746666127350814803295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9831831110751567209868863 14747746666127350814803295)
  ·
    refine ⟨22121619999191026222204943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14747746666127350814803295 22121619999191026222204943)
    ·
      refine ⟨33182429998786539333307415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22121619999191026222204943 33182429998786539333307415)
      ·
        refine ⟨49773644998179808999961123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33182429998786539333307415 49773644998179808999961123)
        ·
          refine ⟨74660467497269713499941685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49773644998179808999961123 74660467497269713499941685)
          ·
            refine ⟨6999418827869035640619533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74660467497269713499941685 6999418827869035640619533)
            ·
              refine ⟨2624782060450888365232325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6999418827869035640619533 2624782060450888365232325)
              ·
                refine ⟨492146636334541568481061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2624782060450888365232325 492146636334541568481061)
                ·
                  refine ⟨92277494312726544090199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492146636334541568481061 92277494312726544090199)
                  ·
                    rfl

theorem cell21_404347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 4].length) (baseStart_404347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404347 prefixEnd_404347 := by exact prefixLift 404347
  have htrace : WordTrace (prefixWord ++ tailWord_404347) baseStart_404347 baseEnd_404347 := by
    simpa [prefixWord, tailWord_404347, baseEnd_404347] using wordTrace_append hprefix tailTrace_404347
  have hstable : (prefixWord ++ tailWord_404347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404347).length < 2 ^ (prefixWord ++ tailWord_404347).sum := by decide
  have hdescent : baseEnd_404347 < baseStart_404347 := by decide
  rcases family_descends (prefixWord ++ tailWord_404347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404409 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 5]
def baseStart_404409 : Nat := 118140960795 + 404409 * 2 ^ 59
def prefixEnd_404409 : Nat := 4983230072969 + 3 ^ 40 * 404409 * 2
def baseEnd_404409 : Nat := 92291643557428214056739

theorem tailTrace_404409 : CollatzResearch.WordTrace tailWord_404409 prefixEnd_404409 92291643557428214056739 := by
  unfold tailWord_404409
  simp only [CollatzResearch.WordTrace]
  refine ⟨14750007991902735403560281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9833338661268490269040187 14750007991902735403560281)
  ·
    refine ⟨11062505993927051552670211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14750007991902735403560281 11062505993927051552670211)
    ·
      refine ⟨16593758990890577329005317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11062505993927051552670211 16593758990890577329005317)
      ·
        refine ⟨3111329810791983249188497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16593758990890577329005317 3111329810791983249188497)
        ·
          refine ⟨2333497358093987436891373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3111329810791983249188497 2333497358093987436891373)
          ·
            refine ⟨875061509285245288834265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2333497358093987436891373 875061509285245288834265)
            ·
              refine ⟨656296131963933966625699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875061509285245288834265 656296131963933966625699)
              ·
                refine ⟨984444197945900949938549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656296131963933966625699 984444197945900949938549)
                ·
                  refine ⟨92291643557428214056739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 984444197945900949938549 92291643557428214056739)
                  ·
                    rfl

theorem cell21_404409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_404409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404409 prefixEnd_404409 := by exact prefixLift 404409
  have htrace : WordTrace (prefixWord ++ tailWord_404409) baseStart_404409 baseEnd_404409 := by
    simpa [prefixWord, tailWord_404409, baseEnd_404409] using wordTrace_append hprefix tailTrace_404409
  have hstable : (prefixWord ++ tailWord_404409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404409).length < 2 ^ (prefixWord ++ tailWord_404409).sum := by decide
  have hdescent : baseEnd_404409 < baseStart_404409 := by decide
  rcases family_descends (prefixWord ++ tailWord_404409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404423 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 4]
def baseStart_404423 : Nat := 118140960795 + 404423 * 2 ^ 59
def prefixEnd_404423 : Nat := 4983230072969 + 3 ^ 40 * 404423 * 2
def baseEnd_404423 : Nat := 92294838548167300823377

theorem tailTrace_404423 : CollatzResearch.WordTrace tailWord_404423 prefixEnd_404423 92294838548167300823377 := by
  unfold tailWord_404423
  simp only [CollatzResearch.WordTrace]
  refine ⟨14750518613852015794569923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9833679075901343863046615 14750518613852015794569923)
  ·
    refine ⟨22125777920778023691854885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14750518613852015794569923 22125777920778023691854885)
    ·
      refine ⟨4148583360145879442222791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22125777920778023691854885 4148583360145879442222791)
      ·
        refine ⟨6222875040218819163334187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4148583360145879442222791 6222875040218819163334187)
        ·
          refine ⟨9334312560328228745001281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6222875040218819163334187 9334312560328228745001281)
          ·
            refine ⟨7000734420246171558750961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9334312560328228745001281 7000734420246171558750961)
            ·
              refine ⟨5250550815184628669063221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7000734420246171558750961 5250550815184628669063221)
              ·
                refine ⟨492239138923558937724677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5250550815184628669063221 492239138923558937724677)
                ·
                  refine ⟨92294838548167300823377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492239138923558937724677 92294838548167300823377)
                  ·
                    rfl

theorem cell21_404423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 4].length) (baseStart_404423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404423 prefixEnd_404423 := by exact prefixLift 404423
  have htrace : WordTrace (prefixWord ++ tailWord_404423) baseStart_404423 baseEnd_404423 := by
    simpa [prefixWord, tailWord_404423, baseEnd_404423] using wordTrace_append hprefix tailTrace_404423
  have hstable : (prefixWord ++ tailWord_404423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404423).length < 2 ^ (prefixWord ++ tailWord_404423).sum := by decide
  have hdescent : baseEnd_404423 < baseStart_404423 := by decide
  rcases family_descends (prefixWord ++ tailWord_404423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404429 : List Nat := [1, 6, 3, 1, 1, 1, 1, 7]
def baseStart_404429 : Nat := 118140960795 + 404429 * 2 ^ 59
def prefixEnd_404429 : Nat := 4983230072969 + 3 ^ 40 * 404429 * 2
def baseEnd_404429 : Nat := 30765402609970874574455

theorem tailTrace_404429 : CollatzResearch.WordTrace tailWord_404429 prefixEnd_404429 30765402609970874574455 := by
  unfold tailWord_404429
  simp only [CollatzResearch.WordTrace]
  refine ⟨14750737451830278819288341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9833824967886852546192227 14750737451830278819288341)
  ·
    refine ⟨691440818054544319654141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14750737451830278819288341 691440818054544319654141)
    ·
      refine ⟨259290306770454119870303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 691440818054544319654141 259290306770454119870303)
      ·
        refine ⟨388935460155681179805455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259290306770454119870303 388935460155681179805455)
        ·
          refine ⟨583403190233521769708183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388935460155681179805455 583403190233521769708183)
          ·
            refine ⟨875104785350282654562275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583403190233521769708183 875104785350282654562275)
            ·
              refine ⟨1312657178025423981843413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875104785350282654562275 1312657178025423981843413)
              ·
                refine ⟨30765402609970874574455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1312657178025423981843413 30765402609970874574455)
                ·
                  rfl

theorem cell21_404429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 7].length) (baseStart_404429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404429 prefixEnd_404429 := by exact prefixLift 404429
  have htrace : WordTrace (prefixWord ++ tailWord_404429) baseStart_404429 baseEnd_404429 := by
    simpa [prefixWord, tailWord_404429, baseEnd_404429] using wordTrace_append hprefix tailTrace_404429
  have hstable : (prefixWord ++ tailWord_404429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404429).length < 2 ^ (prefixWord ++ tailWord_404429).sum := by decide
  have hdescent : baseEnd_404429 < baseStart_404429 := by decide
  rcases family_descends (prefixWord ++ tailWord_404429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404513 : List Nat := [1, 2, 3, 2, 3, 10]
def baseStart_404513 : Nat := 118140960795 + 404513 * 2 ^ 59
def prefixEnd_404513 : Nat := 4983230072969 + 3 ^ 40 * 404513 * 2
def baseEnd_404513 : Nat := 3419088065716560900859

theorem tailTrace_404513 : CollatzResearch.WordTrace tailWord_404513 prefixEnd_404513 3419088065716560900859 := by
  unfold tailWord_404513
  simp only [CollatzResearch.WordTrace]
  refine ⟨14753801183525961165346193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9835867455683974110230795 14753801183525961165346193)
  ·
    refine ⟨11065350887644470874009645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14753801183525961165346193 11065350887644470874009645)
    ·
      refine ⟨4149506582866676577753617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11065350887644470874009645 4149506582866676577753617)
      ·
        refine ⟨3112129937150007433315213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4149506582866676577753617 3112129937150007433315213)
        ·
          refine ⟨1167048726431252787493205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3112129937150007433315213 1167048726431252787493205)
          ·
            refine ⟨3419088065716560900859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1167048726431252787493205 3419088065716560900859)
            ·
              rfl

theorem cell21_404513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 10].length) (baseStart_404513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404513 prefixEnd_404513 := by exact prefixLift 404513
  have htrace : WordTrace (prefixWord ++ tailWord_404513) baseStart_404513 baseEnd_404513 := by
    simpa [prefixWord, tailWord_404513, baseEnd_404513] using wordTrace_append hprefix tailTrace_404513
  have hstable : (prefixWord ++ tailWord_404513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404513).length < 2 ^ (prefixWord ++ tailWord_404513).sum := by decide
  have hdescent : baseEnd_404513 < baseStart_404513 := by decide
  rcases family_descends (prefixWord ++ tailWord_404513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404516 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 4]
def baseStart_404516 : Nat := 118140960795 + 404516 * 2 ^ 59
def prefixEnd_404516 : Nat := 4983230072969 + 3 ^ 40 * 404516 * 2
def baseEnd_404516 : Nat := 92316062415219805773187

theorem tailTrace_404516 : CollatzResearch.WordTrace tailWord_404516 prefixEnd_404516 92316062415219805773187 := by
  unfold tailWord_404516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7376955301257546338852701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9835940401676728451803601 7376955301257546338852701)
  ·
    refine ⟨2766358237971579877069763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7376955301257546338852701 2766358237971579877069763)
    ·
      refine ⟨4149537356957369815604645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2766358237971579877069763 4149537356957369815604645)
      ·
        refine ⟨778038254429506840425871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4149537356957369815604645 778038254429506840425871)
        ·
          refine ⟨1167057381644260260638807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778038254429506840425871 1167057381644260260638807)
          ·
            refine ⟨1750586072466390390958211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167057381644260260638807 1750586072466390390958211)
            ·
              refine ⟨2625879108699585586437317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750586072466390390958211 2625879108699585586437317)
              ·
                refine ⟨492352332881172297456997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2625879108699585586437317 492352332881172297456997)
                ·
                  refine ⟨92316062415219805773187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492352332881172297456997 92316062415219805773187)
                  ·
                    rfl

theorem cell21_404516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_404516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404516 prefixEnd_404516 := by exact prefixLift 404516
  have htrace : WordTrace (prefixWord ++ tailWord_404516) baseStart_404516 baseEnd_404516 := by
    simpa [prefixWord, tailWord_404516, baseEnd_404516] using wordTrace_append hprefix tailTrace_404516
  have hstable : (prefixWord ++ tailWord_404516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404516).length < 2 ^ (prefixWord ++ tailWord_404516).sum := by decide
  have hdescent : baseEnd_404516 < baseStart_404516 := by decide
  rcases family_descends (prefixWord ++ tailWord_404516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404519 : List Nat := [1, 1, 7, 1, 1, 2, 1, 4, 3]
def baseStart_404519 : Nat := 118140960795 + 404519 * 2 ^ 59
def prefixEnd_404519 : Nat := 4983230072969 + 3 ^ 40 * 404519 * 2
def baseEnd_404519 : Nat := 92316747056092467223181

theorem tailTrace_404519 : CollatzResearch.WordTrace tailWord_404519 prefixEnd_404519 92316747056092467223181 := by
  unfold tailWord_404519
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754020021504224190064611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9836013347669482793376407 14754020021504224190064611)
  ·
    refine ⟨22131030032256336285096917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14754020021504224190064611 22131030032256336285096917)
    ·
      refine ⟨518696016381007881681959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22131030032256336285096917 518696016381007881681959)
      ·
        refine ⟨778044024571511822522939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518696016381007881681959 778044024571511822522939)
        ·
          refine ⟨1167066036857267733784409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778044024571511822522939 1167066036857267733784409)
          ·
            refine ⟨875299527642950800338307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167066036857267733784409 875299527642950800338307)
            ·
              refine ⟨1312949291464426200507461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875299527642950800338307 1312949291464426200507461)
              ·
                refine ⟨246177992149579912595149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1312949291464426200507461 246177992149579912595149)
                ·
                  refine ⟨92316747056092467223181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246177992149579912595149 92316747056092467223181)
                  ·
                    rfl

theorem cell21_404519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 3].length) (baseStart_404519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404519 prefixEnd_404519 := by exact prefixLift 404519
  have htrace : WordTrace (prefixWord ++ tailWord_404519) baseStart_404519 baseEnd_404519 := by
    simpa [prefixWord, tailWord_404519, baseEnd_404519] using wordTrace_append hprefix tailTrace_404519
  have hstable : (prefixWord ++ tailWord_404519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404519).length < 2 ^ (prefixWord ++ tailWord_404519).sum := by decide
  have hdescent : baseEnd_404519 < baseStart_404519 := by decide
  rcases family_descends (prefixWord ++ tailWord_404519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404544 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_404544 : Nat := 118140960795 + 404544 * 2 ^ 59
def prefixEnd_404544 : Nat := 4983230072969 + 3 ^ 40 * 404544 * 2
def baseEnd_404544 : Nat := 92322452396697979306463

theorem tailTrace_404544 : CollatzResearch.WordTrace tailWord_404544 prefixEnd_404544 92322452396697979306463 := by
  unfold tailWord_404544
  simp only [CollatzResearch.WordTrace]
  refine ⟨7377465923206826729862343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9836621230942435639816457 7377465923206826729862343)
  ·
    refine ⟨11066198884810240094793515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7377465923206826729862343 11066198884810240094793515)
    ·
      refine ⟨16599298327215360142190273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11066198884810240094793515 16599298327215360142190273)
      ·
        refine ⟨12449473745411520106642705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16599298327215360142190273 12449473745411520106642705)
        ·
          refine ⟨9337105309058640079982029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12449473745411520106642705 9337105309058640079982029)
          ·
            refine ⟨3501414490896990029993261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9337105309058640079982029 3501414490896990029993261)
            ·
              refine ⟨1313030434086371261247473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3501414490896990029993261 1313030434086371261247473)
              ·
                refine ⟨984772825564778445935605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1313030434086371261247473 984772825564778445935605)
                ·
                  refine ⟨92322452396697979306463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 984772825564778445935605 92322452396697979306463)
                  ·
                    rfl

theorem cell21_404544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_404544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404544 prefixEnd_404544 := by exact prefixLift 404544
  have htrace : WordTrace (prefixWord ++ tailWord_404544) baseStart_404544 baseEnd_404544 := by
    simpa [prefixWord, tailWord_404544, baseEnd_404544] using wordTrace_append hprefix tailTrace_404544
  have hstable : (prefixWord ++ tailWord_404544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404544).length < 2 ^ (prefixWord ++ tailWord_404544).sum := by decide
  have hdescent : baseEnd_404544 < baseStart_404544 := by decide
  rcases family_descends (prefixWord ++ tailWord_404544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404561 : List Nat := [1, 2, 2, 1, 3, 1, 3, 5, 3]
def baseStart_404561 : Nat := 118140960795 + 404561 * 2 ^ 59
def prefixEnd_404561 : Nat := 4983230072969 + 3 ^ 40 * 404561 * 2
def baseEnd_404561 : Nat := 92326332028309727523095

theorem tailTrace_404561 : CollatzResearch.WordTrace tailWord_404561 prefixEnd_404561 92326332028309727523095 := by
  unfold tailWord_404561
  simp only [CollatzResearch.WordTrace]
  refine ⟨14755551887352065363093537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9837034591568043575395691 14755551887352065363093537)
  ·
    refine ⟨11066663915514049022320153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14755551887352065363093537 11066663915514049022320153)
    ·
      refine ⟨8299997936635536766740115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11066663915514049022320153 8299997936635536766740115)
      ·
        refine ⟨12449996904953305150110173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8299997936635536766740115 12449996904953305150110173)
        ·
          refine ⟨4668748839357489431291315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12449996904953305150110173 4668748839357489431291315)
          ·
            refine ⟨7003123259036234146936973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668748839357489431291315 7003123259036234146936973)
            ·
              refine ⟨2626171222138587805101365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7003123259036234146936973 2626171222138587805101365)
              ·
                refine ⟨246203552075492606728253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2626171222138587805101365 246203552075492606728253)
                ·
                  refine ⟨92326332028309727523095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246203552075492606728253 92326332028309727523095)
                  ·
                    rfl

theorem cell21_404561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 3].length) (baseStart_404561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404561 prefixEnd_404561 := by exact prefixLift 404561
  have htrace : WordTrace (prefixWord ++ tailWord_404561) baseStart_404561 baseEnd_404561 := by
    simpa [prefixWord, tailWord_404561, baseEnd_404561] using wordTrace_append hprefix tailTrace_404561
  have hstable : (prefixWord ++ tailWord_404561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404561).length < 2 ^ (prefixWord ++ tailWord_404561).sum := by decide
  have hdescent : baseEnd_404561 < baseStart_404561 := by decide
  rcases family_descends (prefixWord ++ tailWord_404561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404578 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_404578 : Nat := 118140960795 + 404578 * 2 ^ 59
def prefixEnd_404578 : Nat := 4983230072969 + 3 ^ 40 * 404578 * 2
def baseEnd_404578 : Nat := 92330211659921475739727

theorem tailTrace_404578 : CollatzResearch.WordTrace tailWord_404578 prefixEnd_404578 92330211659921475739727 := by
  unfold tailWord_404578
  simp only [CollatzResearch.WordTrace]
  refine ⟨3689042982072619316615597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9837447952193651510974925 3689042982072619316615597)
  ·
    refine ⟨1383391118277232243730849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3689042982072619316615597 1383391118277232243730849)
    ·
      refine ⟨1037543338707924182798137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1383391118277232243730849 1037543338707924182798137)
      ·
        refine ⟨778157504030943137098603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1037543338707924182798137 778157504030943137098603)
        ·
          refine ⟨1167236256046414705647905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 778157504030943137098603 1167236256046414705647905)
          ·
            refine ⟨875427192034811029235929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167236256046414705647905 875427192034811029235929)
            ·
              refine ⟨656570394026108271926947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875427192034811029235929 656570394026108271926947)
              ·
                refine ⟨984855591039162407890421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656570394026108271926947 984855591039162407890421)
                ·
                  refine ⟨92330211659921475739727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 984855591039162407890421 92330211659921475739727)
                  ·
                    rfl

theorem cell21_404578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_404578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404578 prefixEnd_404578 := by exact prefixLift 404578
  have htrace : WordTrace (prefixWord ++ tailWord_404578) baseStart_404578 baseEnd_404578 := by
    simpa [prefixWord, tailWord_404578, baseEnd_404578] using wordTrace_append hprefix tailTrace_404578
  have hstable : (prefixWord ++ tailWord_404578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404578).length < 2 ^ (prefixWord ++ tailWord_404578).sum := by decide
  have hdescent : baseEnd_404578 < baseStart_404578 := by decide
  rcases family_descends (prefixWord ++ tailWord_404578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404592 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 4]
def baseStart_404592 : Nat := 118140960795 + 404592 * 2 ^ 59
def prefixEnd_404592 : Nat := 4983230072969 + 3 ^ 40 * 404592 * 2
def baseEnd_404592 : Nat := 92333406650660562506365

theorem tailTrace_404592 : CollatzResearch.WordTrace tailWord_404592 prefixEnd_404592 92333406650660562506365 := by
  unfold tailWord_404592
  simp only [CollatzResearch.WordTrace]
  refine ⟨7378341275119878828736015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9837788366826505104981353 7378341275119878828736015)
  ·
    refine ⟨11067511912679818243104023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7378341275119878828736015 11067511912679818243104023)
    ·
      refine ⟨16601267869019727364656035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11067511912679818243104023 16601267869019727364656035)
      ·
        refine ⟨24901901803529591046984053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16601267869019727364656035 24901901803529591046984053)
        ·
          refine ⟨2334553294080899160654755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24901901803529591046984053 2334553294080899160654755)
          ·
            refine ⟨3501829941121348740982133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334553294080899160654755 3501829941121348740982133)
            ·
              refine ⟨328296556980126444467075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3501829941121348740982133 328296556980126444467075)
              ·
                refine ⟨492444835470189666700613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328296556980126444467075 492444835470189666700613)
                ·
                  refine ⟨92333406650660562506365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 492444835470189666700613 92333406650660562506365)
                  ·
                    rfl

theorem cell21_404592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_404592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404592 prefixEnd_404592 := by exact prefixLift 404592
  have htrace : WordTrace (prefixWord ++ tailWord_404592) baseStart_404592 baseEnd_404592 := by
    simpa [prefixWord, tailWord_404592, baseEnd_404592] using wordTrace_append hprefix tailTrace_404592
  have hstable : (prefixWord ++ tailWord_404592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404592).length < 2 ^ (prefixWord ++ tailWord_404592).sum := by decide
  have hdescent : baseEnd_404592 < baseStart_404592 := by decide
  rcases family_descends (prefixWord ++ tailWord_404592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404665 : List Nat := [1, 2, 1, 4, 1, 3, 2, 7]
def baseStart_404665 : Nat := 118140960795 + 404665 * 2 ^ 59
def prefixEnd_404665 : Nat := 4983230072969 + 3 ^ 40 * 404665 * 2
def baseEnd_404665 : Nat := 30783355415076219263183

theorem tailTrace_404665 : CollatzResearch.WordTrace tailWord_404665 prefixEnd_404665 30783355415076219263183 := by
  unfold tailWord_404665
  simp only [CollatzResearch.WordTrace]
  refine ⟨14759345078975291124879449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9839563385983527416586299 14759345078975291124879449)
  ·
    refine ⟨11069508809231468343659587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14759345078975291124879449 11069508809231468343659587)
    ·
      refine ⟨16604263213847202515489381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11069508809231468343659587 16604263213847202515489381)
      ·
        refine ⟨3113299352596350471654259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16604263213847202515489381 3113299352596350471654259)
        ·
          refine ⟨4669949028894525707481389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113299352596350471654259 4669949028894525707481389)
          ·
            refine ⟨1751230885835447140305521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4669949028894525707481389 1751230885835447140305521)
            ·
              refine ⟨1313423164376585355229141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1751230885835447140305521 1313423164376585355229141)
              ·
                refine ⟨30783355415076219263183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1313423164376585355229141 30783355415076219263183)
                ·
                  rfl

theorem cell21_404665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 7].length) (baseStart_404665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404665 prefixEnd_404665 := by exact prefixLift 404665
  have htrace : WordTrace (prefixWord ++ tailWord_404665) baseStart_404665 baseEnd_404665 := by
    simpa [prefixWord, tailWord_404665, baseEnd_404665] using wordTrace_append hprefix tailTrace_404665
  have hstable : (prefixWord ++ tailWord_404665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404665).length < 2 ^ (prefixWord ++ tailWord_404665).sum := by decide
  have hdescent : baseEnd_404665 < baseStart_404665 := by decide
  rcases family_descends (prefixWord ++ tailWord_404665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404772 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_404772 : Nat := 118140960795 + 404772 * 2 ^ 59
def prefixEnd_404772 : Nat := 4983230072969 + 3 ^ 40 * 404772 * 2
def baseEnd_404772 : Nat := 92374485103020249505997

theorem tailTrace_404772 : CollatzResearch.WordTrace tailWord_404772 prefixEnd_404772 92374485103020249505997 := by
  unfold tailWord_404772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7381623844793824199512285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9842165126391765599349713 7381623844793824199512285)
  ·
    refine ⟨2768108941797684074817107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7381623844793824199512285 2768108941797684074817107)
    ·
      refine ⟨4152163412696526112225661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2768108941797684074817107 4152163412696526112225661)
      ·
        refine ⟨1557061279761197292084623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4152163412696526112225661 1557061279761197292084623)
        ·
          refine ⟨2335591919641795938126935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557061279761197292084623 2335591919641795938126935)
          ·
            refine ⟨3503387879462693907190403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335591919641795938126935 3503387879462693907190403)
            ·
              refine ⟨5255081819194040860785605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503387879462693907190403 5255081819194040860785605)
              ·
                refine ⟨985327841098882661397301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5255081819194040860785605 985327841098882661397301)
                ·
                  refine ⟨92374485103020249505997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 985327841098882661397301 92374485103020249505997)
                  ·
                    rfl

theorem cell21_404772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_404772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404772 prefixEnd_404772 := by exact prefixLift 404772
  have htrace : WordTrace (prefixWord ++ tailWord_404772) baseStart_404772 baseEnd_404772 := by
    simpa [prefixWord, tailWord_404772, baseEnd_404772] using wordTrace_append hprefix tailTrace_404772
  have hstable : (prefixWord ++ tailWord_404772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404772).length < 2 ^ (prefixWord ++ tailWord_404772).sum := by decide
  have hdescent : baseEnd_404772 < baseStart_404772 := by decide
  rcases family_descends (prefixWord ++ tailWord_404772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404817 : List Nat := [1, 2, 2, 1, 4, 1, 4, 6]
def baseStart_404817 : Nat := 118140960795 + 404817 * 2 ^ 59
def prefixEnd_404817 : Nat := 4983230072969 + 3 ^ 40 * 404817 * 2
def baseEnd_404817 : Nat := 30794918238703390418635

theorem tailTrace_404817 : CollatzResearch.WordTrace tailWord_404817 prefixEnd_404817 30794918238703390418635 := by
  unfold tailWord_404817
  simp only [CollatzResearch.WordTrace]
  refine ⟨14764888974424621084412705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9843259316283080722941803 14764888974424621084412705)
  ·
    refine ⟨11073666730818465813309529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14764888974424621084412705 11073666730818465813309529)
    ·
      refine ⟨8305250048113849359982147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11073666730818465813309529 8305250048113849359982147)
      ·
        refine ⟨12457875072170774039973221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8305250048113849359982147 12457875072170774039973221)
        ·
          refine ⟨2335851576032020132494979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12457875072170774039973221 2335851576032020132494979)
          ·
            refine ⟨3503777364048030198742469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335851576032020132494979 3503777364048030198742469)
            ·
              refine ⟨656958255759005662264213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3503777364048030198742469 656958255759005662264213)
              ·
                refine ⟨30794918238703390418635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 656958255759005662264213 30794918238703390418635)
                ·
                  rfl

theorem cell21_404817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 6].length) (baseStart_404817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404817 prefixEnd_404817 := by exact prefixLift 404817
  have htrace : WordTrace (prefixWord ++ tailWord_404817) baseStart_404817 baseEnd_404817 := by
    simpa [prefixWord, tailWord_404817, baseEnd_404817] using wordTrace_append hprefix tailTrace_404817
  have hstable : (prefixWord ++ tailWord_404817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404817).length < 2 ^ (prefixWord ++ tailWord_404817).sum := by decide
  have hdescent : baseEnd_404817 < baseStart_404817 := by decide
  rcases family_descends (prefixWord ++ tailWord_404817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404831 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 7]
def baseStart_404831 : Nat := 118140960795 + 404831 * 2 ^ 59
def prefixEnd_404831 : Nat := 4983230072969 + 3 ^ 40 * 404831 * 2
def baseEnd_404831 : Nat := 92387949706849258022543

theorem tailTrace_404831 : CollatzResearch.WordTrace tailWord_404831 prefixEnd_404831 92387949706849258022543 := by
  unfold tailWord_404831
  simp only [CollatzResearch.WordTrace]
  refine ⟨14765399596373901475422347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9843599730915934316948231 14765399596373901475422347)
  ·
    refine ⟨22148099394560852213133521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14765399596373901475422347 22148099394560852213133521)
    ·
      refine ⟨16611074545920639159850141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22148099394560852213133521 16611074545920639159850141)
      ·
        refine ⟨6229152954720239684943803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16611074545920639159850141 6229152954720239684943803)
        ·
          refine ⟨9343729432080359527415705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229152954720239684943803 9343729432080359527415705)
          ·
            refine ⟨7007797074060269645561779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9343729432080359527415705 7007797074060269645561779)
            ·
              refine ⟨10511695611090404468342669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7007797074060269645561779 10511695611090404468342669)
              ·
                refine ⟨3941885854158901675628501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10511695611090404468342669 3941885854158901675628501)
                ·
                  refine ⟨92387949706849258022543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3941885854158901675628501 92387949706849258022543)
                  ·
                    rfl

theorem cell21_404831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_404831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404831 prefixEnd_404831 := by exact prefixLift 404831
  have htrace : WordTrace (prefixWord ++ tailWord_404831) baseStart_404831 baseEnd_404831 := by
    simpa [prefixWord, tailWord_404831, baseEnd_404831] using wordTrace_append hprefix tailTrace_404831
  have hstable : (prefixWord ++ tailWord_404831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404831).length < 2 ^ (prefixWord ++ tailWord_404831).sum := by decide
  have hdescent : baseEnd_404831 < baseStart_404831 := by decide
  rcases family_descends (prefixWord ++ tailWord_404831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404882 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_404882 : Nat := 118140960795 + 404882 * 2 ^ 59
def prefixEnd_404882 : Nat := 4983230072969 + 3 ^ 40 * 404882 * 2
def baseEnd_404882 : Nat := 92399588601684502672439

theorem tailTrace_404882 : CollatzResearch.WordTrace tailWord_404882 prefixEnd_404882 92399588601684502672439 := by
  unfold tailWord_404882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3691814929797284296382225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9844839812792758123685933 3691814929797284296382225)
  ·
    refine ⟨2768861197347963222286669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3691814929797284296382225 2768861197347963222286669)
    ·
      refine ⟨1038322949005486208357501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2768861197347963222286669 1038322949005486208357501)
      ·
        refine ⟨389371105877057328134063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1038322949005486208357501 389371105877057328134063)
        ·
          refine ⟨584056658815585992201095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389371105877057328134063 584056658815585992201095)
          ·
            refine ⟨876084988223378988301643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584056658815585992201095 876084988223378988301643)
            ·
              refine ⟨1314127482335068482452465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876084988223378988301643 1314127482335068482452465)
              ·
                refine ⟨985595611751301361839349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314127482335068482452465 985595611751301361839349)
                ·
                  refine ⟨92399588601684502672439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 985595611751301361839349 92399588601684502672439)
                  ·
                    rfl

theorem cell21_404882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_404882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404882 prefixEnd_404882 := by exact prefixLift 404882
  have htrace : WordTrace (prefixWord ++ tailWord_404882) baseStart_404882 baseEnd_404882 := by
    simpa [prefixWord, tailWord_404882, baseEnd_404882] using wordTrace_append hprefix tailTrace_404882
  have hstable : (prefixWord ++ tailWord_404882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404882).length < 2 ^ (prefixWord ++ tailWord_404882).sum := by decide
  have hdescent : baseEnd_404882 < baseStart_404882 := by decide
  rcases family_descends (prefixWord ++ tailWord_404882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404983 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 5]
def baseStart_404983 : Nat := 118140960795 + 404983 * 2 ^ 59
def prefixEnd_404983 : Nat := 4983230072969 + 3 ^ 40 * 404983 * 2
def baseEnd_404983 : Nat := 92422638177730771488899

theorem tailTrace_404983 : CollatzResearch.WordTrace tailWord_404983 prefixEnd_404983 92422638177730771488899 := by
  unfold tailWord_404983
  simp only [CollatzResearch.WordTrace]
  refine ⟨14770943491823231434955603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9847295661215487623303735 14770943491823231434955603)
  ·
    refine ⟨22156415237734847152433405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14770943491823231434955603 22156415237734847152433405)
    ·
      refine ⟨8308655714150567682162527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22156415237734847152433405 8308655714150567682162527)
      ·
        refine ⟨12462983571225851523243791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8308655714150567682162527 12462983571225851523243791)
        ·
          refine ⟨18694475356838777284865687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12462983571225851523243791 18694475356838777284865687)
          ·
            refine ⟨28041713035258165927298531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18694475356838777284865687 28041713035258165927298531)
            ·
              refine ⟨42062569552887248890947797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28041713035258165927298531 42062569552887248890947797)
              ·
                refine ⟨985841473895794895881589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42062569552887248890947797 985841473895794895881589)
                ·
                  refine ⟨92422638177730771488899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 985841473895794895881589 92422638177730771488899)
                  ·
                    rfl

theorem cell21_404983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_404983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_404983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_404983 prefixEnd_404983 := by exact prefixLift 404983
  have htrace : WordTrace (prefixWord ++ tailWord_404983) baseStart_404983 baseEnd_404983 := by
    simpa [prefixWord, tailWord_404983, baseEnd_404983] using wordTrace_append hprefix tailTrace_404983
  have hstable : (prefixWord ++ tailWord_404983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404983).length < 2 ^ (prefixWord ++ tailWord_404983).sum := by decide
  have hdescent : baseEnd_404983 < baseStart_404983 := by decide
  rcases family_descends (prefixWord ++ tailWord_404983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405028 : List Nat := [2, 3, 1, 15]
def baseStart_405028 : Nat := 118140960795 + 405028 * 2 ^ 59
def prefixEnd_405028 : Nat := 4983230072969 + 3 ^ 40 * 405028 * 2
def baseEnd_405028 : Nat := 380382336587739478349

theorem tailTrace_405028 : CollatzResearch.WordTrace tailWord_405028 prefixEnd_405028 380382336587739478349 := by
  unfold tailWord_405028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7386292388330102060171869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9848389851106802746895825 7386292388330102060171869)
  ·
    refine ⟨2769859645623788272564451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7386292388330102060171869 2769859645623788272564451)
    ·
      refine ⟨4154789468435682408846677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769859645623788272564451 4154789468435682408846677)
      ·
        refine ⟨380382336587739478349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 4154789468435682408846677 380382336587739478349)
        ·
          rfl

theorem cell21_405028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 15].length) (baseStart_405028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405028 prefixEnd_405028 := by exact prefixLift 405028
  have htrace : WordTrace (prefixWord ++ tailWord_405028) baseStart_405028 baseEnd_405028 := by
    simpa [prefixWord, tailWord_405028, baseEnd_405028] using wordTrace_append hprefix tailTrace_405028
  have hstable : (prefixWord ++ tailWord_405028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405028).length < 2 ^ (prefixWord ++ tailWord_405028).sum := by decide
  have hdescent : baseEnd_405028 < baseStart_405028 := by decide
  rcases family_descends (prefixWord ++ tailWord_405028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405045 : List Nat := [1, 3, 3, 1, 1, 3, 3, 6]
def baseStart_405045 : Nat := 118140960795 + 405045 * 2 ^ 59
def prefixEnd_405045 : Nat := 4983230072969 + 3 ^ 40 * 405045 * 2
def baseEnd_405045 : Nat := 30812262474144147151813

theorem tailTrace_405045 : CollatzResearch.WordTrace tailWord_405045 prefixEnd_405045 30812262474144147151813 := by
  unfold tailWord_405045
  simp only [CollatzResearch.WordTrace]
  refine ⟨14773204817598616023712589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9848803211732410682475059 14773204817598616023712589)
  ·
    refine ⟨5539951806599481008892221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14773204817598616023712589 5539951806599481008892221)
    ·
      refine ⟨2077481927474805378334583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5539951806599481008892221 2077481927474805378334583)
      ·
        refine ⟨3116222891212208067501875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2077481927474805378334583 3116222891212208067501875)
        ·
          refine ⟨4674334336818312101252813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116222891212208067501875 4674334336818312101252813)
          ·
            refine ⟨1752875376306867037969805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4674334336818312101252813 1752875376306867037969805)
            ·
              refine ⟨657328266115075139238677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1752875376306867037969805 657328266115075139238677)
              ·
                refine ⟨30812262474144147151813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 657328266115075139238677 30812262474144147151813)
                ·
                  rfl

theorem cell21_405045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 6].length) (baseStart_405045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405045 prefixEnd_405045 := by exact prefixLift 405045
  have htrace : WordTrace (prefixWord ++ tailWord_405045) baseStart_405045 baseEnd_405045 := by
    simpa [prefixWord, tailWord_405045, baseEnd_405045] using wordTrace_append hprefix tailTrace_405045
  have hstable : (prefixWord ++ tailWord_405045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405045).length < 2 ^ (prefixWord ++ tailWord_405045).sum := by decide
  have hdescent : baseEnd_405045 < baseStart_405045 := by decide
  rcases family_descends (prefixWord ++ tailWord_405045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405093 : List Nat := [1, 3, 1, 3, 3, 1, 2, 4, 3]
def baseStart_405093 : Nat := 118140960795 + 405093 * 2 ^ 59
def prefixEnd_405093 : Nat := 4983230072969 + 3 ^ 40 * 405093 * 2
def baseEnd_405093 : Nat := 92447741676395024655341

theorem tailTrace_405093 : CollatzResearch.WordTrace tailWord_405093 prefixEnd_405093 92447741676395024655341 := by
  unfold tailWord_405093
  simp only [CollatzResearch.WordTrace]
  refine ⟨14774955521424720221459933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9849970347616480147639955 14774955521424720221459933)
  ·
    refine ⟨5540608320534270083047475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14774955521424720221459933 5540608320534270083047475)
    ·
      refine ⟨8310912480801405124571213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5540608320534270083047475 8310912480801405124571213)
      ·
        refine ⟨3116592180300526921714205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8310912480801405124571213 3116592180300526921714205)
        ·
          refine ⟨1168722067612697595642827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3116592180300526921714205 1168722067612697595642827)
          ·
            refine ⟨1753083101419046393464241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168722067612697595642827 1753083101419046393464241)
            ·
              refine ⟨1314812326064284795098181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753083101419046393464241 1314812326064284795098181)
              ·
                refine ⟨246527311137053399080909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1314812326064284795098181 246527311137053399080909)
                ·
                  refine ⟨92447741676395024655341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246527311137053399080909 92447741676395024655341)
                  ·
                    rfl

theorem cell21_405093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_405093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405093 prefixEnd_405093 := by exact prefixLift 405093
  have htrace : WordTrace (prefixWord ++ tailWord_405093) baseStart_405093 baseEnd_405093 := by
    simpa [prefixWord, tailWord_405093, baseEnd_405093] using wordTrace_append hprefix tailTrace_405093
  have hstable : (prefixWord ++ tailWord_405093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405093).length < 2 ^ (prefixWord ++ tailWord_405093).sum := by decide
  have hdescent : baseEnd_405093 < baseStart_405093 := by decide
  rcases family_descends (prefixWord ++ tailWord_405093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405121 : List Nat := [1, 2, 4, 2, 1, 3, 1, 7]
def baseStart_405121 : Nat := 118140960795 + 405121 * 2 ^ 59
def prefixEnd_405121 : Nat := 4983230072969 + 3 ^ 40 * 405121 * 2
def baseEnd_405121 : Nat := 30818043885957732729539

theorem tailTrace_405121 : CollatzResearch.WordTrace tailWord_405121 prefixEnd_405121 30818043885957732729539 := by
  unfold tailWord_405121
  simp only [CollatzResearch.WordTrace]
  refine ⟨14775976765323281003479217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9850651176882187335652811 14775976765323281003479217)
  ·
    refine ⟨11081982573992460752609413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14775976765323281003479217 11081982573992460752609413)
    ·
      refine ⟨2077871732623586391114265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11081982573992460752609413 2077871732623586391114265)
      ·
        refine ⟨1558403799467689793335699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2077871732623586391114265 1558403799467689793335699)
        ·
          refine ⟨2337605699201534690003549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558403799467689793335699 2337605699201534690003549)
          ·
            refine ⟨876602137200575508751331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2337605699201534690003549 876602137200575508751331)
            ·
              refine ⟨1314903205800863263126997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876602137200575508751331 1314903205800863263126997)
              ·
                refine ⟨30818043885957732729539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1314903205800863263126997 30818043885957732729539)
                ·
                  rfl

theorem cell21_405121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 7].length) (baseStart_405121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405121 prefixEnd_405121 := by exact prefixLift 405121
  have htrace : WordTrace (prefixWord ++ tailWord_405121) baseStart_405121 baseEnd_405121 := by
    simpa [prefixWord, tailWord_405121, baseEnd_405121] using wordTrace_append hprefix tailTrace_405121
  have hstable : (prefixWord ++ tailWord_405121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405121).length < 2 ^ (prefixWord ++ tailWord_405121).sum := by decide
  have hdescent : baseEnd_405121 < baseStart_405121 := by decide
  rcases family_descends (prefixWord ++ tailWord_405121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405138 : List Nat := [3, 2, 3, 1, 3, 2, 7]
def baseStart_405138 : Nat := 118140960795 + 405138 * 2 ^ 59
def prefixEnd_405138 : Nat := 4983230072969 + 3 ^ 40 * 405138 * 2
def baseEnd_405138 : Nat := 10273112365498327378361

theorem tailTrace_405138 : CollatzResearch.WordTrace tailWord_405138 prefixEnd_405138 10273112365498327378361 := by
  unfold tailWord_405138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3694149201565423226712017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9851064537507795271232045 3694149201565423226712017)
  ·
    refine ⟨2770611901174067420034013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3694149201565423226712017 2770611901174067420034013)
    ·
      refine ⟨1038979462940275282512755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2770611901174067420034013 1038979462940275282512755)
      ·
        refine ⟨1558469194410412923769133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038979462940275282512755 1558469194410412923769133)
        ·
          refine ⟨584425947903904846413425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1558469194410412923769133 584425947903904846413425)
          ·
            refine ⟨438319460927928634810069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584425947903904846413425 438319460927928634810069)
            ·
              refine ⟨10273112365498327378361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 438319460927928634810069 10273112365498327378361)
              ·
                rfl

theorem cell21_405138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 7].length) (baseStart_405138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405138 prefixEnd_405138 := by exact prefixLift 405138
  have htrace : WordTrace (prefixWord ++ tailWord_405138) baseStart_405138 baseEnd_405138 := by
    simpa [prefixWord, tailWord_405138, baseEnd_405138] using wordTrace_append hprefix tailTrace_405138
  have hstable : (prefixWord ++ tailWord_405138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405138).length < 2 ^ (prefixWord ++ tailWord_405138).sum := by decide
  have hdescent : baseEnd_405138 < baseStart_405138 := by decide
  rcases family_descends (prefixWord ++ tailWord_405138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405152 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 5]
def baseStart_405152 : Nat := 118140960795 + 405152 * 2 ^ 59
def prefixEnd_405152 : Nat := 4983230072969 + 3 ^ 40 * 405152 * 2
def baseEnd_405152 : Nat := 92461206280224033171887

theorem tailTrace_405152 : CollatzResearch.WordTrace tailWord_405152 prefixEnd_405152 92461206280224033171887 := by
  unfold tailWord_405152
  simp only [CollatzResearch.WordTrace]
  refine ⟨7388553714105486648928855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9851404952140648865238473 7388553714105486648928855)
  ·
    refine ⟨11082830571158229973393283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7388553714105486648928855 11082830571158229973393283)
    ·
      refine ⟨16624245856737344960089925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11082830571158229973393283 16624245856737344960089925)
      ·
        refine ⟨3117046098138252180016861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16624245856737344960089925 3117046098138252180016861)
        ·
          refine ⟨1168892286801844567506323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3117046098138252180016861 1168892286801844567506323)
          ·
            refine ⟨1753338430202766851259485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168892286801844567506323 1753338430202766851259485)
            ·
              refine ⟨657501911326037569222307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1753338430202766851259485 657501911326037569222307)
              ·
                refine ⟨986252866989056353833461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657501911326037569222307 986252866989056353833461)
                ·
                  refine ⟨92461206280224033171887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 986252866989056353833461 92461206280224033171887)
                  ·
                    rfl

theorem cell21_405152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_405152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405152 prefixEnd_405152 := by exact prefixLift 405152
  have htrace : WordTrace (prefixWord ++ tailWord_405152) baseStart_405152 baseEnd_405152 := by
    simpa [prefixWord, tailWord_405152, baseEnd_405152] using wordTrace_append hprefix tailTrace_405152
  have hstable : (prefixWord ++ tailWord_405152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405152).length < 2 ^ (prefixWord ++ tailWord_405152).sum := by decide
  have hdescent : baseEnd_405152 < baseStart_405152 := by decide
  rcases family_descends (prefixWord ++ tailWord_405152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405225 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 8]
def baseStart_405225 : Nat := 118140960795 + 405225 * 2 ^ 59
def prefixEnd_405225 : Nat := 4983230072969 + 3 ^ 40 * 405225 * 2
def baseEnd_405225 : Nat := 92477865874792128455071

theorem tailTrace_405225 : CollatzResearch.WordTrace tailWord_405225 prefixEnd_405225 92477865874792128455071 := by
  unfold tailWord_405225
  simp only [CollatzResearch.WordTrace]
  refine ⟨14779769956946506765265129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9853179971297671176843419 14779769956946506765265129)
  ·
    refine ⟨11084827467709880073948847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14779769956946506765265129 11084827467709880073948847)
    ·
      refine ⟨16627241201564820110923271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11084827467709880073948847 16627241201564820110923271)
      ·
        refine ⟨24940861802347230166384907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16627241201564820110923271 24940861802347230166384907)
        ·
          refine ⟨37411292703520845249577361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24940861802347230166384907 37411292703520845249577361)
          ·
            refine ⟨28058469527640633937183021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37411292703520845249577361 28058469527640633937183021)
            ·
              refine ⟨10521926072865237726443633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28058469527640633937183021 10521926072865237726443633)
              ·
                refine ⟨7891444554648928294832725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10521926072865237726443633 7891444554648928294832725)
                ·
                  refine ⟨92477865874792128455071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7891444554648928294832725 92477865874792128455071)
                  ·
                    rfl

theorem cell21_405225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_405225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405225 prefixEnd_405225 := by exact prefixLift 405225
  have htrace : WordTrace (prefixWord ++ tailWord_405225) baseStart_405225 baseEnd_405225 := by
    simpa [prefixWord, tailWord_405225, baseEnd_405225] using wordTrace_append hprefix tailTrace_405225
  have hstable : (prefixWord ++ tailWord_405225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405225).length < 2 ^ (prefixWord ++ tailWord_405225).sum := by decide
  have hdescent : baseEnd_405225 < baseStart_405225 := by decide
  rcases family_descends (prefixWord ++ tailWord_405225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405256 : List Nat := [2, 1, 3, 2, 2, 1, 10]
def baseStart_405256 : Nat := 118140960795 + 405256 * 2 ^ 59
def prefixEnd_405256 : Nat := 4983230072969 + 3 ^ 40 * 405256 * 2
def baseEnd_405256 : Nat := 10276104499682551493149

theorem tailTrace_405256 : CollatzResearch.WordTrace tailWord_405256 prefixEnd_405256 10276104499682551493149 := by
  unfold tailWord_405256
  simp only [CollatzResearch.WordTrace]
  refine ⟨7390450309917099529821811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9853933746556132706429081 7390450309917099529821811)
  ·
    refine ⟨11085675464875649294732717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7390450309917099529821811 11085675464875649294732717)
    ·
      refine ⟨4157128299328368485524769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11085675464875649294732717 4157128299328368485524769)
      ·
        refine ⟨3117846224496276364143577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4157128299328368485524769 3117846224496276364143577)
        ·
          refine ⟨2338384668372207273107683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3117846224496276364143577 2338384668372207273107683)
          ·
            refine ⟨3507577002558310909661525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338384668372207273107683 3507577002558310909661525)
            ·
              refine ⟨10276104499682551493149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3507577002558310909661525 10276104499682551493149)
              ·
                rfl

theorem cell21_405256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 10].length) (baseStart_405256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405256 prefixEnd_405256 := by exact prefixLift 405256
  have htrace : WordTrace (prefixWord ++ tailWord_405256) baseStart_405256 baseEnd_405256 := by
    simpa [prefixWord, tailWord_405256, baseEnd_405256] using wordTrace_append hprefix tailTrace_405256
  have hstable : (prefixWord ++ tailWord_405256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405256).length < 2 ^ (prefixWord ++ tailWord_405256).sum := by decide
  have hdescent : baseEnd_405256 < baseStart_405256 := by decide
  rcases family_descends (prefixWord ++ tailWord_405256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405321 : List Nat := [1, 2, 1, 1, 2, 4, 5, 2, 3]
def baseStart_405321 : Nat := 118140960795 + 405321 * 2 ^ 59
def prefixEnd_405321 : Nat := 4983230072969 + 3 ^ 40 * 405321 * 2
def baseEnd_405321 : Nat := 92499774382717294854875

theorem tailTrace_405321 : CollatzResearch.WordTrace tailWord_405321 prefixEnd_405321 92499774382717294854875 := by
  unfold tailWord_405321
  simp only [CollatzResearch.WordTrace]
  refine ⟨14783271364598715160759817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9855514243065810107173211 14783271364598715160759817)
  ·
    refine ⟨11087453523449036370569863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14783271364598715160759817 11087453523449036370569863)
    ·
      refine ⟨16631180285173554555854795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11087453523449036370569863 16631180285173554555854795)
      ·
        refine ⟨24946770427760331833782193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16631180285173554555854795 24946770427760331833782193)
        ·
          refine ⟨18710077820820248875336645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24946770427760331833782193 18710077820820248875336645)
          ·
            refine ⟨3508139591403796664125621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18710077820820248875336645 3508139591403796664125621)
            ·
              refine ⟨328888086694105937261777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3508139591403796664125621 328888086694105937261777)
              ·
                refine ⟨246666065020579452946333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328888086694105937261777 246666065020579452946333)
                ·
                  refine ⟨92499774382717294854875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246666065020579452946333 92499774382717294854875)
                  ·
                    rfl

theorem cell21_405321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 3].length) (baseStart_405321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405321 prefixEnd_405321 := by exact prefixLift 405321
  have htrace : WordTrace (prefixWord ++ tailWord_405321) baseStart_405321 baseEnd_405321 := by
    simpa [prefixWord, tailWord_405321, baseEnd_405321] using wordTrace_append hprefix tailTrace_405321
  have hstable : (prefixWord ++ tailWord_405321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405321).length < 2 ^ (prefixWord ++ tailWord_405321).sum := by decide
  have hdescent : baseEnd_405321 < baseStart_405321 := by decide
  rcases family_descends (prefixWord ++ tailWord_405321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405335 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 4]
def baseStart_405335 : Nat := 118140960795 + 405335 * 2 ^ 59
def prefixEnd_405335 : Nat := 4983230072969 + 3 ^ 40 * 405335 * 2
def baseEnd_405335 : Nat := 92502969373456381621513

theorem tailTrace_405335 : CollatzResearch.WordTrace tailWord_405335 prefixEnd_405335 92502969373456381621513 := by
  unfold tailWord_405335
  simp only [CollatzResearch.WordTrace]
  refine ⟨14783781986547995551769459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9855854657698663701179639 14783781986547995551769459)
  ·
    refine ⟨22175672979821993327654189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14783781986547995551769459 22175672979821993327654189)
    ·
      refine ⟨8315877367433247497870321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22175672979821993327654189 8315877367433247497870321)
      ·
        refine ⟨6236908025574935623402741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8315877367433247497870321 6236908025574935623402741)
        ·
          refine ⟨584710127397650214694007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6236908025574935623402741 584710127397650214694007)
          ·
            refine ⟨877065191096475322041011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584710127397650214694007 877065191096475322041011)
            ·
              refine ⟨1315597786644712983061517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877065191096475322041011 1315597786644712983061517)
              ·
                refine ⟨493349169991767368648069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1315597786644712983061517 493349169991767368648069)
                ·
                  refine ⟨92502969373456381621513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 493349169991767368648069 92502969373456381621513)
                  ·
                    rfl

theorem cell21_405335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 4].length) (baseStart_405335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405335 prefixEnd_405335 := by exact prefixLift 405335
  have htrace : WordTrace (prefixWord ++ tailWord_405335) baseStart_405335 baseEnd_405335 := by
    simpa [prefixWord, tailWord_405335, baseEnd_405335] using wordTrace_append hprefix tailTrace_405335
  have hstable : (prefixWord ++ tailWord_405335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405335).length < 2 ^ (prefixWord ++ tailWord_405335).sum := by decide
  have hdescent : baseEnd_405335 < baseStart_405335 := by decide
  rcases family_descends (prefixWord ++ tailWord_405335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405366 : List Nat := [5, 1, 1, 3, 3, 8]
def baseStart_405366 : Nat := 118140960795 + 405366 * 2 ^ 59
def prefixEnd_405366 : Nat := 4983230072969 + 3 ^ 40 * 405366 * 2
def baseEnd_405366 : Nat := 3426297925770637652029

theorem tailTrace_405366 : CollatzResearch.WordTrace tailWord_405366 prefixEnd_405366 3426297925770637652029 := by
  unfold tailWord_405366
  simp only [CollatzResearch.WordTrace]
  refine ⟨924057040589730490384247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9856608432957125230765301 924057040589730490384247)
  ·
    refine ⟨1386085560884595735576371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 924057040589730490384247 1386085560884595735576371)
    ·
      refine ⟨2079128341326893603364557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1386085560884595735576371 2079128341326893603364557)
      ·
        refine ⟨779673127997585101261709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2079128341326893603364557 779673127997585101261709)
        ·
          refine ⟨292377422999094412973141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 779673127997585101261709 292377422999094412973141)
          ·
            refine ⟨3426297925770637652029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 292377422999094412973141 3426297925770637652029)
            ·
              rfl

theorem cell21_405366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 8].length) (baseStart_405366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405366 prefixEnd_405366 := by exact prefixLift 405366
  have htrace : WordTrace (prefixWord ++ tailWord_405366) baseStart_405366 baseEnd_405366 := by
    simpa [prefixWord, tailWord_405366, baseEnd_405366] using wordTrace_append hprefix tailTrace_405366
  have hstable : (prefixWord ++ tailWord_405366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405366).length < 2 ^ (prefixWord ++ tailWord_405366).sum := by decide
  have hdescent : baseEnd_405366 < baseStart_405366 := by decide
  rcases family_descends (prefixWord ++ tailWord_405366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405428 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 6]
def baseStart_405428 : Nat := 118140960795 + 405428 * 2 ^ 59
def prefixEnd_405428 : Nat := 4983230072969 + 3 ^ 40 * 405428 * 2
def baseEnd_405428 : Nat := 92524193240508886571323

theorem tailTrace_405428 : CollatzResearch.WordTrace tailWord_405428 prefixEnd_405428 92524193240508886571323 := by
  unfold tailWord_405428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393586987605536217452469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9858115983474048289936625 7393586987605536217452469)
  ·
    refine ⟨693148780088019020386169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7393586987605536217452469 693148780088019020386169)
    ·
      refine ⟨519861585066014265289627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 693148780088019020386169 519861585066014265289627)
      ·
        refine ⟨779792377599021397934441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 519861585066014265289627 779792377599021397934441)
        ·
          refine ⟨584844283199266048450831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 779792377599021397934441 584844283199266048450831)
          ·
            refine ⟨877266424798899072676247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584844283199266048450831 877266424798899072676247)
            ·
              refine ⟨1315899637198348609014371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877266424798899072676247 1315899637198348609014371)
              ·
                refine ⟨1973849455797522913521557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315899637198348609014371 1973849455797522913521557)
                ·
                  refine ⟨92524193240508886571323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1973849455797522913521557 92524193240508886571323)
                  ·
                    rfl

theorem cell21_405428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_405428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405428 prefixEnd_405428 := by exact prefixLift 405428
  have htrace : WordTrace (prefixWord ++ tailWord_405428) baseStart_405428 baseEnd_405428 := by
    simpa [prefixWord, tailWord_405428, baseEnd_405428] using wordTrace_append hprefix tailTrace_405428
  have hstable : (prefixWord ++ tailWord_405428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405428).length < 2 ^ (prefixWord ++ tailWord_405428).sum := by decide
  have hdescent : baseEnd_405428 < baseStart_405428 := by decide
  rcases family_descends (prefixWord ++ tailWord_405428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405439 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 5]
def baseStart_405439 : Nat := 118140960795 + 405439 * 2 ^ 59
def prefixEnd_405439 : Nat := 4983230072969 + 3 ^ 40 * 405439 * 2
def baseEnd_405439 : Nat := 92526703590375311887967

theorem tailTrace_405439 : CollatzResearch.WordTrace tailWord_405439 prefixEnd_405439 92526703590375311887967 := by
  unfold tailWord_405439
  simp only [CollatzResearch.WordTrace]
  refine ⟨14787575178171221313555371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9858383452114147542370247 14787575178171221313555371)
  ·
    refine ⟨22181362767256831970333057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14787575178171221313555371 22181362767256831970333057)
    ·
      refine ⟨16636022075442623977749793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22181362767256831970333057 16636022075442623977749793)
      ·
        refine ⟨12477016556581967983312345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16636022075442623977749793 12477016556581967983312345)
        ·
          refine ⟨9357762417436475987484259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12477016556581967983312345 9357762417436475987484259)
          ·
            refine ⟨14036643626154713981226389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9357762417436475987484259 14036643626154713981226389)
            ·
              refine ⟨657967669976002217869987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14036643626154713981226389 657967669976002217869987)
              ·
                refine ⟨986951504964003326804981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657967669976002217869987 986951504964003326804981)
                ·
                  refine ⟨92526703590375311887967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 986951504964003326804981 92526703590375311887967)
                  ·
                    rfl

theorem cell21_405439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 5].length) (baseStart_405439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405439 prefixEnd_405439 := by exact prefixLift 405439
  have htrace : WordTrace (prefixWord ++ tailWord_405439) baseStart_405439 baseEnd_405439 := by
    simpa [prefixWord, tailWord_405439, baseEnd_405439] using wordTrace_append hprefix tailTrace_405439
  have hstable : (prefixWord ++ tailWord_405439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405439).length < 2 ^ (prefixWord ++ tailWord_405439).sum := by decide
  have hdescent : baseEnd_405439 < baseStart_405439 := by decide
  rcases family_descends (prefixWord ++ tailWord_405439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405636 : List Nat := [2, 3, 2, 1, 2, 1, 3, 7]
def baseStart_405636 : Nat := 118140960795 + 405636 * 2 ^ 59
def prefixEnd_405636 : Nat := 4983230072969 + 3 ^ 40 * 405636 * 2
def baseEnd_405636 : Nat := 30857220558115582368077

theorem tailTrace_405636 : CollatzResearch.WordTrace tailWord_405636 prefixEnd_405636 30857220558115582368077 := by
  unfold tailWord_405636
  simp only [CollatzResearch.WordTrace]
  refine ⟨7397380179228761979238381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9863173572305015972317841 7397380179228761979238381)
  ·
    refine ⟨2774017567210785742214393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7397380179228761979238381 2774017567210785742214393)
    ·
      refine ⟨2080513175408089306660795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2774017567210785742214393 2080513175408089306660795)
      ·
        refine ⟨3120769763112133959991193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2080513175408089306660795 3120769763112133959991193)
        ·
          refine ⟨2340577322334100469993395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3120769763112133959991193 2340577322334100469993395)
          ·
            refine ⟨3510865983501150704990093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340577322334100469993395 3510865983501150704990093)
            ·
              refine ⟨1316574743812931514371285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3510865983501150704990093 1316574743812931514371285)
              ·
                refine ⟨30857220558115582368077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1316574743812931514371285 30857220558115582368077)
                ·
                  rfl

theorem cell21_405636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_405636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405636 prefixEnd_405636 := by exact prefixLift 405636
  have htrace : WordTrace (prefixWord ++ tailWord_405636) baseStart_405636 baseEnd_405636 := by
    simpa [prefixWord, tailWord_405636, baseEnd_405636] using wordTrace_append hprefix tailTrace_405636
  have hstable : (prefixWord ++ tailWord_405636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405636).length < 2 ^ (prefixWord ++ tailWord_405636).sum := by decide
  have hdescent : baseEnd_405636 < baseStart_405636 := by decide
  rcases family_descends (prefixWord ++ tailWord_405636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405718 : List Nat := [5, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_405718 : Nat := 118140960795 + 405718 * 2 ^ 59
def prefixEnd_405718 : Nat := 4983230072969 + 3 ^ 40 * 405718 * 2
def baseEnd_405718 : Nat := 92590375191532826737397

theorem tailTrace_405718 : CollatzResearch.WordTrace tailWord_405718 prefixEnd_405718 92590375191532826737397 := by
  unfold tailWord_405718
  simp only [CollatzResearch.WordTrace]
  refine ⟨924859446510028247685113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9865167429440301308641205 924859446510028247685113)
  ·
    refine ⟨693644584882521185763835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 924859446510028247685113 693644584882521185763835)
    ·
      refine ⟨1040466877323781778645753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693644584882521185763835 1040466877323781778645753)
      ·
        refine ⟨780350157992836333984315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1040466877323781778645753 780350157992836333984315)
        ·
          refine ⟨1170525236989254500976473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780350157992836333984315 1170525236989254500976473)
          ·
            refine ⟨877893927741940875732355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1170525236989254500976473 877893927741940875732355)
            ·
              refine ⟨1316840891612911313598533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877893927741940875732355 1316840891612911313598533)
              ·
                refine ⟨246907667177420871299725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1316840891612911313598533 246907667177420871299725)
                ·
                  refine ⟨92590375191532826737397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246907667177420871299725 92590375191532826737397)
                  ·
                    rfl

theorem cell21_405718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_405718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405718 prefixEnd_405718 := by exact prefixLift 405718
  have htrace : WordTrace (prefixWord ++ tailWord_405718) baseStart_405718 baseEnd_405718 := by
    simpa [prefixWord, tailWord_405718, baseEnd_405718] using wordTrace_append hprefix tailTrace_405718
  have hstable : (prefixWord ++ tailWord_405718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405718).length < 2 ^ (prefixWord ++ tailWord_405718).sum := by decide
  have hdescent : baseEnd_405718 < baseStart_405718 := by decide
  rcases family_descends (prefixWord ++ tailWord_405718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405743 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 5]
def baseStart_405743 : Nat := 118140960795 + 405743 * 2 ^ 59
def prefixEnd_405743 : Nat := 4983230072969 + 3 ^ 40 * 405743 * 2
def baseEnd_405743 : Nat := 92596080532138338820679

theorem tailTrace_405743 : CollatzResearch.WordTrace tailWord_405743 prefixEnd_405743 92596080532138338820679 := by
  unfold tailWord_405743
  simp only [CollatzResearch.WordTrace]
  refine ⟨14798662969069881232621883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9865775312713254155081255 14798662969069881232621883)
  ·
    refine ⟨22197994453604821848932825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14798662969069881232621883 22197994453604821848932825)
    ·
      refine ⟨16648495840203616386699619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22197994453604821848932825 16648495840203616386699619)
      ·
        refine ⟨24972743760305424580049429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16648495840203616386699619 24972743760305424580049429)
        ·
          refine ⟨1170597363764316777189817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24972743760305424580049429 1170597363764316777189817)
          ·
            refine ⟨877948022823237582892363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1170597363764316777189817 877948022823237582892363)
            ·
              refine ⟨1316922034234856374338545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877948022823237582892363 1316922034234856374338545)
              ·
                refine ⟨987691525676142280753909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316922034234856374338545 987691525676142280753909)
                ·
                  refine ⟨92596080532138338820679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 987691525676142280753909 92596080532138338820679)
                  ·
                    rfl

theorem cell21_405743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 5].length) (baseStart_405743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405743 prefixEnd_405743 := by exact prefixLift 405743
  have htrace : WordTrace (prefixWord ++ tailWord_405743) baseStart_405743 baseEnd_405743 := by
    simpa [prefixWord, tailWord_405743, baseEnd_405743] using wordTrace_append hprefix tailTrace_405743
  have hstable : (prefixWord ++ tailWord_405743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405743).length < 2 ^ (prefixWord ++ tailWord_405743).sum := by decide
  have hdescent : baseEnd_405743 < baseStart_405743 := by decide
  rcases family_descends (prefixWord ++ tailWord_405743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405771 : List Nat := [1, 1, 1, 1, 5, 2, 10]
def baseStart_405771 : Nat := 118140960795 + 405771 * 2 ^ 59
def prefixEnd_405771 : Nat := 4983230072969 + 3 ^ 40 * 405771 * 2
def baseEnd_405771 : Nat := 10289163390401834705995

theorem tailTrace_405771 : CollatzResearch.WordTrace tailWord_405771 prefixEnd_405771 10289163390401834705995 := by
  unfold tailWord_405771
  simp only [CollatzResearch.WordTrace]
  refine ⟨14799684212968442014641167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9866456141978961343094111 14799684212968442014641167)
  ·
    refine ⟨22199526319452663021961751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14799684212968442014641167 22199526319452663021961751)
    ·
      refine ⟨33299289479178994532942627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22199526319452663021961751 33299289479178994532942627)
      ·
        refine ⟨49948934218768491799413941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33299289479178994532942627 49948934218768491799413941)
        ·
          refine ⟨4682712583009546106195057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49948934218768491799413941 4682712583009546106195057)
          ·
            refine ⟨3512034437257159579646293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4682712583009546106195057 3512034437257159579646293)
            ·
              refine ⟨10289163390401834705995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3512034437257159579646293 10289163390401834705995)
              ·
                rfl

theorem cell21_405771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 10].length) (baseStart_405771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405771 prefixEnd_405771 := by exact prefixLift 405771
  have htrace : WordTrace (prefixWord ++ tailWord_405771) baseStart_405771 baseEnd_405771 := by
    simpa [prefixWord, tailWord_405771, baseEnd_405771] using wordTrace_append hprefix tailTrace_405771
  have hstable : (prefixWord ++ tailWord_405771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405771).length < 2 ^ (prefixWord ++ tailWord_405771).sum := by decide
  have hdescent : baseEnd_405771 < baseStart_405771 := by decide
  rcases family_descends (prefixWord ++ tailWord_405771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405791 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 4]
def baseStart_405791 : Nat := 118140960795 + 405791 * 2 ^ 59
def prefixEnd_405791 : Nat := 4983230072969 + 3 ^ 40 * 405791 * 2
def baseEnd_405791 : Nat := 92607034786100922020581

theorem tailTrace_405791 : CollatzResearch.WordTrace tailWord_405791 prefixEnd_405791 92607034786100922020581 := by
  unfold tailWord_405791
  simp only [CollatzResearch.WordTrace]
  refine ⟨14800413672895985430369227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9866942448597323620246151 14800413672895985430369227)
  ·
    refine ⟨22200620509343978145553841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14800413672895985430369227 22200620509343978145553841)
    ·
      refine ⟨16650465382007983609165381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22200620509343978145553841 16650465382007983609165381)
      ·
        refine ⟨3121962259126496926718509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16650465382007983609165381 3121962259126496926718509)
        ·
          refine ⟨1170735847172436347519441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3121962259126496926718509 1170735847172436347519441)
          ·
            refine ⟨878051885379327260639581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1170735847172436347519441 878051885379327260639581)
            ·
              refine ⟨329269457017247722739843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 878051885379327260639581 329269457017247722739843)
              ·
                refine ⟨493904185525871584109765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329269457017247722739843 493904185525871584109765)
                ·
                  refine ⟨92607034786100922020581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 493904185525871584109765 92607034786100922020581)
                  ·
                    rfl

theorem cell21_405791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 4].length) (baseStart_405791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405791 prefixEnd_405791 := by exact prefixLift 405791
  have htrace : WordTrace (prefixWord ++ tailWord_405791) baseStart_405791 baseEnd_405791 := by
    simpa [prefixWord, tailWord_405791, baseEnd_405791] using wordTrace_append hprefix tailTrace_405791
  have hstable : (prefixWord ++ tailWord_405791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405791).length < 2 ^ (prefixWord ++ tailWord_405791).sum := by decide
  have hdescent : baseEnd_405791 < baseStart_405791 := by decide
  rcases family_descends (prefixWord ++ tailWord_405791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405833 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 4]
def baseStart_405833 : Nat := 118140960795 + 405833 * 2 ^ 59
def prefixEnd_405833 : Nat := 4983230072969 + 3 ^ 40 * 405833 * 2
def baseEnd_405833 : Nat := 92616619758318182320495

theorem tailTrace_405833 : CollatzResearch.WordTrace tailWord_405833 prefixEnd_405833 92616619758318182320495 := by
  unfold tailWord_405833
  simp only [CollatzResearch.WordTrace]
  refine ⟨14801945538743826603398153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9867963692495884402265435 14801945538743826603398153)
  ·
    refine ⟨11101459154057869952548615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14801945538743826603398153 11101459154057869952548615)
    ·
      refine ⟨16652188731086804928822923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11101459154057869952548615 16652188731086804928822923)
      ·
        refine ⟨24978283096630207393234385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16652188731086804928822923 24978283096630207393234385)
        ·
          refine ⟨18733712322472655544925789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24978283096630207393234385 18733712322472655544925789)
          ·
            refine ⟨7025142120927245829347171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18733712322472655544925789 7025142120927245829347171)
            ·
              refine ⟨10537713181390868744020757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7025142120927245829347171 10537713181390868744020757)
              ·
                refine ⟨493955305377696972375973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10537713181390868744020757 493955305377696972375973)
                ·
                  refine ⟨92616619758318182320495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 493955305377696972375973 92616619758318182320495)
                  ·
                    rfl

theorem cell21_405833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_405833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405833 prefixEnd_405833 := by exact prefixLift 405833
  have htrace : WordTrace (prefixWord ++ tailWord_405833) baseStart_405833 baseEnd_405833 := by
    simpa [prefixWord, tailWord_405833, baseEnd_405833] using wordTrace_append hprefix tailTrace_405833
  have hstable : (prefixWord ++ tailWord_405833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405833).length < 2 ^ (prefixWord ++ tailWord_405833).sum := by decide
  have hdescent : baseEnd_405833 < baseStart_405833 := by decide
  rcases family_descends (prefixWord ++ tailWord_405833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405864 : List Nat := [2, 1, 4, 2, 2, 1, 2, 7]
def baseStart_405864 : Nat := 118140960795 + 405864 * 2 ^ 59
def prefixEnd_405864 : Nat := 4983230072969 + 3 ^ 40 * 405864 * 2
def baseEnd_405864 : Nat := 30874564793556339101255

theorem tailTrace_405864 : CollatzResearch.WordTrace tailWord_405864 prefixEnd_405864 30874564793556339101255 := by
  unfold tailWord_405864
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401538100815759448888323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9868717467754345931851097 7401538100815759448888323)
  ·
    refine ⟨11102307151223639173332485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7401538100815759448888323 11102307151223639173332485)
    ·
      refine ⟨2081682590854432344999841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11102307151223639173332485 2081682590854432344999841)
      ·
        refine ⟨1561261943140824258749881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2081682590854432344999841 1561261943140824258749881)
        ·
          refine ⟨1170946457355618194062411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1561261943140824258749881 1170946457355618194062411)
          ·
            refine ⟨1756419686033427291093617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170946457355618194062411 1756419686033427291093617)
            ·
              refine ⟨1317314764525070468320213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1756419686033427291093617 1317314764525070468320213)
              ·
                refine ⟨30874564793556339101255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1317314764525070468320213 30874564793556339101255)
                ·
                  rfl

theorem cell21_405864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_405864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405864 prefixEnd_405864 := by exact prefixLift 405864
  have htrace : WordTrace (prefixWord ++ tailWord_405864) baseStart_405864 baseEnd_405864 := by
    simpa [prefixWord, tailWord_405864, baseEnd_405864] using wordTrace_append hprefix tailTrace_405864
  have hstable : (prefixWord ++ tailWord_405864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405864).length < 2 ^ (prefixWord ++ tailWord_405864).sum := by decide
  have hdescent : baseEnd_405864 < baseStart_405864 := by decide
  rcases family_descends (prefixWord ++ tailWord_405864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405898 : List Nat := [3, 1, 2, 5, 1, 2, 1, 6]
def baseStart_405898 : Nat := 118140960795 + 405898 * 2 ^ 59
def prefixEnd_405898 : Nat := 4983230072969 + 3 ^ 40 * 405898 * 2
def baseEnd_405898 : Nat := 30877151214630837912343

theorem tailTrace_405898 : CollatzResearch.WordTrace tailWord_405898 prefixEnd_405898 30877151214630837912343 := by
  unfold tailWord_405898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3701079070877085676128587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9869544189005561803009565 3701079070877085676128587)
  ·
    refine ⟨5551618606315628514192881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3701079070877085676128587 5551618606315628514192881)
    ·
      refine ⟨4163713954736721385644661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5551618606315628514192881 4163713954736721385644661)
      ·
        refine ⟨390348183256567629904187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4163713954736721385644661 390348183256567629904187)
        ·
          refine ⟨585522274884851444856281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390348183256567629904187 585522274884851444856281)
          ·
            refine ⟨439141706163638583642211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585522274884851444856281 439141706163638583642211)
            ·
              refine ⟨658712559245457875463317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439141706163638583642211 658712559245457875463317)
              ·
                refine ⟨30877151214630837912343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 658712559245457875463317 30877151214630837912343)
                ·
                  rfl

theorem cell21_405898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_405898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405898 prefixEnd_405898 := by exact prefixLift 405898
  have htrace : WordTrace (prefixWord ++ tailWord_405898) baseStart_405898 baseEnd_405898 := by
    simpa [prefixWord, tailWord_405898, baseEnd_405898] using wordTrace_append hprefix tailTrace_405898
  have hstable : (prefixWord ++ tailWord_405898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405898).length < 2 ^ (prefixWord ++ tailWord_405898).sum := by decide
  have hdescent : baseEnd_405898 < baseStart_405898 := by decide
  rcases family_descends (prefixWord ++ tailWord_405898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405968 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_405968 : Nat := 118140960795 + 405968 * 2 ^ 59
def prefixEnd_405968 : Nat := 4983230072969 + 3 ^ 40 * 405968 * 2
def baseEnd_405968 : Nat := 92647428597587947570219

theorem tailTrace_405968 : CollatzResearch.WordTrace tailWord_405968 prefixEnd_405968 92647428597587947570219 := by
  unfold tailWord_405968
  simp only [CollatzResearch.WordTrace]
  refine ⟨7403434696627372329781279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9871246262169829773041705 7403434696627372329781279)
  ·
    refine ⟨11105152044941058494671919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7403434696627372329781279 11105152044941058494671919)
    ·
      refine ⟨16657728067411587742007879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11105152044941058494671919 16657728067411587742007879)
      ·
        refine ⟨24986592101117381613011819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16657728067411587742007879 24986592101117381613011819)
        ·
          refine ⟨37479888151676072419517729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24986592101117381613011819 37479888151676072419517729)
          ·
            refine ⟨28109916113757054314638297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37479888151676072419517729 28109916113757054314638297)
            ·
              refine ⟨21082437085317790735978723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28109916113757054314638297 21082437085317790735978723)
              ·
                refine ⟨31623655627976686103968085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21082437085317790735978723 31623655627976686103968085)
                ·
                  refine ⟨92647428597587947570219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 31623655627976686103968085 92647428597587947570219)
                  ·
                    rfl

theorem cell21_405968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_405968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_405968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_405968 prefixEnd_405968 := by exact prefixLift 405968
  have htrace : WordTrace (prefixWord ++ tailWord_405968) baseStart_405968 baseEnd_405968 := by
    simpa [prefixWord, tailWord_405968, baseEnd_405968] using wordTrace_append hprefix tailTrace_405968
  have hstable : (prefixWord ++ tailWord_405968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405968).length < 2 ^ (prefixWord ++ tailWord_405968).sum := by decide
  have hdescent : baseEnd_405968 < baseStart_405968 := by decide
  rcases family_descends (prefixWord ++ tailWord_405968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406005 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 5]
def baseStart_406005 : Nat := 118140960795 + 406005 * 2 ^ 59
def prefixEnd_406005 : Nat := 4983230072969 + 3 ^ 40 * 406005 * 2
def baseEnd_406005 : Nat := 92655872501684105453477

theorem tailTrace_406005 : CollatzResearch.WordTrace tailWord_406005 prefixEnd_406005 92655872501684105453477 := by
  unfold tailWord_406005
  simp only [CollatzResearch.WordTrace]
  refine ⟨14808218894120699978659469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9872145929413799985772979 14808218894120699978659469)
  ·
    refine ⟨5553082085295262491997301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14808218894120699978659469 5553082085295262491997301)
    ·
      refine ⟨520601445496430858624747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5553082085295262491997301 520601445496430858624747)
      ·
        refine ⟨780902168244646287937121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520601445496430858624747 780902168244646287937121)
        ·
          refine ⟨585676626183484715952841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780902168244646287937121 585676626183484715952841)
          ·
            refine ⟨439257469637613536964631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585676626183484715952841 439257469637613536964631)
            ·
              refine ⟨658886204456420305446947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439257469637613536964631 658886204456420305446947)
              ·
                refine ⟨988329306684630458170421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658886204456420305446947 988329306684630458170421)
                ·
                  refine ⟨92655872501684105453477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 988329306684630458170421 92655872501684105453477)
                  ·
                    rfl

theorem cell21_406005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_406005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406005 prefixEnd_406005 := by exact prefixLift 406005
  have htrace : WordTrace (prefixWord ++ tailWord_406005) baseStart_406005 baseEnd_406005 := by
    simpa [prefixWord, tailWord_406005, baseEnd_406005] using wordTrace_append hprefix tailTrace_406005
  have hstable : (prefixWord ++ tailWord_406005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406005).length < 2 ^ (prefixWord ++ tailWord_406005).sum := by decide
  have hdescent : baseEnd_406005 < baseStart_406005 := by decide
  rcases family_descends (prefixWord ++ tailWord_406005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406047 : List Nat := [1, 1, 2, 4, 1, 1, 1, 7, 3]
def baseStart_406047 : Nat := 118140960795 + 406047 * 2 ^ 59
def prefixEnd_406047 : Nat := 4983230072969 + 3 ^ 40 * 406047 * 2
def baseEnd_406047 : Nat := 92665457473901365753391

theorem tailTrace_406047 : CollatzResearch.WordTrace tailWord_406047 prefixEnd_406047 92665457473901365753391 := by
  unfold tailWord_406047
  simp only [CollatzResearch.WordTrace]
  refine ⟨14809750759968541151688395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9873167173312360767792263 14809750759968541151688395)
  ·
    refine ⟨22214626139952811727532593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14809750759968541151688395 22214626139952811727532593)
    ·
      refine ⟨16660969604964608795649445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22214626139952811727532593 16660969604964608795649445)
      ·
        refine ⟨3123931800930864149184271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16660969604964608795649445 3123931800930864149184271)
        ·
          refine ⟨4685897701396296223776407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3123931800930864149184271 4685897701396296223776407)
          ·
            refine ⟨7028846552094444335664611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4685897701396296223776407 7028846552094444335664611)
            ·
              refine ⟨10543269828141666503496917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7028846552094444335664611 10543269828141666503496917)
              ·
                refine ⟨247107886597070308675709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10543269828141666503496917 247107886597070308675709)
                ·
                  refine ⟨92665457473901365753391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247107886597070308675709 92665457473901365753391)
                  ·
                    rfl

theorem cell21_406047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 3].length) (baseStart_406047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406047 prefixEnd_406047 := by exact prefixLift 406047
  have htrace : WordTrace (prefixWord ++ tailWord_406047) baseStart_406047 baseEnd_406047 := by
    simpa [prefixWord, tailWord_406047, baseEnd_406047] using wordTrace_append hprefix tailTrace_406047
  have hstable : (prefixWord ++ tailWord_406047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406047).length < 2 ^ (prefixWord ++ tailWord_406047).sum := by decide
  have hdescent : baseEnd_406047 < baseStart_406047 := by decide
  rcases family_descends (prefixWord ++ tailWord_406047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406064 : List Nat := [2, 1, 1, 1, 2, 3, 6, 2, 3]
def baseStart_406064 : Nat := 118140960795 + 406064 * 2 ^ 59
def prefixEnd_406064 : Nat := 4983230072969 + 3 ^ 40 * 406064 * 2
def baseEnd_406064 : Nat := 92669337105513113970023

theorem tailTrace_406064 : CollatzResearch.WordTrace tailWord_406064 prefixEnd_406064 92669337105513113970023 := by
  unfold tailWord_406064
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405185400453476527528623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9873580533937968703371497 7405185400453476527528623)
  ·
    refine ⟨11107778100680214791292935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7405185400453476527528623 11107778100680214791292935)
    ·
      refine ⟨16661667151020322186939403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11107778100680214791292935 16661667151020322186939403)
      ·
        refine ⟨24992500726530483280409105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16661667151020322186939403 24992500726530483280409105)
        ·
          refine ⟨18744375544897862460306829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24992500726530483280409105 18744375544897862460306829)
          ·
            refine ⟨7029140829336698422615061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18744375544897862460306829 7029140829336698422615061)
            ·
              refine ⟨329490976375157738560081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7029140829336698422615061 329490976375157738560081)
              ·
                refine ⟨247118232281368303920061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329490976375157738560081 247118232281368303920061)
                ·
                  refine ⟨92669337105513113970023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247118232281368303920061 92669337105513113970023)
                  ·
                    rfl

theorem cell21_406064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 3].length) (baseStart_406064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406064 prefixEnd_406064 := by exact prefixLift 406064
  have htrace : WordTrace (prefixWord ++ tailWord_406064) baseStart_406064 baseEnd_406064 := by
    simpa [prefixWord, tailWord_406064, baseEnd_406064] using wordTrace_append hprefix tailTrace_406064
  have hstable : (prefixWord ++ tailWord_406064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406064).length < 2 ^ (prefixWord ++ tailWord_406064).sum := by decide
  have hdescent : baseEnd_406064 < baseStart_406064 := by decide
  rcases family_descends (prefixWord ++ tailWord_406064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406092 : List Nat := [2, 2, 1, 3, 1, 2, 5, 5]
def baseStart_406092 : Nat := 118140960795 + 406092 * 2 ^ 59
def prefixEnd_406092 : Nat := 4983230072969 + 3 ^ 40 * 406092 * 2
def baseEnd_406092 : Nat := 30891909028997095834433

theorem tailTrace_406092 : CollatzResearch.WordTrace tailWord_406092 prefixEnd_406092 30891909028997095834433 := by
  unfold tailWord_406092
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405696022402756918538265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9874261363203675891384353 7405696022402756918538265)
  ·
    refine ⟨5554272016802067688903699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7405696022402756918538265 5554272016802067688903699)
    ·
      refine ⟨8331408025203101533355549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5554272016802067688903699 8331408025203101533355549)
      ·
        refine ⟨3124278009451163075008331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8331408025203101533355549 3124278009451163075008331)
        ·
          refine ⟨4686417014176744612512497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3124278009451163075008331 4686417014176744612512497)
          ·
            refine ⟨3514812760632558459384373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4686417014176744612512497 3514812760632558459384373)
            ·
              refine ⟨329513696309302355567285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3514812760632558459384373 329513696309302355567285)
              ·
                refine ⟨30891909028997095834433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 329513696309302355567285 30891909028997095834433)
                ·
                  rfl

theorem cell21_406092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_406092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406092 prefixEnd_406092 := by exact prefixLift 406092
  have htrace : WordTrace (prefixWord ++ tailWord_406092) baseStart_406092 baseEnd_406092 := by
    simpa [prefixWord, tailWord_406092, baseEnd_406092] using wordTrace_append hprefix tailTrace_406092
  have hstable : (prefixWord ++ tailWord_406092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406092).length < 2 ^ (prefixWord ++ tailWord_406092).sum := by decide
  have hdescent : baseEnd_406092 < baseStart_406092 := by decide
  rcases family_descends (prefixWord ++ tailWord_406092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406151 : List Nat := [1, 1, 4, 2, 1, 2, 3, 7]
def baseStart_406151 : Nat := 118140960795 + 406151 * 2 ^ 59
def prefixEnd_406151 : Nat := 4983230072969 + 3 ^ 40 * 406151 * 2
def baseEnd_406151 : Nat := 30896397230273432006615

theorem tailTrace_406151 : CollatzResearch.WordTrace tailWord_406151 prefixEnd_406151 30896397230273432006615 := by
  unfold tailWord_406151
  simp only [CollatzResearch.WordTrace]
  refine ⟨14813543951591766913474307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9875695967727844608982871 14813543951591766913474307)
  ·
    refine ⟨22220315927387650370211461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14813543951591766913474307 22220315927387650370211461)
    ·
      refine ⟨4166309236385184444414649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22220315927387650370211461 4166309236385184444414649)
      ·
        refine ⟨3124731927288888333310987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4166309236385184444414649 3124731927288888333310987)
        ·
          refine ⟨4687097890933332499966481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3124731927288888333310987 4687097890933332499966481)
          ·
            refine ⟨3515323418199999374974861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4687097890933332499966481 3515323418199999374974861)
            ·
              refine ⟨1318246281824999765615573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3515323418199999374974861 1318246281824999765615573)
              ·
                refine ⟨30896397230273432006615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1318246281824999765615573 30896397230273432006615)
                ·
                  rfl

theorem cell21_406151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 7].length) (baseStart_406151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406151 prefixEnd_406151 := by exact prefixLift 406151
  have htrace : WordTrace (prefixWord ++ tailWord_406151) baseStart_406151 baseEnd_406151 := by
    simpa [prefixWord, tailWord_406151, baseEnd_406151] using wordTrace_append hprefix tailTrace_406151
  have hstable : (prefixWord ++ tailWord_406151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406151).length < 2 ^ (prefixWord ++ tailWord_406151).sum := by decide
  have hdescent : baseEnd_406151 < baseStart_406151 := by decide
  rcases family_descends (prefixWord ++ tailWord_406151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406244 : List Nat := [2, 3, 1, 1, 1, 6, 1, 6]
def baseStart_406244 : Nat := 118140960795 + 406244 * 2 ^ 59
def prefixEnd_406244 : Nat := 4983230072969 + 3 ^ 40 * 406244 * 2
def baseEnd_406244 : Nat := 30903471852624266989885

theorem tailTrace_406244 : CollatzResearch.WordTrace tailWord_406244 prefixEnd_406244 30903471852624266989885 := by
  unfold tailWord_406244
  simp only [CollatzResearch.WordTrace]
  refine ⟨7408467970127421898304893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9877957293503229197739857 7408467970127421898304893)
  ·
    refine ⟨2778175488797783211864335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7408467970127421898304893 2778175488797783211864335)
    ·
      refine ⟨4167263233196674817796503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2778175488797783211864335 4167263233196674817796503)
      ·
        refine ⟨6250894849795012226694755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4167263233196674817796503 6250894849795012226694755)
        ·
          refine ⟨9376342274692518340042133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6250894849795012226694755 9376342274692518340042133)
          ·
            refine ⟨439516044126211797189475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9376342274692518340042133 439516044126211797189475)
            ·
              refine ⟨659274066189317695784213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439516044126211797189475 659274066189317695784213)
              ·
                refine ⟨30903471852624266989885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 659274066189317695784213 30903471852624266989885)
                ·
                  rfl

theorem cell21_406244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_406244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406244 prefixEnd_406244 := by exact prefixLift 406244
  have htrace : WordTrace (prefixWord ++ tailWord_406244) baseStart_406244 baseEnd_406244 := by
    simpa [prefixWord, tailWord_406244, baseEnd_406244] using wordTrace_append hprefix tailTrace_406244
  have hstable : (prefixWord ++ tailWord_406244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406244).length < 2 ^ (prefixWord ++ tailWord_406244).sum := by decide
  have hdescent : baseEnd_406244 < baseStart_406244 := by decide
  rcases family_descends (prefixWord ++ tailWord_406244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406258 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_406258 : Nat := 118140960795 + 406258 * 2 ^ 59
def prefixEnd_406258 : Nat := 4983230072969 + 3 ^ 40 * 406258 * 2
def baseEnd_406258 : Nat := 92713610548611887736293

theorem tailTrace_406258 : CollatzResearch.WordTrace tailWord_406258 prefixEnd_406258 92713610548611887736293 := by
  unfold tailWord_406258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3704361640551031046904857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9878297708136082791746285 3704361640551031046904857)
  ·
    refine ⟨2778271230413273285178643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3704361640551031046904857 2778271230413273285178643)
    ·
      refine ⟨4167406845619909927767965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2778271230413273285178643 4167406845619909927767965)
      ·
        refine ⟨1562777567107466222912987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4167406845619909927767965 1562777567107466222912987)
        ·
          refine ⟨2344166350661199334369481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562777567107466222912987 2344166350661199334369481)
          ·
            refine ⟨1758124762995899500777111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2344166350661199334369481 1758124762995899500777111)
            ·
              refine ⟨2637187144493849251165667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1758124762995899500777111 2637187144493849251165667)
              ·
                refine ⟨3955780716740773876748501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637187144493849251165667 3955780716740773876748501)
                ·
                  refine ⟨92713610548611887736293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3955780716740773876748501 92713610548611887736293)
                  ·
                    rfl

theorem cell21_406258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_406258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406258 prefixEnd_406258 := by exact prefixLift 406258
  have htrace : WordTrace (prefixWord ++ tailWord_406258) baseStart_406258 baseEnd_406258 := by
    simpa [prefixWord, tailWord_406258, baseEnd_406258] using wordTrace_append hprefix tailTrace_406258
  have hstable : (prefixWord ++ tailWord_406258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406258).length < 2 ^ (prefixWord ++ tailWord_406258).sum := by decide
  have hdescent : baseEnd_406258 < baseStart_406258 := by decide
  rcases family_descends (prefixWord ++ tailWord_406258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406289 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 4]
def baseStart_406289 : Nat := 118140960795 + 406289 * 2 ^ 59
def prefixEnd_406289 : Nat := 4983230072969 + 3 ^ 40 * 406289 * 2
def baseEnd_406289 : Nat := 92720685170962722719563

theorem tailTrace_406289 : CollatzResearch.WordTrace tailWord_406289 prefixEnd_406289 92720685170962722719563 := by
  unfold tailWord_406289
  simp only [CollatzResearch.WordTrace]
  refine ⟨14818577225091816481997921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9879051483394544321331947 14818577225091816481997921)
  ·
    refine ⟨11113932918818862361498441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14818577225091816481997921 11113932918818862361498441)
    ·
      refine ⟨8335449689114146771123831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11113932918818862361498441 8335449689114146771123831)
      ·
        refine ⟨12503174533671220156685747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8335449689114146771123831 12503174533671220156685747)
        ·
          refine ⟨18754761800506830235028621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12503174533671220156685747 18754761800506830235028621)
          ·
            refine ⟨7033035675190061338135733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18754761800506830235028621 7033035675190061338135733)
            ·
              refine ⟨659347094549068250450225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7033035675190061338135733 659347094549068250450225)
              ·
                refine ⟨494510320911801187837669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659347094549068250450225 494510320911801187837669)
                ·
                  refine ⟨92720685170962722719563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 494510320911801187837669 92720685170962722719563)
                  ·
                    rfl

theorem cell21_406289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_406289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406289 prefixEnd_406289 := by exact prefixLift 406289
  have htrace : WordTrace (prefixWord ++ tailWord_406289) baseStart_406289 baseEnd_406289 := by
    simpa [prefixWord, tailWord_406289, baseEnd_406289] using wordTrace_append hprefix tailTrace_406289
  have hstable : (prefixWord ++ tailWord_406289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406289).length < 2 ^ (prefixWord ++ tailWord_406289).sum := by decide
  have hdescent : baseEnd_406289 < baseStart_406289 := by decide
  rcases family_descends (prefixWord ++ tailWord_406289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406326 : List Nat := [5, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_406326 : Nat := 118140960795 + 406326 * 2 ^ 59
def prefixEnd_406326 : Nat := 4983230072969 + 3 ^ 40 * 406326 * 2
def baseEnd_406326 : Nat := 92729129075058880602821

theorem tailTrace_406326 : CollatzResearch.WordTrace tailWord_406326 prefixEnd_406326 92729129075058880602821 := by
  unfold tailWord_406326
  simp only [CollatzResearch.WordTrace]
  refine ⟨926245420372360737568427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9879951150638514534063221 926245420372360737568427)
  ·
    refine ⟨1389368130558541106352641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 926245420372360737568427 1389368130558541106352641)
    ·
      refine ⟨1042026097918905829764481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1389368130558541106352641 1042026097918905829764481)
      ·
        refine ⟨781519573439179372323361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1042026097918905829764481 781519573439179372323361)
        ·
          refine ⟨586139680079384529242521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 781519573439179372323361 586139680079384529242521)
          ·
            refine ⟨439604760059538396931891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586139680079384529242521 439604760059538396931891)
            ·
              refine ⟨659407140089307595397837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439604760059538396931891 659407140089307595397837)
              ·
                refine ⟨247277677533490348274189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 659407140089307595397837 247277677533490348274189)
                ·
                  refine ⟨92729129075058880602821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247277677533490348274189 92729129075058880602821)
                  ·
                    rfl

theorem cell21_406326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_406326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406326 prefixEnd_406326 := by exact prefixLift 406326
  have htrace : WordTrace (prefixWord ++ tailWord_406326) baseStart_406326 baseEnd_406326 := by
    simpa [prefixWord, tailWord_406326, baseEnd_406326] using wordTrace_append hprefix tailTrace_406326
  have hstable : (prefixWord ++ tailWord_406326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406326).length < 2 ^ (prefixWord ++ tailWord_406326).sum := by decide
  have hdescent : baseEnd_406326 < baseStart_406326 := by decide
  rcases family_descends (prefixWord ++ tailWord_406326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406337 : List Nat := [1, 2, 5, 3, 1, 2, 7]
def baseStart_406337 : Nat := 118140960795 + 406337 * 2 ^ 59
def prefixEnd_406337 : Nat := 4983230072969 + 3 ^ 40 * 406337 * 2
def baseEnd_406337 : Nat := 10303515491658367324385

theorem tailTrace_406337 : CollatzResearch.WordTrace tailWord_406337 prefixEnd_406337 10303515491658367324385 := by
  unfold tailWord_406337
  simp only [CollatzResearch.WordTrace]
  refine ⟨14820327928917920679745265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9880218619278613786496843 14820327928917920679745265)
  ·
    refine ⟨11115245946688440509808949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14820327928917920679745265 11115245946688440509808949)
    ·
      refine ⟨1042054307502041297794589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11115245946688440509808949 1042054307502041297794589)
      ·
        refine ⟨390770365313265486672971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1042054307502041297794589 390770365313265486672971)
        ·
          refine ⟨586155547969898230009457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390770365313265486672971 586155547969898230009457)
          ·
            refine ⟨439616660977423672507093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586155547969898230009457 439616660977423672507093)
            ·
              refine ⟨10303515491658367324385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 439616660977423672507093 10303515491658367324385)
              ·
                rfl

theorem cell21_406337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 7].length) (baseStart_406337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406337 prefixEnd_406337 := by exact prefixLift 406337
  have htrace : WordTrace (prefixWord ++ tailWord_406337) baseStart_406337 baseEnd_406337 := by
    simpa [prefixWord, tailWord_406337, baseEnd_406337] using wordTrace_append hprefix tailTrace_406337
  have hstable : (prefixWord ++ tailWord_406337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406337).length < 2 ^ (prefixWord ++ tailWord_406337).sum := by decide
  have hdescent : baseEnd_406337 < baseStart_406337 := by decide
  rcases family_descends (prefixWord ++ tailWord_406337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406402 : List Nat := [3, 4, 2, 2, 1, 1, 1, 4, 3]
def baseStart_406402 : Nat := 118140960795 + 406402 * 2 ^ 59
def prefixEnd_406402 : Nat := 4983230072969 + 3 ^ 40 * 406402 * 2
def baseEnd_406402 : Nat := 92746473310499637335999

theorem tailTrace_406402 : CollatzResearch.WordTrace tailWord_406402 prefixEnd_406402 92746473310499637335999 := by
  unfold tailWord_406402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3705674668420609195215365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9881799115788291187240973 3705674668420609195215365)
  ·
    refine ⟨694814000328864224102881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3705674668420609195215365 694814000328864224102881)
    ·
      refine ⟨521110500246648168077161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 694814000328864224102881 521110500246648168077161)
      ·
        refine ⟨390832875184986126057871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521110500246648168077161 390832875184986126057871)
        ·
          refine ⟨586249312777479189086807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390832875184986126057871 586249312777479189086807)
          ·
            refine ⟨879373969166218783630211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586249312777479189086807 879373969166218783630211)
            ·
              refine ⟨1319060953749328175445317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879373969166218783630211 1319060953749328175445317)
              ·
                refine ⟨247323928827999032895997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1319060953749328175445317 247323928827999032895997)
                ·
                  refine ⟨92746473310499637335999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247323928827999032895997 92746473310499637335999)
                  ·
                    rfl

theorem cell21_406402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_406402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406402 prefixEnd_406402 := by exact prefixLift 406402
  have htrace : WordTrace (prefixWord ++ tailWord_406402) baseStart_406402 baseEnd_406402 := by
    simpa [prefixWord, tailWord_406402, baseEnd_406402] using wordTrace_append hprefix tailTrace_406402
  have hstable : (prefixWord ++ tailWord_406402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406402).length < 2 ^ (prefixWord ++ tailWord_406402).sum := by decide
  have hdescent : baseEnd_406402 < baseStart_406402 := by decide
  rcases family_descends (prefixWord ++ tailWord_406402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406545 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 5]
def baseStart_406545 : Nat := 118140960795 + 406545 * 2 ^ 59
def prefixEnd_406545 : Nat := 4983230072969 + 3 ^ 40 * 406545 * 2
def baseEnd_406545 : Nat := 92779107858763166452373

theorem tailTrace_406545 : CollatzResearch.WordTrace tailWord_406545 prefixEnd_406545 92779107858763166452373 := by
  unfold tailWord_406545
  simp only [CollatzResearch.WordTrace]
  refine ⟨14827914312164372203317089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9885276208109581468878059 14827914312164372203317089)
  ·
    refine ⟨11120935734123279152487817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14827914312164372203317089 11120935734123279152487817)
    ·
      refine ⟨8340701800592459364365863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11120935734123279152487817 8340701800592459364365863)
      ·
        refine ⟨12511052700888689046548795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8340701800592459364365863 12511052700888689046548795)
        ·
          refine ⟨18766579051333033569823193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12511052700888689046548795 18766579051333033569823193)
          ·
            refine ⟨14074934288499775177367395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18766579051333033569823193 14074934288499775177367395)
            ·
              refine ⟨21112401432749662766051093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14074934288499775177367395 21112401432749662766051093)
              ·
                refine ⟨989643817160140442158645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21112401432749662766051093 989643817160140442158645)
                ·
                  refine ⟨92779107858763166452373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 989643817160140442158645 92779107858763166452373)
                  ·
                    rfl

theorem cell21_406545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_406545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406545 prefixEnd_406545 := by exact prefixLift 406545
  have htrace : WordTrace (prefixWord ++ tailWord_406545) baseStart_406545 baseEnd_406545 := by
    simpa [prefixWord, tailWord_406545, baseEnd_406545] using wordTrace_append hprefix tailTrace_406545
  have hstable : (prefixWord ++ tailWord_406545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406545).length < 2 ^ (prefixWord ++ tailWord_406545).sum := by decide
  have hdescent : baseEnd_406545 < baseStart_406545 := by decide
  rcases family_descends (prefixWord ++ tailWord_406545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406638 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_406638 : Nat := 118140960795 + 406638 * 2 ^ 59
def prefixEnd_406638 : Nat := 4983230072969 + 3 ^ 40 * 406638 * 2
def baseEnd_406638 : Nat := 92800331725815671402183

theorem tailTrace_406638 : CollatzResearch.WordTrace tailWord_406638 prefixEnd_406638 92800331725815671402183 := by
  unfold tailWord_406638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853913287603431135806571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9887537533884966057635045 1853913287603431135806571)
  ·
    refine ⟨2780869931405146703709857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1853913287603431135806571 2780869931405146703709857)
    ·
      refine ⟨2085652448553860027782393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2780869931405146703709857 2085652448553860027782393)
      ·
        refine ⟨1564239336415395020836795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2085652448553860027782393 1564239336415395020836795)
        ·
          refine ⟨2346359004623092531255193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564239336415395020836795 2346359004623092531255193)
          ·
            refine ⟨1759769253467319398441395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2346359004623092531255193 1759769253467319398441395)
            ·
              refine ⟨2639653880200979097662093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759769253467319398441395 2639653880200979097662093)
              ·
                refine ⟨989870205075367161623285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2639653880200979097662093 989870205075367161623285)
                ·
                  refine ⟨92800331725815671402183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 989870205075367161623285 92800331725815671402183)
                  ·
                    rfl

theorem cell21_406638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_406638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406638 prefixEnd_406638 := by exact prefixLift 406638
  have htrace : WordTrace (prefixWord ++ tailWord_406638) baseStart_406638 baseEnd_406638 := by
    simpa [prefixWord, tailWord_406638, baseEnd_406638] using wordTrace_append hprefix tailTrace_406638
  have hstable : (prefixWord ++ tailWord_406638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406638).length < 2 ^ (prefixWord ++ tailWord_406638).sum := by decide
  have hdescent : baseEnd_406638 < baseStart_406638 := by decide
  rcases family_descends (prefixWord ++ tailWord_406638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406835 : List Nat := [1, 1, 1, 2, 5, 2, 4, 5]
def baseStart_406835 : Nat := 118140960795 + 406835 * 2 ^ 59
def prefixEnd_406835 : Nat := 4983230072969 + 3 ^ 40 * 406835 * 2
def baseEnd_406835 : Nat := 30948429936595702206149

theorem tailTrace_406835 : CollatzResearch.WordTrace tailWord_406835 prefixEnd_406835 30948429936595702206149 := by
  unfold tailWord_406835
  simp only [CollatzResearch.WordTrace]
  refine ⟨14838491481113751731373959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9892327654075834487582639 14838491481113751731373959)
  ·
    refine ⟨22257737221670627597060939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14838491481113751731373959 22257737221670627597060939)
    ·
      refine ⟨33386605832505941395591409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22257737221670627597060939 33386605832505941395591409)
      ·
        refine ⟨25039954374379456046693557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33386605832505941395591409 25039954374379456046693557)
        ·
          refine ⟨2347495722598074004377521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25039954374379456046693557 2347495722598074004377521)
          ·
            refine ⟨1760621791948555503283141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2347495722598074004377521 1760621791948555503283141)
            ·
              refine ⟨330116585990354156865589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1760621791948555503283141 330116585990354156865589)
              ·
                refine ⟨30948429936595702206149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 330116585990354156865589 30948429936595702206149)
                ·
                  rfl

theorem cell21_406835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 5].length) (baseStart_406835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406835 prefixEnd_406835 := by exact prefixLift 406835
  have htrace : WordTrace (prefixWord ++ tailWord_406835) baseStart_406835 baseEnd_406835 := by
    simpa [prefixWord, tailWord_406835, baseEnd_406835] using wordTrace_append hprefix tailTrace_406835
  have hstable : (prefixWord ++ tailWord_406835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406835).length < 2 ^ (prefixWord ++ tailWord_406835).sum := by decide
  have hdescent : baseEnd_406835 < baseStart_406835 := by decide
  rcases family_descends (prefixWord ++ tailWord_406835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406841 : List Nat := [1, 2, 1, 6, 3, 1, 1, 3, 3]
def baseStart_406841 : Nat := 118140960795 + 406841 * 2 ^ 59
def prefixEnd_406841 : Nat := 4983230072969 + 3 ^ 40 * 406841 * 2
def baseEnd_406841 : Nat := 92846659091532429518435

theorem tailTrace_406841 : CollatzResearch.WordTrace tailWord_406841 prefixEnd_406841 92846659091532429518435 := by
  unfold tailWord_406841
  simp only [CollatzResearch.WordTrace]
  refine ⟨14838710319092014756092377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9892473546061343170728251 14838710319092014756092377)
  ·
    refine ⟨11129032739319011067069283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14838710319092014756092377 11129032739319011067069283)
    ·
      refine ⟨16693549108978516600603925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11129032739319011067069283 16693549108978516600603925)
      ·
        refine ⟨782510114483367965653309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16693549108978516600603925 782510114483367965653309)
        ·
          refine ⟨293441292931262987119991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 782510114483367965653309 293441292931262987119991)
          ·
            refine ⟨440161939396894480679987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293441292931262987119991 440161939396894480679987)
            ·
              refine ⟨660242909095341721019981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440161939396894480679987 660242909095341721019981)
              ·
                refine ⟨247591090910753145382493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 660242909095341721019981 247591090910753145382493)
                ·
                  refine ⟨92846659091532429518435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247591090910753145382493 92846659091532429518435)
                  ·
                    rfl

theorem cell21_406841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 3].length) (baseStart_406841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406841 prefixEnd_406841 := by exact prefixLift 406841
  have htrace : WordTrace (prefixWord ++ tailWord_406841) baseStart_406841 baseEnd_406841 := by
    simpa [prefixWord, tailWord_406841, baseEnd_406841] using wordTrace_append hprefix tailTrace_406841
  have hstable : (prefixWord ++ tailWord_406841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406841).length < 2 ^ (prefixWord ++ tailWord_406841).sum := by decide
  have hdescent : baseEnd_406841 < baseStart_406841 := by decide
  rcases family_descends (prefixWord ++ tailWord_406841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406852 : List Nat := [2, 3, 4, 1, 1, 3, 7]
def baseStart_406852 : Nat := 118140960795 + 406852 * 2 ^ 59
def prefixEnd_406852 : Nat := 4983230072969 + 3 ^ 40 * 406852 * 2
def baseEnd_406852 : Nat := 10316574382377650537231

theorem tailTrace_406852 : CollatzResearch.WordTrace tailWord_406852 prefixEnd_406852 10316574382377650537231 := by
  unfold tailWord_406852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7419555761026081817371405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9892741014701442423161873 7419555761026081817371405)
  ·
    refine ⟨2782333410384780681514277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7419555761026081817371405 2782333410384780681514277)
    ·
      refine ⟨521687514447146377783927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2782333410384780681514277 521687514447146377783927)
      ·
        refine ⟨782531271670719566675891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521687514447146377783927 782531271670719566675891)
        ·
          refine ⟨1173796907506079350013837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782531271670719566675891 1173796907506079350013837)
          ·
            refine ⟨440173840314779756255189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1173796907506079350013837 440173840314779756255189)
            ·
              refine ⟨10316574382377650537231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 440173840314779756255189 10316574382377650537231)
              ·
                rfl

theorem cell21_406852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 7].length) (baseStart_406852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406852 prefixEnd_406852 := by exact prefixLift 406852
  have htrace : WordTrace (prefixWord ++ tailWord_406852) baseStart_406852 baseEnd_406852 := by
    simpa [prefixWord, tailWord_406852, baseEnd_406852] using wordTrace_append hprefix tailTrace_406852
  have hstable : (prefixWord ++ tailWord_406852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406852).length < 2 ^ (prefixWord ++ tailWord_406852).sum := by decide
  have hdescent : baseEnd_406852 < baseStart_406852 := by decide
  rcases family_descends (prefixWord ++ tailWord_406852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406914 : List Nat := [3, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_406914 : Nat := 118140960795 + 406914 * 2 ^ 59
def prefixEnd_406914 : Nat := 4983230072969 + 3 ^ 40 * 406914 * 2
def baseEnd_406914 : Nat := 92863318686100524801619

theorem tailTrace_406914 : CollatzResearch.WordTrace tailWord_406914 prefixEnd_406914 92863318686100524801619 := by
  unfold tailWord_406914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3710343211956887055874949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9894248565218365482333197 3710343211956887055874949)
  ·
    refine ⟨695689352241916322976553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3710343211956887055874949 695689352241916322976553)
    ·
      refine ⟨521767014181437242232415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 695689352241916322976553 521767014181437242232415)
      ·
        refine ⟨782650521272155863348623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521767014181437242232415 782650521272155863348623)
        ·
          refine ⟨1173975781908233795022935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782650521272155863348623 1173975781908233795022935)
          ·
            refine ⟨1760963672862350692534403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173975781908233795022935 1760963672862350692534403)
            ·
              refine ⟨2641445509293526038801605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760963672862350692534403 2641445509293526038801605)
              ·
                refine ⟨495271032992536132275301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2641445509293526038801605 495271032992536132275301)
                ·
                  refine ⟨92863318686100524801619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 495271032992536132275301 92863318686100524801619)
                  ·
                    rfl

theorem cell21_406914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_406914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_406914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_406914 prefixEnd_406914 := by exact prefixLift 406914
  have htrace : WordTrace (prefixWord ++ tailWord_406914) baseStart_406914 baseEnd_406914 := by
    simpa [prefixWord, tailWord_406914, baseEnd_406914] using wordTrace_append hprefix tailTrace_406914
  have hstable : (prefixWord ++ tailWord_406914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406914).length < 2 ^ (prefixWord ++ tailWord_406914).sum := by decide
  have hdescent : baseEnd_406914 < baseStart_406914 := by decide
  rcases family_descends (prefixWord ++ tailWord_406914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407001 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 5]
def baseStart_407001 : Nat := 118140960795 + 407001 * 2 ^ 59
def prefixEnd_407001 : Nat := 4983230072969 + 3 ^ 40 * 407001 * 2
def baseEnd_407001 : Nat := 92883173271407706851441

theorem tailTrace_407001 : CollatzResearch.WordTrace tailWord_407001 prefixEnd_407001 92883173271407706851441 := by
  unfold tailWord_407001
  simp only [CollatzResearch.WordTrace]
  refine ⟨14844545998512362081916857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9896363999008241387944571 14844545998512362081916857)
  ·
    refine ⟨11133409498884271561437643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14844545998512362081916857 11133409498884271561437643)
    ·
      refine ⟨16700114248326407342156465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11133409498884271561437643 16700114248326407342156465)
      ·
        refine ⟨12525085686244805506617349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16700114248326407342156465 12525085686244805506617349)
        ·
          refine ⟨2348453566170901032490753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12525085686244805506617349 2348453566170901032490753)
          ·
            refine ⟨1761340174628175774368065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2348453566170901032490753 1761340174628175774368065)
            ·
              refine ⟨1321005130971131830776049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1761340174628175774368065 1321005130971131830776049)
              ·
                refine ⟨990753848228348873082037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1321005130971131830776049 990753848228348873082037)
                ·
                  refine ⟨92883173271407706851441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 990753848228348873082037 92883173271407706851441)
                  ·
                    rfl

theorem cell21_407001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_407001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407001 prefixEnd_407001 := by exact prefixLift 407001
  have htrace : WordTrace (prefixWord ++ tailWord_407001) baseStart_407001 baseEnd_407001 := by
    simpa [prefixWord, tailWord_407001, baseEnd_407001] using wordTrace_append hprefix tailTrace_407001
  have hstable : (prefixWord ++ tailWord_407001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407001).length < 2 ^ (prefixWord ++ tailWord_407001).sum := by decide
  have hdescent : baseEnd_407001 < baseStart_407001 := by decide
  rcases family_descends (prefixWord ++ tailWord_407001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407136 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_407136 : Nat := 118140960795 + 407136 * 2 ^ 59
def prefixEnd_407136 : Nat := 4983230072969 + 3 ^ 40 * 407136 * 2
def baseEnd_407136 : Nat := 92913982110677472101165

theorem tailTrace_407136 : CollatzResearch.WordTrace tailWord_407136 prefixEnd_407136 92913982110677472101165 := by
  unfold tailWord_407136
  simp only [CollatzResearch.WordTrace]
  refine ⟨7424734926511640069040631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9899646568682186758720841 7424734926511640069040631)
  ·
    refine ⟨11137102389767460103560947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7424734926511640069040631 11137102389767460103560947)
    ·
      refine ⟨16705653584651190155341421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11137102389767460103560947 16705653584651190155341421)
      ·
        refine ⟨6264620094244196308253033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16705653584651190155341421 6264620094244196308253033)
        ·
          refine ⟨4698465070683147231189775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6264620094244196308253033 4698465070683147231189775)
          ·
            refine ⟨7047697606024720846784663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4698465070683147231189775 7047697606024720846784663)
            ·
              refine ⟨10571546409037081270176995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7047697606024720846784663 10571546409037081270176995)
              ·
                refine ⟨15857319613555621905265493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10571546409037081270176995 15857319613555621905265493)
                ·
                  refine ⟨92913982110677472101165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15857319613555621905265493 92913982110677472101165)
                  ·
                    rfl

theorem cell21_407136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_407136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407136 prefixEnd_407136 := by exact prefixLift 407136
  have htrace : WordTrace (prefixWord ++ tailWord_407136) baseStart_407136 baseEnd_407136 := by
    simpa [prefixWord, tailWord_407136, baseEnd_407136] using wordTrace_append hprefix tailTrace_407136
  have hstable : (prefixWord ++ tailWord_407136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407136).length < 2 ^ (prefixWord ++ tailWord_407136).sum := by decide
  have hdescent : baseEnd_407136 < baseStart_407136 := by decide
  rcases family_descends (prefixWord ++ tailWord_407136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407246 : List Nat := [4, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_407246 : Nat := 118140960795 + 407246 * 2 ^ 59
def prefixEnd_407246 : Nat := 4983230072969 + 3 ^ 40 * 407246 * 2
def baseEnd_407246 : Nat := 92939085609341725267607

theorem tailTrace_407246 : CollatzResearch.WordTrace tailWord_407246 prefixEnd_407246 92939085609341725267607 := by
  unfold tailWord_407246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1856685235328096115573199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9902321255083179283057061 1856685235328096115573199)
  ·
    refine ⟨2785027852992144173359799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1856685235328096115573199 2785027852992144173359799)
    ·
      refine ⟨4177541779488216260039699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2785027852992144173359799 4177541779488216260039699)
      ·
        refine ⟨6266312669232324390059549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4177541779488216260039699 6266312669232324390059549)
        ·
          refine ⟨2349867250962121646272331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6266312669232324390059549 2349867250962121646272331)
          ·
            refine ⟨3524800876443182469408497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349867250962121646272331 3524800876443182469408497)
            ·
              refine ⟨2643600657332386852056373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524800876443182469408497 2643600657332386852056373)
              ·
                refine ⟨247837561624911267380285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2643600657332386852056373 247837561624911267380285)
                ·
                  refine ⟨92939085609341725267607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247837561624911267380285 92939085609341725267607)
                  ·
                    rfl

theorem cell21_407246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_407246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407246 prefixEnd_407246 := by exact prefixLift 407246
  have htrace : WordTrace (prefixWord ++ tailWord_407246) baseStart_407246 baseEnd_407246 := by
    simpa [prefixWord, tailWord_407246, baseEnd_407246] using wordTrace_append hprefix tailTrace_407246
  have hstable : (prefixWord ++ tailWord_407246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407246).length < 2 ^ (prefixWord ++ tailWord_407246).sum := by decide
  have hdescent : baseEnd_407246 < baseStart_407246 := by decide
  rcases family_descends (prefixWord ++ tailWord_407246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407257 : List Nat := [1, 2, 1, 2, 3, 12]
def baseStart_407257 : Nat := 118140960795 + 407257 * 2 ^ 59
def prefixEnd_407257 : Nat := 4983230072969 + 3 ^ 40 * 407257 * 2
def baseEnd_407257 : Nat := 3442281331822524095713

theorem tailTrace_407257 : CollatzResearch.WordTrace tailWord_407257 prefixEnd_407257 3442281331822524095713 := by
  unfold tailWord_407257
  simp only [CollatzResearch.WordTrace]
  refine ⟨14853883085584917803236025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9902588723723278535490683 14853883085584917803236025)
  ·
    refine ⟨11140412314188688352427019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14853883085584917803236025 11140412314188688352427019)
    ·
      refine ⟨16710618471283032528640529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11140412314188688352427019 16710618471283032528640529)
      ·
        refine ⟨12532963853462274396480397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16710618471283032528640529 12532963853462274396480397)
        ·
          refine ⟨4699861445048352898680149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12532963853462274396480397 4699861445048352898680149)
          ·
            refine ⟨3442281331822524095713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4699861445048352898680149 3442281331822524095713)
            ·
              rfl

theorem cell21_407257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 12].length) (baseStart_407257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407257 prefixEnd_407257 := by exact prefixLift 407257
  have htrace : WordTrace (prefixWord ++ tailWord_407257) baseStart_407257 baseEnd_407257 := by
    simpa [prefixWord, tailWord_407257, baseEnd_407257] using wordTrace_append hprefix tailTrace_407257
  have hstable : (prefixWord ++ tailWord_407257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407257).length < 2 ^ (prefixWord ++ tailWord_407257).sum := by decide
  have hdescent : baseEnd_407257 < baseStart_407257 := by decide
  rcases family_descends (prefixWord ++ tailWord_407257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407274 : List Nat := [3, 1, 3, 1, 1, 1, 5, 6]
def baseStart_407274 : Nat := 118140960795 + 407274 * 2 ^ 59
def prefixEnd_407274 : Nat := 4983230072969 + 3 ^ 40 * 407274 * 2
def baseEnd_407274 : Nat := 30981825196939966266961

theorem tailTrace_407274 : CollatzResearch.WordTrace tailWord_407274 prefixEnd_407274 30981825196939966266961 := by
  unfold tailWord_407274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3713625781630832426651219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9903002084348886471069917 3713625781630832426651219)
  ·
    refine ⟨5570438672446248639976829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3713625781630832426651219 5570438672446248639976829)
    ·
      refine ⟨2088914502167343239991311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5570438672446248639976829 2088914502167343239991311)
      ·
        refine ⟨3133371753251014859986967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2088914502167343239991311 3133371753251014859986967)
        ·
          refine ⟨4700057629876522289980451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3133371753251014859986967 4700057629876522289980451)
          ·
            refine ⟨7050086444814783434970677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700057629876522289980451 7050086444814783434970677)
            ·
              refine ⟨660945604201385947028501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7050086444814783434970677 660945604201385947028501)
              ·
                refine ⟨30981825196939966266961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 660945604201385947028501 30981825196939966266961)
                ·
                  rfl

theorem cell21_407274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_407274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407274 prefixEnd_407274 := by exact prefixLift 407274
  have htrace : WordTrace (prefixWord ++ tailWord_407274) baseStart_407274 baseEnd_407274 := by
    simpa [prefixWord, tailWord_407274, baseEnd_407274] using wordTrace_append hprefix tailTrace_407274
  have hstable : (prefixWord ++ tailWord_407274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407274).length < 2 ^ (prefixWord ++ tailWord_407274).sum := by decide
  have hdescent : baseEnd_407274 < baseStart_407274 := by decide
  rcases family_descends (prefixWord ++ tailWord_407274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407322 : List Nat := [3, 1, 1, 3, 2, 2, 2, 4, 3]
def baseStart_407322 : Nat := 118140960795 + 407322 * 2 ^ 59
def prefixEnd_407322 : Nat := 4983230072969 + 3 ^ 40 * 407322 * 2
def baseEnd_407322 : Nat := 92956429844782482000785

theorem tailTrace_407322 : CollatzResearch.WordTrace tailWord_407322 prefixEnd_407322 92956429844782482000785 := by
  unfold tailWord_407322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3714063457587358476088055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9904169220232955936234813 3714063457587358476088055)
  ·
    refine ⟨5571095186381037714132083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3714063457587358476088055 5571095186381037714132083)
    ·
      refine ⟨8356642779571556571198125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5571095186381037714132083 8356642779571556571198125)
      ·
        refine ⟨3133741042339333714199297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8356642779571556571198125 3133741042339333714199297)
        ·
          refine ⟨2350305781754500285649473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3133741042339333714199297 2350305781754500285649473)
          ·
            refine ⟨1762729336315875214237105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2350305781754500285649473 1762729336315875214237105)
            ·
              refine ⟨1322047002236906410677829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762729336315875214237105 1322047002236906410677829)
              ·
                refine ⟨247883812919419952002093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1322047002236906410677829 247883812919419952002093)
                ·
                  refine ⟨92956429844782482000785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247883812919419952002093 92956429844782482000785)
                  ·
                    rfl

theorem cell21_407322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_407322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407322 prefixEnd_407322 := by exact prefixLift 407322
  have htrace : WordTrace (prefixWord ++ tailWord_407322) baseStart_407322 baseEnd_407322 := by
    simpa [prefixWord, tailWord_407322, baseEnd_407322] using wordTrace_append hprefix tailTrace_407322
  have hstable : (prefixWord ++ tailWord_407322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407322).length < 2 ^ (prefixWord ++ tailWord_407322).sum := by decide
  have hdescent : baseEnd_407322 < baseStart_407322 := by decide
  rcases family_descends (prefixWord ++ tailWord_407322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407381 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 5]
def baseStart_407381 : Nat := 118140960795 + 407381 * 2 ^ 59
def prefixEnd_407381 : Nat := 4983230072969 + 3 ^ 40 * 407381 * 2
def baseEnd_407381 : Nat := 92969894448611490517331

theorem tailTrace_407381 : CollatzResearch.WordTrace tailWord_407381 prefixEnd_407381 92969894448611490517331 := by
  unfold tailWord_407381
  simp only [CollatzResearch.WordTrace]
  refine ⟨14858405737135686980749997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9905603824757124653833331 14858405737135686980749997)
  ·
    refine ⟨5571902151425882617781249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14858405737135686980749997 5571902151425882617781249)
    ·
      refine ⟨4178926613569411963335937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5571902151425882617781249 4178926613569411963335937)
      ·
        refine ⟨3134194960177058972501953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4178926613569411963335937 3134194960177058972501953)
        ·
          refine ⟨2350646220132794229376465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3134194960177058972501953 2350646220132794229376465)
          ·
            refine ⟨1762984665099595672032349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2350646220132794229376465 1762984665099595672032349)
            ·
              refine ⟨661119249412348377012131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1762984665099595672032349 661119249412348377012131)
              ·
                refine ⟨991678874118522565518197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661119249412348377012131 991678874118522565518197)
                ·
                  refine ⟨92969894448611490517331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 991678874118522565518197 92969894448611490517331)
                  ·
                    rfl

theorem cell21_407381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_407381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407381 prefixEnd_407381 := by exact prefixLift 407381
  have htrace : WordTrace (prefixWord ++ tailWord_407381) baseStart_407381 baseEnd_407381 := by
    simpa [prefixWord, tailWord_407381, baseEnd_407381] using wordTrace_append hprefix tailTrace_407381
  have hstable : (prefixWord ++ tailWord_407381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407381).length < 2 ^ (prefixWord ++ tailWord_407381).sum := by decide
  have hdescent : baseEnd_407381 < baseStart_407381 := by decide
  rcases family_descends (prefixWord ++ tailWord_407381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407409 : List Nat := [1, 2, 2, 2, 1, 3, 1, 9]
def baseStart_407409 : Nat := 118140960795 + 407409 * 2 ^ 59
def prefixEnd_407409 : Nat := 4983230072969 + 3 ^ 40 * 407409 * 2
def baseEnd_407409 : Nat := 30992094810029888016869

theorem tailTrace_407409 : CollatzResearch.WordTrace tailWord_407409 prefixEnd_407409 30992094810029888016869 := by
  unfold tailWord_407409
  simp only [CollatzResearch.WordTrace]
  refine ⟨14859426981034247762769281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9906284654022831841846187 14859426981034247762769281)
  ·
    refine ⟨11144570235775685822076961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14859426981034247762769281 11144570235775685822076961)
    ·
      refine ⟨8358427676831764366557721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11144570235775685822076961 8358427676831764366557721)
      ·
        refine ⟨6268820757623823274918291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8358427676831764366557721 6268820757623823274918291)
        ·
          refine ⟨9403231136435734912377437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6268820757623823274918291 9403231136435734912377437)
          ·
            refine ⟨3526211676163400592141539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9403231136435734912377437 3526211676163400592141539)
            ·
              refine ⟨5289317514245100888212309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3526211676163400592141539 5289317514245100888212309)
              ·
                refine ⟨30992094810029888016869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5289317514245100888212309 30992094810029888016869)
                ·
                  rfl

theorem cell21_407409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 9].length) (baseStart_407409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407409 prefixEnd_407409 := by exact prefixLift 407409
  have htrace : WordTrace (prefixWord ++ tailWord_407409) baseStart_407409 baseEnd_407409 := by
    simpa [prefixWord, tailWord_407409, baseEnd_407409] using wordTrace_append hprefix tailTrace_407409
  have hstable : (prefixWord ++ tailWord_407409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407409).length < 2 ^ (prefixWord ++ tailWord_407409).sum := by decide
  have hdescent : baseEnd_407409 < baseStart_407409 := by decide
  rcases family_descends (prefixWord ++ tailWord_407409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407426 : List Nat := [3, 4, 2, 12]
def baseStart_407426 : Nat := 118140960795 + 407426 * 2 ^ 59
def prefixEnd_407426 : Nat := 4983230072969 + 3 ^ 40 * 407426 * 2
def baseEnd_407426 : Nat := 382634420007001696573

theorem tailTrace_407426 : CollatzResearch.WordTrace tailWord_407426 prefixEnd_407426 382634420007001696573 := by
  unfold tailWord_407426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715011755493164916534533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9906698014648439777425421 3715011755493164916534533)
  ·
    refine ⟨696564704154968421850225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3715011755493164916534533 696564704154968421850225)
    ·
      refine ⟨522423528116226316387669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 696564704154968421850225 522423528116226316387669)
      ·
        refine ⟨382634420007001696573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 522423528116226316387669 382634420007001696573)
        ·
          rfl

theorem cell21_407426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 12].length) (baseStart_407426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407426 prefixEnd_407426 := by exact prefixLift 407426
  have htrace : WordTrace (prefixWord ++ tailWord_407426) baseStart_407426 baseEnd_407426 := by
    simpa [prefixWord, tailWord_407426, baseEnd_407426] using wordTrace_append hprefix tailTrace_407426
  have hstable : (prefixWord ++ tailWord_407426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407426).length < 2 ^ (prefixWord ++ tailWord_407426).sum := by decide
  have hdescent : baseEnd_407426 < baseStart_407426 := by decide
  rcases family_descends (prefixWord ++ tailWord_407426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407432 : List Nat := [2, 1, 3, 3, 3, 2, 2, 2, 3]
def baseStart_407432 : Nat := 118140960795 + 407432 * 2 ^ 59
def prefixEnd_407432 : Nat := 4983230072969 + 3 ^ 40 * 407432 * 2
def baseEnd_407432 : Nat := 92981533343446735167227

theorem tailTrace_407432 : CollatzResearch.WordTrace tailWord_407432 prefixEnd_407432 92981533343446735167227 := by
  unfold tailWord_407432
  simp only [CollatzResearch.WordTrace]
  refine ⟨7430132929975461345428275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9906843906633948460571033 7430132929975461345428275)
  ·
    refine ⟨11145199394963192018142413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7430132929975461345428275 11145199394963192018142413)
    ·
      refine ⟨4179449773111197006803405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11145199394963192018142413 4179449773111197006803405)
      ·
        refine ⟨1567293664916698877551277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4179449773111197006803405 1567293664916698877551277)
        ·
          refine ⟨587735124343762079081729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1567293664916698877551277 587735124343762079081729)
          ·
            refine ⟨440801343257821559311297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 587735124343762079081729 440801343257821559311297)
            ·
              refine ⟨330601007443366169483473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440801343257821559311297 330601007443366169483473)
              ·
                refine ⟨247950755582524627112605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330601007443366169483473 247950755582524627112605)
                ·
                  refine ⟨92981533343446735167227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247950755582524627112605 92981533343446735167227)
                  ·
                    rfl

theorem cell21_407432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 2, 3].length) (baseStart_407432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407432 prefixEnd_407432 := by exact prefixLift 407432
  have htrace : WordTrace (prefixWord ++ tailWord_407432) baseStart_407432 baseEnd_407432 := by
    simpa [prefixWord, tailWord_407432, baseEnd_407432] using wordTrace_append hprefix tailTrace_407432
  have hstable : (prefixWord ++ tailWord_407432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407432).length < 2 ^ (prefixWord ++ tailWord_407432).sum := by decide
  have hdescent : baseEnd_407432 < baseStart_407432 := by decide
  rcases family_descends (prefixWord ++ tailWord_407432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407519 : List Nat := [1, 1, 2, 3, 4, 3, 2, 5]
def baseStart_407519 : Nat := 118140960795 + 407519 * 2 ^ 59
def prefixEnd_407519 : Nat := 4983230072969 + 3 ^ 40 * 407519 * 2
def baseEnd_407519 : Nat := 31000462642917972405683

theorem tailTrace_407519 : CollatzResearch.WordTrace tailWord_407519 prefixEnd_407519 31000462642917972405683 := by
  unfold tailWord_407519
  simp only [CollatzResearch.WordTrace]
  refine ⟨14863439010635736549273611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9908959340423824366182407 14863439010635736549273611)
  ·
    refine ⟨22295158515953604823910417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14863439010635736549273611 22295158515953604823910417)
    ·
      refine ⟨16721368886965203617932813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22295158515953604823910417 16721368886965203617932813)
      ·
        refine ⟨6270513332611951356724805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16721368886965203617932813 6270513332611951356724805)
        ·
          refine ⟨1175721249864740879385901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6270513332611951356724805 1175721249864740879385901)
          ·
            refine ⟨440895468699277829769713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1175721249864740879385901 440895468699277829769713)
            ·
              refine ⟨330671601524458372327285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440895468699277829769713 330671601524458372327285)
              ·
                refine ⟨31000462642917972405683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 330671601524458372327285 31000462642917972405683)
                ·
                  rfl

theorem cell21_407519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 5].length) (baseStart_407519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407519 prefixEnd_407519 := by exact prefixLift 407519
  have htrace : WordTrace (prefixWord ++ tailWord_407519) baseStart_407519 baseEnd_407519 := by
    simpa [prefixWord, tailWord_407519, baseEnd_407519] using wordTrace_append hprefix tailTrace_407519
  have hstable : (prefixWord ++ tailWord_407519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407519).length < 2 ^ (prefixWord ++ tailWord_407519).sum := by decide
  have hdescent : baseEnd_407519 < baseStart_407519 := by decide
  rcases family_descends (prefixWord ++ tailWord_407519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407550 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_407550 : Nat := 118140960795 + 407550 * 2 ^ 59
def prefixEnd_407550 : Nat := 4983230072969 + 3 ^ 40 * 407550 * 2
def baseEnd_407550 : Nat := 93008462551104752200319

theorem tailTrace_407550 : CollatzResearch.WordTrace tailWord_407550 prefixEnd_407550 93008462551104752200319 := by
  unfold tailWord_407550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858071209190428605456513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9909713115682285895768069 1858071209190428605456513)
  ·
    refine ⟨1393553406892821454092385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1858071209190428605456513 1393553406892821454092385)
    ·
      refine ⟨1045165055169616090569289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1393553406892821454092385 1045165055169616090569289)
      ·
        refine ⟨783873791377212067926967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1045165055169616090569289 783873791377212067926967)
        ·
          refine ⟨1175810687065818101890451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783873791377212067926967 1175810687065818101890451)
          ·
            refine ⟨1763716030598727152835677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175810687065818101890451 1763716030598727152835677)
            ·
              refine ⟨661393511474522682313379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1763716030598727152835677 661393511474522682313379)
              ·
                refine ⟨992090267211784023470069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661393511474522682313379 992090267211784023470069)
                ·
                  refine ⟨93008462551104752200319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 992090267211784023470069 93008462551104752200319)
                  ·
                    rfl

theorem cell21_407550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_407550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407550 prefixEnd_407550 := by exact prefixLift 407550
  have htrace : WordTrace (prefixWord ++ tailWord_407550) baseStart_407550 baseEnd_407550 := by
    simpa [prefixWord, tailWord_407550, baseEnd_407550] using wordTrace_append hprefix tailTrace_407550
  have hstable : (prefixWord ++ tailWord_407550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407550).length < 2 ^ (prefixWord ++ tailWord_407550).sum := by decide
  have hdescent : baseEnd_407550 < baseStart_407550 := by decide
  rcases family_descends (prefixWord ++ tailWord_407550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407623 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 4]
def baseStart_407623 : Nat := 118140960795 + 407623 * 2 ^ 59
def prefixEnd_407623 : Nat := 4983230072969 + 3 ^ 40 * 407623 * 2
def baseEnd_407623 : Nat := 93025122145672847483503

theorem tailTrace_407623 : CollatzResearch.WordTrace tailWord_407623 prefixEnd_407623 93025122145672847483503 := by
  unfold tailWord_407623
  simp only [CollatzResearch.WordTrace]
  refine ⟨14867232202258962311059523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9911488134839308207373015 14867232202258962311059523)
  ·
    refine ⟨22300848303388443466589285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14867232202258962311059523 22300848303388443466589285)
    ·
      refine ⟨4181409056885333149985491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22300848303388443466589285 4181409056885333149985491)
      ·
        refine ⟨6272113585327999724978237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4181409056885333149985491 6272113585327999724978237)
        ·
          refine ⟨2352042594497999896866839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6272113585327999724978237 2352042594497999896866839)
          ·
            refine ⟨3528063891746999845300259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352042594497999896866839 3528063891746999845300259)
            ·
              refine ⟨5292095837620499767950389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528063891746999845300259 5292095837620499767950389)
              ·
                refine ⟨496133984776921853245349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5292095837620499767950389 496133984776921853245349)
                ·
                  refine ⟨93025122145672847483503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 496133984776921853245349 93025122145672847483503)
                  ·
                    rfl

theorem cell21_407623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 4].length) (baseStart_407623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407623 prefixEnd_407623 := by exact prefixLift 407623
  have htrace : WordTrace (prefixWord ++ tailWord_407623) baseStart_407623 baseEnd_407623 := by
    simpa [prefixWord, tailWord_407623, baseEnd_407623] using wordTrace_append hprefix tailTrace_407623
  have hstable : (prefixWord ++ tailWord_407623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407623).length < 2 ^ (prefixWord ++ tailWord_407623).sum := by decide
  have hdescent : baseEnd_407623 < baseStart_407623 := by decide
  rcases family_descends (prefixWord ++ tailWord_407623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407713 : List Nat := [1, 2, 3, 3, 1, 2, 9]
def baseStart_407713 : Nat := 118140960795 + 407713 * 2 ^ 59
def prefixEnd_407713 : Nat := 4983230072969 + 3 ^ 40 * 407713 * 2
def baseEnd_407713 : Nat := 10338406819094743442591

theorem tailTrace_407713 : CollatzResearch.WordTrace tailWord_407713 prefixEnd_407713 10338406819094743442591 := by
  unfold tailWord_407713
  simp only [CollatzResearch.WordTrace]
  refine ⟨14870514771932907681835793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9913676514621938454557195 14870514771932907681835793)
  ·
    refine ⟨11152886078949680761376845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14870514771932907681835793 11152886078949680761376845)
    ·
      refine ⟨4182332279606130285516317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11152886078949680761376845 4182332279606130285516317)
      ·
        refine ⟨1568374604852298857068619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4182332279606130285516317 1568374604852298857068619)
        ·
          refine ⟨2352561907278448285602929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568374604852298857068619 2352561907278448285602929)
          ·
            refine ⟨1764421430458836214202197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2352561907278448285602929 1764421430458836214202197)
            ·
              refine ⟨10338406819094743442591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1764421430458836214202197 10338406819094743442591)
              ·
                rfl

theorem cell21_407713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 9].length) (baseStart_407713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407713 prefixEnd_407713 := by exact prefixLift 407713
  have htrace : WordTrace (prefixWord ++ tailWord_407713) baseStart_407713 baseEnd_407713 := by
    simpa [prefixWord, tailWord_407713, baseEnd_407713] using wordTrace_append hprefix tailTrace_407713
  have hstable : (prefixWord ++ tailWord_407713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407713).length < 2 ^ (prefixWord ++ tailWord_407713).sum := by decide
  have hdescent : baseEnd_407713 < baseStart_407713 := by decide
  rcases family_descends (prefixWord ++ tailWord_407713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407719 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 5]
def baseStart_407719 : Nat := 118140960795 + 407719 * 2 ^ 59
def prefixEnd_407719 : Nat := 4983230072969 + 3 ^ 40 * 407719 * 2
def baseEnd_407719 : Nat := 93047030653598013883307

theorem tailTrace_407719 : CollatzResearch.WordTrace tailWord_407719 prefixEnd_407719 93047030653598013883307 := by
  unfold tailWord_407719
  simp only [CollatzResearch.WordTrace]
  refine ⟨14870733609911170706554211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9913822406607447137702807 14870733609911170706554211)
  ·
    refine ⟨22306100414866756059831317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14870733609911170706554211 22306100414866756059831317)
    ·
      refine ⟨1045598456946879190304593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22306100414866756059831317 1045598456946879190304593)
      ·
        refine ⟨784198842710159392728445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1045598456946879190304593 784198842710159392728445)
        ·
          refine ⟨294074566016309772273167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 784198842710159392728445 294074566016309772273167)
          ·
            refine ⟨441111849024464658409751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294074566016309772273167 441111849024464658409751)
            ·
              refine ⟨661667773536696987614627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441111849024464658409751 661667773536696987614627)
              ·
                refine ⟨992501660305045481421941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 661667773536696987614627 992501660305045481421941)
                ·
                  refine ⟨93047030653598013883307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 992501660305045481421941 93047030653598013883307)
                  ·
                    rfl

theorem cell21_407719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 5].length) (baseStart_407719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407719 prefixEnd_407719 := by exact prefixLift 407719
  have htrace : WordTrace (prefixWord ++ tailWord_407719) baseStart_407719 baseEnd_407719 := by
    simpa [prefixWord, tailWord_407719, baseEnd_407719] using wordTrace_append hprefix tailTrace_407719
  have hstable : (prefixWord ++ tailWord_407719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407719).length < 2 ^ (prefixWord ++ tailWord_407719).sum := by decide
  have hdescent : baseEnd_407719 < baseStart_407719 := by decide
  rcases family_descends (prefixWord ++ tailWord_407719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407733 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 4]
def baseStart_407733 : Nat := 118140960795 + 407733 * 2 ^ 59
def prefixEnd_407733 : Nat := 4983230072969 + 3 ^ 40 * 407733 * 2
def baseEnd_407733 : Nat := 93050225644337100649945

theorem tailTrace_407733 : CollatzResearch.WordTrace tailWord_407733 prefixEnd_407733 93050225644337100649945 := by
  unfold tailWord_407733
  simp only [CollatzResearch.WordTrace]
  refine ⟨14871244231860451097563853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9914162821240300731709235 14871244231860451097563853)
  ·
    refine ⟨5576716586947669161586445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14871244231860451097563853 5576716586947669161586445)
    ·
      refine ⟨2091268720105375935594917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5576716586947669161586445 2091268720105375935594917)
      ·
        refine ⟨392112885019757987924047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2091268720105375935594917 392112885019757987924047)
        ·
          refine ⟨588169327529636981886071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392112885019757987924047 588169327529636981886071)
          ·
            refine ⟨882253991294455472829107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588169327529636981886071 882253991294455472829107)
            ·
              refine ⟨1323380986941683209243661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882253991294455472829107 1323380986941683209243661)
              ·
                refine ⟨496267870103131203466373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1323380986941683209243661 496267870103131203466373)
                ·
                  refine ⟨93050225644337100649945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 496267870103131203466373 93050225644337100649945)
                  ·
                    rfl

theorem cell21_407733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_407733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407733 prefixEnd_407733 := by exact prefixLift 407733
  have htrace : WordTrace (prefixWord ++ tailWord_407733) baseStart_407733 baseEnd_407733 := by
    simpa [prefixWord, tailWord_407733, baseEnd_407733] using wordTrace_append hprefix tailTrace_407733
  have hstable : (prefixWord ++ tailWord_407733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407733).length < 2 ^ (prefixWord ++ tailWord_407733).sum := by decide
  have hdescent : baseEnd_407733 < baseStart_407733 := by decide
  rcases family_descends (prefixWord ++ tailWord_407733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407986 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_407986 : Nat := 118140960795 + 407986 * 2 ^ 59
def prefixEnd_407986 : Nat := 4983230072969 + 3 ^ 40 * 407986 * 2
def baseEnd_407986 : Nat := 93107963691264882932761

theorem tailTrace_407986 : CollatzResearch.WordTrace tailWord_407986 prefixEnd_407986 93107963691264882932761 := by
  unfold tailWord_407986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720117974985968826630953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9920314599962583537682541 3720117974985968826630953)
  ·
    refine ⟨2790088481239476619973215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3720117974985968826630953 2790088481239476619973215)
    ·
      refine ⟨4185132721859214929959823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790088481239476619973215 4185132721859214929959823)
      ·
        refine ⟨6277699082788822394939735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185132721859214929959823 6277699082788822394939735)
        ·
          refine ⟨9416548624183233592409603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6277699082788822394939735 9416548624183233592409603)
          ·
            refine ⟨14124822936274850388614405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9416548624183233592409603 14124822936274850388614405)
            ·
              refine ⟨2648404300551534447865201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14124822936274850388614405 2648404300551534447865201)
              ·
                refine ⟨1986303225413650835898901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648404300551534447865201 1986303225413650835898901)
                ·
                  refine ⟨93107963691264882932761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1986303225413650835898901 93107963691264882932761)
                  ·
                    rfl

theorem cell21_407986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_407986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_407986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_407986 prefixEnd_407986 := by exact prefixLift 407986
  have htrace : WordTrace (prefixWord ++ tailWord_407986) baseStart_407986 baseEnd_407986 := by
    simpa [prefixWord, tailWord_407986, baseEnd_407986] using wordTrace_append hprefix tailTrace_407986
  have hstable : (prefixWord ++ tailWord_407986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407986).length < 2 ^ (prefixWord ++ tailWord_407986).sum := by decide
  have hdescent : baseEnd_407986 < baseStart_407986 := by decide
  rcases family_descends (prefixWord ++ tailWord_407986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408065 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 5]
def baseStart_408065 : Nat := 118140960795 + 408065 * 2 ^ 59
def prefixEnd_408065 : Nat := 4983230072969 + 3 ^ 40 * 408065 * 2
def baseEnd_408065 : Nat := 93125992567578301115933

theorem tailTrace_408065 : CollatzResearch.WordTrace tailWord_408065 prefixEnd_408065 93125992567578301115933 := by
  unfold tailWord_408065
  simp only [CollatzResearch.WordTrace]
  refine ⟨14883353266657671798649649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9922235511105114532433099 14883353266657671798649649)
  ·
    refine ⟨11162514949993253848987237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14883353266657671798649649 11162514949993253848987237)
    ·
      refine ⟨2092971553123735096685107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11162514949993253848987237 2092971553123735096685107)
      ·
        refine ⟨3139457329685602645027661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2092971553123735096685107 3139457329685602645027661)
        ·
          refine ⟨1177296498632100991885373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3139457329685602645027661 1177296498632100991885373)
          ·
            refine ⟨441486186987037871957015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1177296498632100991885373 441486186987037871957015)
            ·
              refine ⟨662229280480556807935523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441486186987037871957015 662229280480556807935523)
              ·
                refine ⟨993343920720835211903285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662229280480556807935523 993343920720835211903285)
                ·
                  refine ⟨93125992567578301115933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 993343920720835211903285 93125992567578301115933)
                  ·
                    rfl

theorem cell21_408065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_408065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408065 prefixEnd_408065 := by exact prefixLift 408065
  have htrace : WordTrace (prefixWord ++ tailWord_408065) baseStart_408065 baseEnd_408065 := by
    simpa [prefixWord, tailWord_408065, baseEnd_408065] using wordTrace_append hprefix tailTrace_408065
  have hstable : (prefixWord ++ tailWord_408065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408065).length < 2 ^ (prefixWord ++ tailWord_408065).sum := by decide
  have hdescent : baseEnd_408065 < baseStart_408065 := by decide
  rcases family_descends (prefixWord ++ tailWord_408065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408093 : List Nat := [1, 4, 2, 2, 1, 2, 2, 7]
def baseStart_408093 : Nat := 118140960795 + 408093 * 2 ^ 59
def prefixEnd_408093 : Nat := 4983230072969 + 3 ^ 40 * 408093 * 2
def baseEnd_408093 : Nat := 31044127516352158216403

theorem tailTrace_408093 : CollatzResearch.WordTrace tailWord_408093 prefixEnd_408093 31044127516352158216403 := by
  unfold tailWord_408093
  simp only [CollatzResearch.WordTrace]
  refine ⟨14884374510556232580668933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9922916340370821720445955 14884374510556232580668933)
  ·
    refine ⟨2790820220729293608875425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14884374510556232580668933 2790820220729293608875425)
    ·
      refine ⟨2093115165546970206656569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2790820220729293608875425 2093115165546970206656569)
      ·
        refine ⟨1569836374160227654992427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2093115165546970206656569 1569836374160227654992427)
        ·
          refine ⟨2354754561240341482488641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569836374160227654992427 2354754561240341482488641)
          ·
            refine ⟨1766065920930256111866481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2354754561240341482488641 1766065920930256111866481)
            ·
              refine ⟨1324549440697692083899861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1766065920930256111866481 1324549440697692083899861)
              ·
                refine ⟨31044127516352158216403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1324549440697692083899861 31044127516352158216403)
                ·
                  rfl

theorem cell21_408093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 7].length) (baseStart_408093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408093 prefixEnd_408093 := by exact prefixLift 408093
  have htrace : WordTrace (prefixWord ++ tailWord_408093) baseStart_408093 baseEnd_408093 := by
    simpa [prefixWord, tailWord_408093, baseEnd_408093] using wordTrace_append hprefix tailTrace_408093
  have hstable : (prefixWord ++ tailWord_408093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408093).length < 2 ^ (prefixWord ++ tailWord_408093).sum := by decide
  have hdescent : baseEnd_408093 < baseStart_408093 := by decide
  rcases family_descends (prefixWord ++ tailWord_408093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408110 : List Nat := [4, 1, 3, 1, 4, 8]
def baseStart_408110 : Nat := 118140960795 + 408110 * 2 ^ 59
def prefixEnd_408110 : Nat := 4983230072969 + 3 ^ 40 * 408110 * 2
def baseEnd_408110 : Nat := 3449491191876600846883

theorem tailTrace_408110 : CollatzResearch.WordTrace tailWord_408110 prefixEnd_408110 3449491191876600846883 := by
  unfold tailWord_408110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860624318936830560504723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9923329700996429656025189 1860624318936830560504723)
  ·
    refine ⟨2790936478405245840757085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1860624318936830560504723 2790936478405245840757085)
    ·
      refine ⟨1046601179401967190283907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2790936478405245840757085 1046601179401967190283907)
      ·
        refine ⟨1569901769102950785425861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046601179401967190283907 1569901769102950785425861)
        ·
          refine ⟨294356581706803272267349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1569901769102950785425861 294356581706803272267349)
          ·
            refine ⟨3449491191876600846883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 294356581706803272267349 3449491191876600846883)
            ·
              rfl

theorem cell21_408110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 8].length) (baseStart_408110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408110 prefixEnd_408110 := by exact prefixLift 408110
  have htrace : WordTrace (prefixWord ++ tailWord_408110) baseStart_408110 baseEnd_408110 := by
    simpa [prefixWord, tailWord_408110, baseEnd_408110] using wordTrace_append hprefix tailTrace_408110
  have hstable : (prefixWord ++ tailWord_408110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408110).length < 2 ^ (prefixWord ++ tailWord_408110).sum := by decide
  have hdescent : baseEnd_408110 < baseStart_408110 := by decide
  rcases family_descends (prefixWord ++ tailWord_408110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408141 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 5]
def baseStart_408141 : Nat := 118140960795 + 408141 * 2 ^ 59
def prefixEnd_408141 : Nat := 4983230072969 + 3 ^ 40 * 408141 * 2
def baseEnd_408141 : Nat := 93143336803019057849111

theorem tailTrace_408141 : CollatzResearch.WordTrace tailWord_408141 prefixEnd_408141 93143336803019057849111 := by
  unfold tailWord_408141
  simp only [CollatzResearch.WordTrace]
  refine ⟨14886125214382336778416277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9924083476254891185610851 14886125214382336778416277)
  ·
    refine ⟨697787119424172036488263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14886125214382336778416277 697787119424172036488263)
    ·
      refine ⟨1046680679136258054732395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 697787119424172036488263 1046680679136258054732395)
      ·
        refine ⟨1570021018704387082098593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046680679136258054732395 1570021018704387082098593)
        ·
          refine ⟨1177515764028290311573945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1570021018704387082098593 1177515764028290311573945)
          ·
            refine ⟨883136823021217733680459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1177515764028290311573945 883136823021217733680459)
            ·
              refine ⟨1324705234531826600520689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883136823021217733680459 1324705234531826600520689)
              ·
                refine ⟨993528925898869950390517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1324705234531826600520689 993528925898869950390517)
                ·
                  refine ⟨93143336803019057849111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 993528925898869950390517 93143336803019057849111)
                  ·
                    rfl

theorem cell21_408141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_408141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408141 prefixEnd_408141 := by exact prefixLift 408141
  have htrace : WordTrace (prefixWord ++ tailWord_408141) baseStart_408141 baseEnd_408141 := by
    simpa [prefixWord, tailWord_408141, baseEnd_408141] using wordTrace_append hprefix tailTrace_408141
  have hstable : (prefixWord ++ tailWord_408141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408141).length < 2 ^ (prefixWord ++ tailWord_408141).sum := by decide
  have hdescent : baseEnd_408141 < baseStart_408141 := by decide
  rcases family_descends (prefixWord ++ tailWord_408141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408152 : List Nat := [2, 1, 2, 2, 1, 2, 2, 9]
def baseStart_408152 : Nat := 118140960795 + 408152 * 2 ^ 59
def prefixEnd_408152 : Nat := 4983230072969 + 3 ^ 40 * 408152 * 2
def baseEnd_408152 : Nat := 31048615717628494388585

theorem tailTrace_408152 : CollatzResearch.WordTrace tailWord_408152 prefixEnd_408152 31048615717628494388585 := by
  unfold tailWord_408152
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443263208671242828533355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9924350944894990438044473 7443263208671242828533355)
  ·
    refine ⟨11164894813006864242800033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7443263208671242828533355 11164894813006864242800033)
    ·
      refine ⟨8373671109755148182100025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11164894813006864242800033 8373671109755148182100025)
      ·
        refine ⟨6280253332316361136575019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8373671109755148182100025 6280253332316361136575019)
        ·
          refine ⟨9420379998474541704862529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6280253332316361136575019 9420379998474541704862529)
          ·
            refine ⟨7065284998855906278646897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9420379998474541704862529 7065284998855906278646897)
            ·
              refine ⟨5298963749141929708985173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7065284998855906278646897 5298963749141929708985173)
              ·
                refine ⟨31048615717628494388585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5298963749141929708985173 31048615717628494388585)
                ·
                  rfl

theorem cell21_408152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_408152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408152 prefixEnd_408152 := by exact prefixLift 408152
  have htrace : WordTrace (prefixWord ++ tailWord_408152) baseStart_408152 baseEnd_408152 := by
    simpa [prefixWord, tailWord_408152, baseEnd_408152] using wordTrace_append hprefix tailTrace_408152
  have hstable : (prefixWord ++ tailWord_408152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408152).length < 2 ^ (prefixWord ++ tailWord_408152).sum := by decide
  have hdescent : baseEnd_408152 < baseStart_408152 := by decide
  rcases family_descends (prefixWord ++ tailWord_408152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408183 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 5]
def baseStart_408183 : Nat := 118140960795 + 408183 * 2 ^ 59
def prefixEnd_408183 : Nat := 4983230072969 + 3 ^ 40 * 408183 * 2
def baseEnd_408183 : Nat := 93152921775236318149025

theorem tailTrace_408183 : CollatzResearch.WordTrace tailWord_408183 prefixEnd_408183 93152921775236318149025 := by
  unfold tailWord_408183
  simp only [CollatzResearch.WordTrace]
  refine ⟨14887657080230177951445203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9925104720153451967630135 14887657080230177951445203)
  ·
    refine ⟨22331485620345266927167805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14887657080230177951445203 22331485620345266927167805)
    ·
      refine ⟨8374307107629475097687927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22331485620345266927167805 8374307107629475097687927)
      ·
        refine ⟨12561460661444212646531891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8374307107629475097687927 12561460661444212646531891)
        ·
          refine ⟨18842190992166318969797837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12561460661444212646531891 18842190992166318969797837)
          ·
            refine ⟨7065821622062369613674189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18842190992166318969797837 7065821622062369613674189)
            ·
              refine ⟨2649683108273388605127821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7065821622062369613674189 2649683108273388605127821)
              ·
                refine ⟨993631165602520726922933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2649683108273388605127821 993631165602520726922933)
                ·
                  refine ⟨93152921775236318149025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 993631165602520726922933 93152921775236318149025)
                  ·
                    rfl

theorem cell21_408183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_408183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408183 prefixEnd_408183 := by exact prefixLift 408183
  have htrace : WordTrace (prefixWord ++ tailWord_408183) baseStart_408183 baseEnd_408183 := by
    simpa [prefixWord, tailWord_408183, baseEnd_408183] using wordTrace_append hprefix tailTrace_408183
  have hstable : (prefixWord ++ tailWord_408183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408183).length < 2 ^ (prefixWord ++ tailWord_408183).sum := by decide
  have hdescent : baseEnd_408183 < baseStart_408183 := by decide
  rcases family_descends (prefixWord ++ tailWord_408183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408245 : List Nat := [1, 3, 3, 3, 1, 1, 1, 8]
def baseStart_408245 : Nat := 118140960795 + 408245 * 2 ^ 59
def prefixEnd_408245 : Nat := 4983230072969 + 3 ^ 40 * 408245 * 2
def baseEnd_408245 : Nat := 31055690339979329371855

theorem tailTrace_408245 : CollatzResearch.WordTrace tailWord_408245 prefixEnd_408245 31055690339979329371855 := by
  unfold tailWord_408245
  simp only [CollatzResearch.WordTrace]
  refine ⟨14889918406005562540202189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9926612270670375026801459 14889918406005562540202189)
  ·
    refine ⟨5583719402252085952575821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14889918406005562540202189 5583719402252085952575821)
    ·
      refine ⟨2093894775844532232215933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5583719402252085952575821 2093894775844532232215933)
      ·
        refine ⟨785210540941699587080975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2093894775844532232215933 785210540941699587080975)
        ·
          refine ⟨1177815811412549380621463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785210540941699587080975 1177815811412549380621463)
          ·
            refine ⟨1766723717118824070932195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177815811412549380621463 1766723717118824070932195)
            ·
              refine ⟨2650085575678236106398293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766723717118824070932195 2650085575678236106398293)
              ·
                refine ⟨31055690339979329371855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2650085575678236106398293 31055690339979329371855)
                ·
                  rfl

theorem cell21_408245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 8].length) (baseStart_408245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408245 prefixEnd_408245 := by exact prefixLift 408245
  have htrace : WordTrace (prefixWord ++ tailWord_408245) baseStart_408245 baseEnd_408245 := by
    simpa [prefixWord, tailWord_408245, baseEnd_408245] using wordTrace_append hprefix tailTrace_408245
  have hstable : (prefixWord ++ tailWord_408245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408245).length < 2 ^ (prefixWord ++ tailWord_408245).sum := by decide
  have hdescent : baseEnd_408245 < baseStart_408245 := by decide
  rcases family_descends (prefixWord ++ tailWord_408245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408293 : List Nat := [1, 3, 1, 4, 1, 3, 1, 4, 3]
def baseStart_408293 : Nat := 118140960795 + 408293 * 2 ^ 59
def prefixEnd_408293 : Nat := 4983230072969 + 3 ^ 40 * 408293 * 2
def baseEnd_408293 : Nat := 93178025273900571315467

theorem tailTrace_408293 : CollatzResearch.WordTrace tailWord_408293 prefixEnd_408293 93178025273900571315467 := by
  unfold tailWord_408293
  simp only [CollatzResearch.WordTrace]
  refine ⟨14891669109831666737949533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9927779406554444491966355 14891669109831666737949533)
  ·
    refine ⟨5584375916186875026731075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14891669109831666737949533 5584375916186875026731075)
    ·
      refine ⟨8376563874280312540096613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5584375916186875026731075 8376563874280312540096613)
      ·
        refine ⟨1570605726427558601268115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8376563874280312540096613 1570605726427558601268115)
        ·
          refine ⟨2355908589641337901902173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570605726427558601268115 2355908589641337901902173)
          ·
            refine ⟨883465721115501713213315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2355908589641337901902173 883465721115501713213315)
            ·
              refine ⟨1325198581673252569819973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883465721115501713213315 1325198581673252569819973)
              ·
                refine ⟨248474734063734856841245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1325198581673252569819973 248474734063734856841245)
                ·
                  refine ⟨93178025273900571315467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248474734063734856841245 93178025273900571315467)
                  ·
                    rfl

theorem cell21_408293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_408293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408293 prefixEnd_408293 := by exact prefixLift 408293
  have htrace : WordTrace (prefixWord ++ tailWord_408293) baseStart_408293 baseEnd_408293 := by
    simpa [prefixWord, tailWord_408293, baseEnd_408293] using wordTrace_append hprefix tailTrace_408293
  have hstable : (prefixWord ++ tailWord_408293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408293).length < 2 ^ (prefixWord ++ tailWord_408293).sum := by decide
  have hdescent : baseEnd_408293 < baseStart_408293 := by decide
  rcases family_descends (prefixWord ++ tailWord_408293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408338 : List Nat := [3, 2, 4, 1, 2, 1, 8]
def baseStart_408338 : Nat := 118140960795 + 408338 * 2 ^ 59
def prefixEnd_408338 : Nat := 4983230072969 + 3 ^ 40 * 408338 * 2
def baseEnd_408338 : Nat := 10354254987443388118375

theorem tailTrace_408338 : CollatzResearch.WordTrace tailWord_408338 prefixEnd_408338 10354254987443388118375 := by
  unfold tailWord_408338
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723327598667159855834417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9928873596445759615558445 3723327598667159855834417)
  ·
    refine ⟨2792495699000369891875813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3723327598667159855834417 2792495699000369891875813)
    ·
      refine ⟨523592943562569354726715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2792495699000369891875813 523592943562569354726715)
      ·
        refine ⟨785389415343854032090073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523592943562569354726715 785389415343854032090073)
        ·
          refine ⟨589042061507890524067555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785389415343854032090073 589042061507890524067555)
          ·
            refine ⟨883563092261835786101333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589042061507890524067555 883563092261835786101333)
            ·
              refine ⟨10354254987443388118375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 883563092261835786101333 10354254987443388118375)
              ·
                rfl

theorem cell21_408338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 8].length) (baseStart_408338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408338 prefixEnd_408338 := by exact prefixLift 408338
  have htrace : WordTrace (prefixWord ++ tailWord_408338) baseStart_408338 baseEnd_408338 := by
    simpa [prefixWord, tailWord_408338, baseEnd_408338] using wordTrace_append hprefix tailTrace_408338
  have hstable : (prefixWord ++ tailWord_408338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408338).length < 2 ^ (prefixWord ++ tailWord_408338).sum := by decide
  have hdescent : baseEnd_408338 < baseStart_408338 := by decide
  rcases family_descends (prefixWord ++ tailWord_408338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408352 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 5]
def baseStart_408352 : Nat := 118140960795 + 408352 * 2 ^ 59
def prefixEnd_408352 : Nat := 4983230072969 + 3 ^ 40 * 408352 * 2
def baseEnd_408352 : Nat := 93191489877729579832013

theorem tailTrace_408352 : CollatzResearch.WordTrace tailWord_408352 prefixEnd_408352 93191489877729579832013 := by
  unfold tailWord_408352
  simp only [CollatzResearch.WordTrace]
  refine ⟨7446910508308959907173655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9929214011078613209564873 7446910508308959907173655)
  ·
    refine ⟨11170365762463439860760483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7446910508308959907173655 11170365762463439860760483)
    ·
      refine ⟨16755548643695159791140725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11170365762463439860760483 16755548643695159791140725)
      ·
        refine ⟨1570832685346421230419443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16755548643695159791140725 1570832685346421230419443)
        ·
          refine ⟨2356249028019631845629165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570832685346421230419443 2356249028019631845629165)
          ·
            refine ⟨883593385507361942110937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2356249028019631845629165 883593385507361942110937)
            ·
              refine ⟨662695039130521456583203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883593385507361942110937 662695039130521456583203)
              ·
                refine ⟨994042558695782184874805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662695039130521456583203 994042558695782184874805)
                ·
                  refine ⟨93191489877729579832013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 994042558695782184874805 93191489877729579832013)
                  ·
                    rfl

theorem cell21_408352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_408352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408352 prefixEnd_408352 := by exact prefixLift 408352
  have htrace : WordTrace (prefixWord ++ tailWord_408352) baseStart_408352 baseEnd_408352 := by
    simpa [prefixWord, tailWord_408352, baseEnd_408352] using wordTrace_append hprefix tailTrace_408352
  have hstable : (prefixWord ++ tailWord_408352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408352).length < 2 ^ (prefixWord ++ tailWord_408352).sum := by decide
  have hdescent : baseEnd_408352 < baseStart_408352 := by decide
  rcases family_descends (prefixWord ++ tailWord_408352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408372 : List Nat := [2, 5, 1, 1, 4, 1, 2, 5]
def baseStart_408372 : Nat := 118140960795 + 408372 * 2 ^ 59
def prefixEnd_408372 : Nat := 4983230072969 + 3 ^ 40 * 408372 * 2
def baseEnd_408372 : Nat := 31065351383404663166213

theorem tailTrace_408372 : CollatzResearch.WordTrace tailWord_408372 prefixEnd_408372 31065351383404663166213 := by
  unfold tailWord_408372
  simp only [CollatzResearch.WordTrace]
  refine ⟨7447275238272731615037685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9929700317696975486716913 7447275238272731615037685)
  ·
    refine ⟨698182053588068588909783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7447275238272731615037685 698182053588068588909783)
    ·
      refine ⟨1047273080382102883364675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 698182053588068588909783 1047273080382102883364675)
      ·
        refine ⟨1570909620573154325047013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047273080382102883364675 1570909620573154325047013)
        ·
          refine ⟨294545553857466435946315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1570909620573154325047013 294545553857466435946315)
          ·
            refine ⟨441818330786199653919473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294545553857466435946315 441818330786199653919473)
            ·
              refine ⟨331363748089649740439605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441818330786199653919473 331363748089649740439605)
              ·
                refine ⟨31065351383404663166213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 331363748089649740439605 31065351383404663166213)
                ·
                  rfl

theorem cell21_408372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 5].length) (baseStart_408372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408372 prefixEnd_408372 := by exact prefixLift 408372
  have htrace : WordTrace (prefixWord ++ tailWord_408372) baseStart_408372 baseEnd_408372 := by
    simpa [prefixWord, tailWord_408372, baseEnd_408372] using wordTrace_append hprefix tailTrace_408372
  have hstable : (prefixWord ++ tailWord_408372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408372).length < 2 ^ (prefixWord ++ tailWord_408372).sum := by decide
  have hdescent : baseEnd_408372 < baseStart_408372 := by decide
  rcases family_descends (prefixWord ++ tailWord_408372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408456 : List Nat := [2, 1, 3, 3, 2, 10]
def baseStart_408456 : Nat := 118140960795 + 408456 * 2 ^ 59
def prefixEnd_408456 : Nat := 4983230072969 + 3 ^ 40 * 408456 * 2
def baseEnd_408456 : Nat := 3452415707209204077721

theorem tailTrace_408456 : CollatzResearch.WordTrace tailWord_408456 prefixEnd_408456 3452415707209204077721 := by
  unfold tailWord_408456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7448807104120572788066611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9931742805494097050755481 7448807104120572788066611)
  ·
    refine ⟨11173210656180859182099917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7448807104120572788066611 11173210656180859182099917)
    ·
      refine ⟨4189953996067822193287469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11173210656180859182099917 4189953996067822193287469)
      ·
        refine ⟨1571232748525433322482801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4189953996067822193287469 1571232748525433322482801)
        ·
          refine ⟨1178424561394074991862101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1571232748525433322482801 1178424561394074991862101)
          ·
            refine ⟨3452415707209204077721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1178424561394074991862101 3452415707209204077721)
            ·
              rfl

theorem cell21_408456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 10].length) (baseStart_408456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408456 prefixEnd_408456 := by exact prefixLift 408456
  have htrace : WordTrace (prefixWord ++ tailWord_408456) baseStart_408456 baseEnd_408456 := by
    simpa [prefixWord, tailWord_408456, baseEnd_408456] using wordTrace_append hprefix tailTrace_408456
  have hstable : (prefixWord ++ tailWord_408456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408456).length < 2 ^ (prefixWord ++ tailWord_408456).sum := by decide
  have hdescent : baseEnd_408456 < baseStart_408456 := by decide
  rcases family_descends (prefixWord ++ tailWord_408456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408504 : List Nat := [2, 1, 2, 1, 2, 4, 1, 5, 3]
def baseStart_408504 : Nat := 118140960795 + 408504 * 2 ^ 59
def prefixEnd_408504 : Nat := 4983230072969 + 3 ^ 40 * 408504 * 2
def baseEnd_408504 : Nat := 93226178348611093298369

theorem tailTrace_408504 : CollatzResearch.WordTrace tailWord_408504 prefixEnd_408504 93226178348611093298369 := by
  unfold tailWord_408504
  simp only [CollatzResearch.WordTrace]
  refine ⟨7449682456033624886940283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9932909941378166515920377 7449682456033624886940283)
  ·
    refine ⟨11174523684050437330410425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7449682456033624886940283 11174523684050437330410425)
    ·
      refine ⟨8380892763037827997807819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11174523684050437330410425 8380892763037827997807819)
      ·
        refine ⟨12571339144556741996711729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8380892763037827997807819 12571339144556741996711729)
        ·
          refine ⟨9428504358417556497533797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12571339144556741996711729 9428504358417556497533797)
          ·
            refine ⟨1767844567203291843287587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9428504358417556497533797 1767844567203291843287587)
            ·
              refine ⟨2651766850804937764931381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767844567203291843287587 2651766850804937764931381)
              ·
                refine ⟨248603142262962915462317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2651766850804937764931381 248603142262962915462317)
                ·
                  refine ⟨93226178348611093298369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248603142262962915462317 93226178348611093298369)
                  ·
                    rfl

theorem cell21_408504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 3].length) (baseStart_408504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408504 prefixEnd_408504 := by exact prefixLift 408504
  have htrace : WordTrace (prefixWord ++ tailWord_408504) baseStart_408504 baseEnd_408504 := by
    simpa [prefixWord, tailWord_408504, baseEnd_408504] using wordTrace_append hprefix tailTrace_408504
  have hstable : (prefixWord ++ tailWord_408504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408504).length < 2 ^ (prefixWord ++ tailWord_408504).sum := by decide
  have hdescent : baseEnd_408504 < baseStart_408504 := by decide
  rcases family_descends (prefixWord ++ tailWord_408504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408628 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 4]
def baseStart_408628 : Nat := 118140960795 + 408628 * 2 ^ 59
def prefixEnd_408628 : Nat := 4983230072969 + 3 ^ 40 * 408628 * 2
def baseEnd_408628 : Nat := 93254476838014433231449

theorem tailTrace_408628 : CollatzResearch.WordTrace tailWord_408628 prefixEnd_408628 93254476838014433231449 := by
  unfold tailWord_408628
  simp only [CollatzResearch.WordTrace]
  refine ⟨7451943781809009475697269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9935925042412012634263025 7451943781809009475697269)
  ·
    refine ⟨698619729544594638346619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7451943781809009475697269 698619729544594638346619)
    ·
      refine ⟨1047929594316891957519929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 698619729544594638346619 1047929594316891957519929)
      ·
        refine ⟨785947195737668968139947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1047929594316891957519929 785947195737668968139947)
        ·
          refine ⟨1178920793606503452209921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785947195737668968139947 1178920793606503452209921)
          ·
            refine ⟨884190595204877589157441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1178920793606503452209921 884190595204877589157441)
            ·
              refine ⟨663142946403658191868081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884190595204877589157441 663142946403658191868081)
              ·
                refine ⟨497357209802743643901061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663142946403658191868081 497357209802743643901061)
                ·
                  refine ⟨93254476838014433231449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 497357209802743643901061 93254476838014433231449)
                  ·
                    rfl

theorem cell21_408628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_408628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408628 prefixEnd_408628 := by exact prefixLift 408628
  have htrace : WordTrace (prefixWord ++ tailWord_408628) baseStart_408628 baseEnd_408628 := by
    simpa [prefixWord, tailWord_408628, baseEnd_408628] using wordTrace_append hprefix tailTrace_408628
  have hstable : (prefixWord ++ tailWord_408628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408628).length < 2 ^ (prefixWord ++ tailWord_408628).sum := by decide
  have hdescent : baseEnd_408628 < baseStart_408628 := by decide
  rcases family_descends (prefixWord ++ tailWord_408628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408718 : List Nat := [4, 1, 1, 3, 2, 3, 2, 5]
def baseStart_408718 : Nat := 118140960795 + 408718 * 2 ^ 59
def prefixEnd_408718 : Nat := 4983230072969 + 3 ^ 40 * 408718 * 2
def baseEnd_408718 : Nat := 31091672021398092243755

theorem tailTrace_408718 : CollatzResearch.WordTrace tailWord_408718 prefixEnd_408718 31091672021398092243755 := by
  unfold tailWord_408718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863396266661495540271351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9938113422194642881447205 1863396266661495540271351)
  ·
    refine ⟨2795094399992243310407027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1863396266661495540271351 2795094399992243310407027)
    ·
      refine ⟨4192641599988364965610541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2795094399992243310407027 4192641599988364965610541)
      ·
        refine ⟨1572240599995636862103953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4192641599988364965610541 1572240599995636862103953)
        ·
          refine ⟨1179180449996727646577965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1572240599995636862103953 1179180449996727646577965)
          ·
            refine ⟨442192668748772867466737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1179180449996727646577965 442192668748772867466737)
            ·
              refine ⟨331644501561579650600053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442192668748772867466737 331644501561579650600053)
              ·
                refine ⟨31091672021398092243755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 331644501561579650600053 31091672021398092243755)
                ·
                  rfl

theorem cell21_408718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_408718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408718 prefixEnd_408718 := by exact prefixLift 408718
  have htrace : WordTrace (prefixWord ++ tailWord_408718) baseStart_408718 baseEnd_408718 := by
    simpa [prefixWord, tailWord_408718, baseEnd_408718] using wordTrace_append hprefix tailTrace_408718
  have hstable : (prefixWord ++ tailWord_408718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408718).length < 2 ^ (prefixWord ++ tailWord_408718).sum := by decide
  have hdescent : baseEnd_408718 < baseStart_408718 := by decide
  rcases family_descends (prefixWord ++ tailWord_408718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408749 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 5]
def baseStart_408749 : Nat := 118140960795 + 408749 * 2 ^ 59
def prefixEnd_408749 : Nat := 4983230072969 + 3 ^ 40 * 408749 * 2
def baseEnd_408749 : Nat := 93282090686545111714535

theorem tailTrace_408749 : CollatzResearch.WordTrace tailWord_408749 prefixEnd_408749 93282090686545111714535 := by
  unfold tailWord_408749
  simp only [CollatzResearch.WordTrace]
  refine ⟨14908300796179656616549301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9938867197453104411032867 14908300796179656616549301)
  ·
    refine ⟨1397653199641842807801497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14908300796179656616549301 1397653199641842807801497)
    ·
      refine ⟨1048239899731382105851123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1397653199641842807801497 1048239899731382105851123)
      ·
        refine ⟨1572359849597073158776685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048239899731382105851123 1572359849597073158776685)
        ·
          refine ⟨589634943598902434541257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1572359849597073158776685 589634943598902434541257)
          ·
            refine ⟨442226207699176825905943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589634943598902434541257 442226207699176825905943)
            ·
              refine ⟨663339311548765238858915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442226207699176825905943 663339311548765238858915)
              ·
                refine ⟨995008967323147858288373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663339311548765238858915 995008967323147858288373)
                ·
                  refine ⟨93282090686545111714535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 995008967323147858288373 93282090686545111714535)
                  ·
                    rfl

theorem cell21_408749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_408749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408749 prefixEnd_408749 := by exact prefixLift 408749
  have htrace : WordTrace (prefixWord ++ tailWord_408749) baseStart_408749 baseEnd_408749 := by
    simpa [prefixWord, tailWord_408749, baseEnd_408749] using wordTrace_append hprefix tailTrace_408749
  have hstable : (prefixWord ++ tailWord_408749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408749).length < 2 ^ (prefixWord ++ tailWord_408749).sum := by decide
  have hdescent : baseEnd_408749 < baseStart_408749 := by decide
  rcases family_descends (prefixWord ++ tailWord_408749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408808 : List Nat := [2, 1, 4, 1, 2, 1, 3, 4, 3]
def baseStart_408808 : Nat := 118140960795 + 408808 * 2 ^ 59
def prefixEnd_408808 : Nat := 4983230072969 + 3 ^ 40 * 408808 * 2
def baseEnd_408808 : Nat := 93295555290374120231081

theorem tailTrace_408808 : CollatzResearch.WordTrace tailWord_408808 prefixEnd_408808 93295555290374120231081 := by
  unfold tailWord_408808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7455226351482954846473539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9940301801977273128631385 7455226351482954846473539)
  ·
    refine ⟨11182839527224432269710309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7455226351482954846473539 11182839527224432269710309)
    ·
      refine ⟨2096782411354581050570683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11182839527224432269710309 2096782411354581050570683)
      ·
        refine ⟨3145173617031871575856025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096782411354581050570683 3145173617031871575856025)
        ·
          refine ⟨2358880212773903681892019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3145173617031871575856025 2358880212773903681892019)
          ·
            refine ⟨3538320319160855522838029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358880212773903681892019 3538320319160855522838029)
            ·
              refine ⟨1326870119685320821064261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3538320319160855522838029 1326870119685320821064261)
              ·
                refine ⟨248788147440997653949549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1326870119685320821064261 248788147440997653949549)
                ·
                  refine ⟨93295555290374120231081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248788147440997653949549 93295555290374120231081)
                  ·
                    rfl

theorem cell21_408808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 3].length) (baseStart_408808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408808 prefixEnd_408808 := by exact prefixLift 408808
  have htrace : WordTrace (prefixWord ++ tailWord_408808) baseStart_408808 baseEnd_408808 := by
    simpa [prefixWord, tailWord_408808, baseEnd_408808] using wordTrace_append hprefix tailTrace_408808
  have hstable : (prefixWord ++ tailWord_408808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408808).length < 2 ^ (prefixWord ++ tailWord_408808).sum := by decide
  have hdescent : baseEnd_408808 < baseStart_408808 := by decide
  rcases family_descends (prefixWord ++ tailWord_408808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408867 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 5]
def baseStart_408867 : Nat := 118140960795 + 408867 * 2 ^ 59
def prefixEnd_408867 : Nat := 4983230072969 + 3 ^ 40 * 408867 * 2
def baseEnd_408867 : Nat := 93309019894203128747627

theorem tailTrace_408867 : CollatzResearch.WordTrace tailWord_408867 prefixEnd_408867 93309019894203128747627 := by
  unfold tailWord_408867
  simp only [CollatzResearch.WordTrace]
  refine ⟨14912604609752162769344855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9941736406501441846229903 14912604609752162769344855)
  ·
    refine ⟨22368906914628244154017283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14912604609752162769344855 22368906914628244154017283)
    ·
      refine ⟨33553360371942366231025925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22368906914628244154017283 33553360371942366231025925)
      ·
        refine ⟨6291255069739193668317361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33553360371942366231025925 6291255069739193668317361)
        ·
          refine ⟨4718441302304395251238021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6291255069739193668317361 4718441302304395251238021)
          ·
            refine ⟨884707744182074109607129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4718441302304395251238021 884707744182074109607129)
            ·
              refine ⟨663530808136555582205347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884707744182074109607129 663530808136555582205347)
              ·
                refine ⟨995296212204833373308021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663530808136555582205347 995296212204833373308021)
                ·
                  refine ⟨93309019894203128747627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 995296212204833373308021 93309019894203128747627)
                  ·
                    rfl

theorem cell21_408867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 5].length) (baseStart_408867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_408867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_408867 prefixEnd_408867 := by exact prefixLift 408867
  have htrace : WordTrace (prefixWord ++ tailWord_408867) baseStart_408867 baseEnd_408867 := by
    simpa [prefixWord, tailWord_408867, baseEnd_408867] using wordTrace_append hprefix tailTrace_408867
  have hstable : (prefixWord ++ tailWord_408867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408867).length < 2 ^ (prefixWord ++ tailWord_408867).sum := by decide
  have hdescent : baseEnd_408867 < baseStart_408867 := by decide
  rcases family_descends (prefixWord ++ tailWord_408867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409036 : List Nat := [2, 2, 1, 4, 2, 1, 2, 4, 3]
def baseStart_409036 : Nat := 118140960795 + 409036 * 2 ^ 59
def prefixEnd_409036 : Nat := 4983230072969 + 3 ^ 40 * 409036 * 2
def baseEnd_409036 : Nat := 93347587996696390430615

theorem tailTrace_409036 : CollatzResearch.WordTrace tailWord_409036 prefixEnd_409036 93347587996696390430615 := by
  unfold tailWord_409036
  simp only [CollatzResearch.WordTrace]
  refine ⟨7459384273069952316123481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9945845697426603088164641 7459384273069952316123481)
  ·
    refine ⟨5594538204802464237092611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7459384273069952316123481 5594538204802464237092611)
    ·
      refine ⟨8391807307203696355638917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5594538204802464237092611 8391807307203696355638917)
      ·
        refine ⟨1573463870100693066682297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8391807307203696355638917 1573463870100693066682297)
        ·
          refine ⟨1180097902575519800011723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573463870100693066682297 1180097902575519800011723)
          ·
            refine ⟨1770146853863279700017585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180097902575519800011723 1770146853863279700017585)
            ·
              refine ⟨1327610140397459775013189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770146853863279700017585 1327610140397459775013189)
              ·
                refine ⟨248926901324523707814973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1327610140397459775013189 248926901324523707814973)
                ·
                  refine ⟨93347587996696390430615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 248926901324523707814973 93347587996696390430615)
                  ·
                    rfl

theorem cell21_409036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_409036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409036 prefixEnd_409036 := by exact prefixLift 409036
  have htrace : WordTrace (prefixWord ++ tailWord_409036) baseStart_409036 baseEnd_409036 := by
    simpa [prefixWord, tailWord_409036, baseEnd_409036] using wordTrace_append hprefix tailTrace_409036
  have hstable : (prefixWord ++ tailWord_409036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409036).length < 2 ^ (prefixWord ++ tailWord_409036).sum := by decide
  have hdescent : baseEnd_409036 < baseStart_409036 := by decide
  rcases family_descends (prefixWord ++ tailWord_409036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409095 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 5]
def baseStart_409095 : Nat := 118140960795 + 409095 * 2 ^ 59
def prefixEnd_409095 : Nat := 4983230072969 + 3 ^ 40 * 409095 * 2
def baseEnd_409095 : Nat := 93361052600525398947161

theorem tailTrace_409095 : CollatzResearch.WordTrace tailWord_409095 prefixEnd_409095 93361052600525398947161 := by
  unfold tailWord_409095
  simp only [CollatzResearch.WordTrace]
  refine ⟨14920920452926157708644739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9947280301950771805763159 14920920452926157708644739)
  ·
    refine ⟨22381380679389236562967109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14920920452926157708644739 22381380679389236562967109)
    ·
      refine ⟨4196508877385481855556333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22381380679389236562967109 4196508877385481855556333)
      ·
        refine ⟨1573690829019555695833625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4196508877385481855556333 1573690829019555695833625)
        ·
          refine ⟨1180268121764666771875219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1573690829019555695833625 1180268121764666771875219)
          ·
            refine ⟨1770402182647000157812829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180268121764666771875219 1770402182647000157812829)
            ·
              refine ⟨663900818492625059179811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1770402182647000157812829 663900818492625059179811)
              ·
                refine ⟨995851227738937588769717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663900818492625059179811 995851227738937588769717)
                ·
                  refine ⟨93361052600525398947161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 995851227738937588769717 93361052600525398947161)
                  ·
                    rfl

theorem cell21_409095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 5].length) (baseStart_409095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409095 prefixEnd_409095 := by exact prefixLift 409095
  have htrace : WordTrace (prefixWord ++ tailWord_409095) baseStart_409095 baseEnd_409095 := by
    simpa [prefixWord, tailWord_409095, baseEnd_409095] using wordTrace_append hprefix tailTrace_409095
  have hstable : (prefixWord ++ tailWord_409095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409095).length < 2 ^ (prefixWord ++ tailWord_409095).sum := by decide
  have hdescent : baseEnd_409095 < baseStart_409095 := by decide
  rcases family_descends (prefixWord ++ tailWord_409095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409188 : List Nat := [2, 3, 1, 1, 2, 4, 2, 3, 3]
def baseStart_409188 : Nat := 118140960795 + 409188 * 2 ^ 59
def prefixEnd_409188 : Nat := 4983230072969 + 3 ^ 40 * 409188 * 2
def baseEnd_409188 : Nat := 93382276467577903896971

theorem tailTrace_409188 : CollatzResearch.WordTrace tailWord_409188 prefixEnd_409188 93382276467577903896971 := by
  unfold tailWord_409188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7462156220794617295890109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9949541627726156394520145 7462156220794617295890109)
  ·
    refine ⟨2798308582797981485958791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7462156220794617295890109 2798308582797981485958791)
    ·
      refine ⟨4197462874196972228938187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798308582797981485958791 4197462874196972228938187)
      ·
        refine ⟨6296194311295458343407281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4197462874196972228938187 6296194311295458343407281)
        ·
          refine ⟨4722145733471593757555461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6296194311295458343407281 4722145733471593757555461)
          ·
            refine ⟨885402325025923829541649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4722145733471593757555461 885402325025923829541649)
            ·
              refine ⟨664051743769442872156237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885402325025923829541649 664051743769442872156237)
              ·
                refine ⟨249019403913541077058589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 664051743769442872156237 249019403913541077058589)
                ·
                  refine ⟨93382276467577903896971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249019403913541077058589 93382276467577903896971)
                  ·
                    rfl

theorem cell21_409188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_409188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409188 prefixEnd_409188 := by exact prefixLift 409188
  have htrace : WordTrace (prefixWord ++ tailWord_409188) baseStart_409188 baseEnd_409188 := by
    simpa [prefixWord, tailWord_409188, baseEnd_409188] using wordTrace_append hprefix tailTrace_409188
  have hstable : (prefixWord ++ tailWord_409188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409188).length < 2 ^ (prefixWord ++ tailWord_409188).sum := by decide
  have hdescent : baseEnd_409188 < baseStart_409188 := by decide
  rcases family_descends (prefixWord ++ tailWord_409188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409202 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_409202 : Nat := 118140960795 + 409202 * 2 ^ 59
def prefixEnd_409202 : Nat := 4983230072969 + 3 ^ 40 * 409202 * 2
def baseEnd_409202 : Nat := 93385471458316990663609

theorem tailTrace_409202 : CollatzResearch.WordTrace tailWord_409202 prefixEnd_409202 93385471458316990663609 := by
  unfold tailWord_409202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731205765884628745697465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9949882042359009988526573 3731205765884628745697465)
  ·
    refine ⟨2798404324413471559273099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3731205765884628745697465 2798404324413471559273099)
    ·
      refine ⟨4197606486620207338909649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798404324413471559273099 4197606486620207338909649)
      ·
        refine ⟨3148204864965155504182237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4197606486620207338909649 3148204864965155504182237)
        ·
          refine ⟨1180576824361933314068339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3148204864965155504182237 1180576824361933314068339)
          ·
            refine ⟨1770865236542899971102509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180576824361933314068339 1770865236542899971102509)
            ·
              refine ⟨664074463703587489163441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1770865236542899971102509 664074463703587489163441)
              ·
                refine ⟨498055847777690616872581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664074463703587489163441 498055847777690616872581)
                ·
                  refine ⟨93385471458316990663609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498055847777690616872581 93385471458316990663609)
                  ·
                    rfl

theorem cell21_409202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_409202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409202 prefixEnd_409202 := by exact prefixLift 409202
  have htrace : WordTrace (prefixWord ++ tailWord_409202) baseStart_409202 baseEnd_409202 := by
    simpa [prefixWord, tailWord_409202, baseEnd_409202] using wordTrace_append hprefix tailTrace_409202
  have hstable : (prefixWord ++ tailWord_409202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409202).length < 2 ^ (prefixWord ++ tailWord_409202).sum := by decide
  have hdescent : baseEnd_409202 < baseStart_409202 := by decide
  rcases family_descends (prefixWord ++ tailWord_409202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409250 : List Nat := [3, 3, 1, 4, 2, 1, 7]
def baseStart_409250 : Nat := 118140960795 + 409250 * 2 ^ 59
def prefixEnd_409250 : Nat := 4983230072969 + 3 ^ 40 * 409250 * 2
def baseEnd_409250 : Nat := 10377380634697730429279

theorem tailTrace_409250 : CollatzResearch.WordTrace tailWord_409250 prefixEnd_409250 10377380634697730429279 := by
  unfold tailWord_409250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731643441841154795134301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9951049178243079453691469 3731643441841154795134301)
  ·
    refine ⟨1399366290690433048175363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3731643441841154795134301 1399366290690433048175363)
    ·
      refine ⟨2099049436035649572263045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1399366290690433048175363 2099049436035649572263045)
      ·
        refine ⟨393571769256684294799321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2099049436035649572263045 393571769256684294799321)
        ·
          refine ⟨295178826942513221099491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393571769256684294799321 295178826942513221099491)
          ·
            refine ⟨442768240413769831649237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295178826942513221099491 442768240413769831649237)
            ·
              refine ⟨10377380634697730429279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 442768240413769831649237 10377380634697730429279)
              ·
                rfl

theorem cell21_409250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 7].length) (baseStart_409250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409250 prefixEnd_409250 := by exact prefixLift 409250
  have htrace : WordTrace (prefixWord ++ tailWord_409250) baseStart_409250 baseEnd_409250 := by
    simpa [prefixWord, tailWord_409250, baseEnd_409250] using wordTrace_append hprefix tailTrace_409250
  have hstable : (prefixWord ++ tailWord_409250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409250).length < 2 ^ (prefixWord ++ tailWord_409250).sum := by decide
  have hdescent : baseEnd_409250 < baseStart_409250 := by decide
  rcases family_descends (prefixWord ++ tailWord_409250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409261 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 6]
def baseStart_409261 : Nat := 118140960795 + 409261 * 2 ^ 59
def prefixEnd_409261 : Nat := 4983230072969 + 3 ^ 40 * 409261 * 2
def baseEnd_409261 : Nat := 93398936062145999180155

theorem tailTrace_409261 : CollatzResearch.WordTrace tailWord_409261 prefixEnd_409261 93398936062145999180155 := by
  unfold tailWord_409261
  simp only [CollatzResearch.WordTrace]
  refine ⟨14926974970324768059187637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9951316646883178706125091 14926974970324768059187637)
  ·
    refine ⟨1399403903467947005548841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14926974970324768059187637 1399403903467947005548841)
    ·
      refine ⟨1049552927600960254161631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1399403903467947005548841 1049552927600960254161631)
      ·
        refine ⟨1574329391401440381242447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049552927600960254161631 1574329391401440381242447)
        ·
          refine ⟨2361494087102160571863671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574329391401440381242447 2361494087102160571863671)
          ·
            refine ⟨3542241130653240857795507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2361494087102160571863671 3542241130653240857795507)
            ·
              refine ⟨5313361695979861286693261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3542241130653240857795507 5313361695979861286693261)
              ·
                refine ⟨1992510635992447982509973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5313361695979861286693261 1992510635992447982509973)
                ·
                  refine ⟨93398936062145999180155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1992510635992447982509973 93398936062145999180155)
                  ·
                    rfl

theorem cell21_409261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_409261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409261 prefixEnd_409261 := by exact prefixLift 409261
  have htrace : WordTrace (prefixWord ++ tailWord_409261) baseStart_409261 baseEnd_409261 := by
    simpa [prefixWord, tailWord_409261, baseEnd_409261] using wordTrace_append hprefix tailTrace_409261
  have hstable : (prefixWord ++ tailWord_409261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409261).length < 2 ^ (prefixWord ++ tailWord_409261).sum := by decide
  have hdescent : baseEnd_409261 < baseStart_409261 := by decide
  rcases family_descends (prefixWord ++ tailWord_409261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409278 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_409278 : Nat := 118140960795 + 409278 * 2 ^ 59
def prefixEnd_409278 : Nat := 4983230072969 + 3 ^ 40 * 409278 * 2
def baseEnd_409278 : Nat := 93402815693757747396787

theorem tailTrace_409278 : CollatzResearch.WordTrace tailWord_409278 prefixEnd_409278 93402815693757747396787 := by
  unfold tailWord_409278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865949376407897495319561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9951730007508786641704325 1865949376407897495319561)
  ·
    refine ⟨1399462032305923121489671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1865949376407897495319561 1399462032305923121489671)
    ·
      refine ⟨2099193048458884682234507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1399462032305923121489671 2099193048458884682234507)
      ·
        refine ⟨3148789572688327023351761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099193048458884682234507 3148789572688327023351761)
        ·
          refine ⟨2361592179516245267513821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3148789572688327023351761 2361592179516245267513821)
          ·
            refine ⟨885597067318591975317683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2361592179516245267513821 885597067318591975317683)
            ·
              refine ⟨1328395600977887962976525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885597067318591975317683 1328395600977887962976525)
              ·
                refine ⟨498148350366707986116197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1328395600977887962976525 498148350366707986116197)
                ·
                  refine ⟨93402815693757747396787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498148350366707986116197 93402815693757747396787)
                  ·
                    rfl

theorem cell21_409278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_409278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409278 prefixEnd_409278 := by exact prefixLift 409278
  have htrace : WordTrace (prefixWord ++ tailWord_409278) baseStart_409278 baseEnd_409278 := by
    simpa [prefixWord, tailWord_409278, baseEnd_409278] using wordTrace_append hprefix tailTrace_409278
  have hstable : (prefixWord ++ tailWord_409278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409278).length < 2 ^ (prefixWord ++ tailWord_409278).sum := by decide
  have hdescent : baseEnd_409278 < baseStart_409278 := by decide
  rcases family_descends (prefixWord ++ tailWord_409278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409309 : List Nat := [1, 4, 3, 3, 2, 8]
def baseStart_409309 : Nat := 118140960795 + 409309 * 2 ^ 59
def prefixEnd_409309 : Nat := 4983230072969 + 3 ^ 40 * 409309 * 2
def baseEnd_409309 : Nat := 3459625567263280828891

theorem tailTrace_409309 : CollatzResearch.WordTrace tailWord_409309 prefixEnd_409309 3459625567263280828891 := by
  unfold tailWord_409309
  simp only [CollatzResearch.WordTrace]
  refine ⟨14928725674150872256934981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9952483782767248171289987 14928725674150872256934981)
  ·
    refine ⟨2799136063903288548175309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14928725674150872256934981 2799136063903288548175309)
    ·
      refine ⟨1049676023963733205565741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2799136063903288548175309 1049676023963733205565741)
      ·
        refine ⟨393628508986399952087153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1049676023963733205565741 393628508986399952087153)
        ·
          refine ⟨295221381739799964065365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393628508986399952087153 295221381739799964065365)
          ·
            refine ⟨3459625567263280828891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 295221381739799964065365 3459625567263280828891)
            ·
              rfl

theorem cell21_409309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 8].length) (baseStart_409309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409309 prefixEnd_409309 := by exact prefixLift 409309
  have htrace : WordTrace (prefixWord ++ tailWord_409309) baseStart_409309 baseEnd_409309 := by
    simpa [prefixWord, tailWord_409309, baseEnd_409309] using wordTrace_append hprefix tailTrace_409309
  have hstable : (prefixWord ++ tailWord_409309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409309).length < 2 ^ (prefixWord ++ tailWord_409309).sum := by decide
  have hdescent : baseEnd_409309 < baseStart_409309 := by decide
  rcases family_descends (prefixWord ++ tailWord_409309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409416 : List Nat := [2, 1, 3, 1, 1, 6, 1, 3, 3]
def baseStart_409416 : Nat := 118140960795 + 409416 * 2 ^ 59
def prefixEnd_409416 : Nat := 4983230072969 + 3 ^ 40 * 409416 * 2
def baseEnd_409416 : Nat := 93434309173900174096505

theorem tailTrace_409416 : CollatzResearch.WordTrace tailWord_409416 prefixEnd_409416 93434309173900174096505 := by
  unfold tailWord_409416
  simp only [CollatzResearch.WordTrace]
  refine ⟨7466314142381614765540051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9955085523175486354053401 7466314142381614765540051)
  ·
    refine ⟨11199471213572422148310077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7466314142381614765540051 11199471213572422148310077)
    ·
      refine ⟨4199801705089658305616279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11199471213572422148310077 4199801705089658305616279)
      ·
        refine ⟨6299702557634487458424419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4199801705089658305616279 6299702557634487458424419)
        ·
          refine ⟨9449553836451731187636629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6299702557634487458424419 9449553836451731187636629)
          ·
            refine ⟨442947836083674899420467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9449553836451731187636629 442947836083674899420467)
            ·
              refine ⟨664421754125512349130701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442947836083674899420467 664421754125512349130701)
              ·
                refine ⟨249158157797067130924013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 664421754125512349130701 249158157797067130924013)
                ·
                  refine ⟨93434309173900174096505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249158157797067130924013 93434309173900174096505)
                  ·
                    rfl

theorem cell21_409416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 3].length) (baseStart_409416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409416 prefixEnd_409416 := by exact prefixLift 409416
  have htrace : WordTrace (prefixWord ++ tailWord_409416) baseStart_409416 baseEnd_409416 := by
    simpa [prefixWord, tailWord_409416, baseEnd_409416] using wordTrace_append hprefix tailTrace_409416
  have hstable : (prefixWord ++ tailWord_409416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409416).length < 2 ^ (prefixWord ++ tailWord_409416).sum := by decide
  have hdescent : baseEnd_409416 < baseStart_409416 := by decide
  rcases family_descends (prefixWord ++ tailWord_409416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409444 : List Nat := [2, 3, 1, 1, 5, 1, 2, 6]
def baseStart_409444 : Nat := 118140960795 + 409444 * 2 ^ 59
def prefixEnd_409444 : Nat := 4983230072969 + 3 ^ 40 * 409444 * 2
def baseEnd_409444 : Nat := 31146899718459449209927

theorem tailTrace_409444 : CollatzResearch.WordTrace tailWord_409444 prefixEnd_409444 31146899718459449209927 := by
  unfold tailWord_409444
  simp only [CollatzResearch.WordTrace]
  refine ⟨7466824764330895156549693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9955766352441193542066257 7466824764330895156549693)
  ·
    refine ⟨2800059286624085683706135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7466824764330895156549693 2800059286624085683706135)
    ·
      refine ⟨4200088929936128525559203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2800059286624085683706135 4200088929936128525559203)
      ·
        refine ⟨6300133394904192788338805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4200088929936128525559203 6300133394904192788338805)
        ·
          refine ⟨590637505772268073906763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6300133394904192788338805 590637505772268073906763)
          ·
            refine ⟨885956258658402110860145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590637505772268073906763 885956258658402110860145)
            ·
              refine ⟨664467193993801583145109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885956258658402110860145 664467193993801583145109)
              ·
                refine ⟨31146899718459449209927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 664467193993801583145109 31146899718459449209927)
                ·
                  rfl

theorem cell21_409444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_409444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409444 prefixEnd_409444 := by exact prefixLift 409444
  have htrace : WordTrace (prefixWord ++ tailWord_409444) baseStart_409444 baseEnd_409444 := by
    simpa [prefixWord, tailWord_409444, baseEnd_409444] using wordTrace_append hprefix tailTrace_409444
  have hstable : (prefixWord ++ tailWord_409444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409444).length < 2 ^ (prefixWord ++ tailWord_409444).sum := by decide
  have hdescent : baseEnd_409444 < baseStart_409444 := by decide
  rcases family_descends (prefixWord ++ tailWord_409444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409492 : List Nat := [2, 4, 2, 1, 1, 3, 1, 4, 3]
def baseStart_409492 : Nat := 118140960795 + 409492 * 2 ^ 59
def prefixEnd_409492 : Nat := 4983230072969 + 3 ^ 40 * 409492 * 2
def baseEnd_409492 : Nat := 93451653409340930829683

theorem tailTrace_409492 : CollatzResearch.WordTrace tailWord_409492 prefixEnd_409492 93451653409340930829683 := by
  unfold tailWord_409492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7467700116243947255423365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9956933488325263007231153 7467700116243947255423365)
  ·
    refine ⟨1400193771795740110391881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7467700116243947255423365 1400193771795740110391881)
    ·
      refine ⟨1050145328846805082793911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1400193771795740110391881 1050145328846805082793911)
      ·
        refine ⟨1575217993270207624190867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050145328846805082793911 1575217993270207624190867)
        ·
          refine ⟨2362826989905311436286301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1575217993270207624190867 2362826989905311436286301)
          ·
            refine ⟨886060121214491788607363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2362826989905311436286301 886060121214491788607363)
            ·
              refine ⟨1329090181821737682911045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886060121214491788607363 1329090181821737682911045)
              ·
                refine ⟨249204409091575815545821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1329090181821737682911045 249204409091575815545821)
                ·
                  refine ⟨93451653409340930829683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249204409091575815545821 93451653409340930829683)
                  ·
                    rfl

theorem cell21_409492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_409492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409492 prefixEnd_409492 := by exact prefixLift 409492
  have htrace : WordTrace (prefixWord ++ tailWord_409492) baseStart_409492 baseEnd_409492 := by
    simpa [prefixWord, tailWord_409492, baseEnd_409492] using wordTrace_append hprefix tailTrace_409492
  have hstable : (prefixWord ++ tailWord_409492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409492).length < 2 ^ (prefixWord ++ tailWord_409492).sum := by decide
  have hdescent : baseEnd_409492 < baseStart_409492 := by decide
  rcases family_descends (prefixWord ++ tailWord_409492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409585 : List Nat := [1, 2, 2, 2, 6, 1, 1, 3, 3]
def baseStart_409585 : Nat := 118140960795 + 409585 * 2 ^ 59
def prefixEnd_409585 : Nat := 4983230072969 + 3 ^ 40 * 409585 * 2
def baseEnd_409585 : Nat := 93472877276393435779493

theorem tailTrace_409585 : CollatzResearch.WordTrace tailWord_409585 prefixEnd_409585 93472877276393435779493 := by
  unfold tailWord_409585
  simp only [CollatzResearch.WordTrace]
  refine ⟨14938792221150971393982209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9959194814100647595988139 14938792221150971393982209)
  ·
    refine ⟨11204094165863228545486657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14938792221150971393982209 11204094165863228545486657)
    ·
      refine ⟨8403070624397421409114993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11204094165863228545486657 8403070624397421409114993)
      ·
        refine ⟨6302302968298066056836245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8403070624397421409114993 6302302968298066056836245)
        ·
          refine ⟨295420451638971846414199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6302302968298066056836245 295420451638971846414199)
          ·
            refine ⟨443130677458457769621299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295420451638971846414199 443130677458457769621299)
            ·
              refine ⟨664696016187686654431949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443130677458457769621299 664696016187686654431949)
              ·
                refine ⟨249261006070382495411981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 664696016187686654431949 249261006070382495411981)
                ·
                  refine ⟨93472877276393435779493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249261006070382495411981 93472877276393435779493)
                  ·
                    rfl

theorem cell21_409585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 3].length) (baseStart_409585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409585 prefixEnd_409585 := by exact prefixLift 409585
  have htrace : WordTrace (prefixWord ++ tailWord_409585) baseStart_409585 baseEnd_409585 := by
    simpa [prefixWord, tailWord_409585, baseEnd_409585] using wordTrace_append hprefix tailTrace_409585
  have hstable : (prefixWord ++ tailWord_409585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409585).length < 2 ^ (prefixWord ++ tailWord_409585).sum := by decide
  have hdescent : baseEnd_409585 < baseStart_409585 := by decide
  rcases family_descends (prefixWord ++ tailWord_409585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409669 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 5]
def baseStart_409669 : Nat := 118140960795 + 409669 * 2 ^ 59
def prefixEnd_409669 : Nat := 4983230072969 + 3 ^ 40 * 409669 * 2
def baseEnd_409669 : Nat := 93492047220827956379321

theorem tailTrace_409669 : CollatzResearch.WordTrace tailWord_409669 prefixEnd_409669 93492047220827956379321 := by
  unfold tailWord_409669
  simp only [CollatzResearch.WordTrace]
  refine ⟨14941855952846653740040061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9961237301897769160026707 14941855952846653740040061)
  ·
    refine ⟨5603195982317495152515023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14941855952846653740040061 5603195982317495152515023)
    ·
      refine ⟨8404793973476242728772535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5603195982317495152515023 8404793973476242728772535)
      ·
        refine ⟨12607190960214364093158803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8404793973476242728772535 12607190960214364093158803)
        ·
          refine ⟨18910786440321546139738205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12607190960214364093158803 18910786440321546139738205)
          ·
            refine ⟨7091544915120579802401827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18910786440321546139738205 7091544915120579802401827)
            ·
              refine ⟨10637317372680869703602741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091544915120579802401827 10637317372680869703602741)
              ·
                refine ⟨997248503688831534712757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10637317372680869703602741 997248503688831534712757)
                ·
                  refine ⟨93492047220827956379321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 997248503688831534712757 93492047220827956379321)
                  ·
                    rfl

theorem cell21_409669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_409669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409669 prefixEnd_409669 := by exact prefixLift 409669
  have htrace : WordTrace (prefixWord ++ tailWord_409669) baseStart_409669 baseEnd_409669 := by
    simpa [prefixWord, tailWord_409669, baseEnd_409669] using wordTrace_append hprefix tailTrace_409669
  have hstable : (prefixWord ++ tailWord_409669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409669).length < 2 ^ (prefixWord ++ tailWord_409669).sum := by decide
  have hdescent : baseEnd_409669 < baseStart_409669 := by decide
  rcases family_descends (prefixWord ++ tailWord_409669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409703 : List Nat := [1, 1, 5, 1, 1, 2, 4, 3, 3]
def baseStart_409703 : Nat := 118140960795 + 409703 * 2 ^ 59
def prefixEnd_409703 : Nat := 4983230072969 + 3 ^ 40 * 409703 * 2
def baseEnd_409703 : Nat := 93499806484051452812585

theorem tailTrace_409703 : CollatzResearch.WordTrace tailWord_409703 prefixEnd_409703 93499806484051452812585 := by
  unfold tailWord_409703
  simp only [CollatzResearch.WordTrace]
  refine ⟨14943096034723477546777763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9962064023148985031185175 14943096034723477546777763)
  ·
    refine ⟨22414644052085216320166645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14943096034723477546777763 22414644052085216320166645)
    ·
      refine ⟨2101372879882989030015623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22414644052085216320166645 2101372879882989030015623)
      ·
        refine ⟨3152059319824483545023435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2101372879882989030015623 3152059319824483545023435)
        ·
          refine ⟨4728088979736725317535153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3152059319824483545023435 4728088979736725317535153)
          ·
            refine ⟨3546066734802543988151365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4728088979736725317535153 3546066734802543988151365)
            ·
              refine ⟨664887512775476997778381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3546066734802543988151365 664887512775476997778381)
              ·
                refine ⟨249332817290803874166893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 664887512775476997778381 249332817290803874166893)
                ·
                  refine ⟨93499806484051452812585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249332817290803874166893 93499806484051452812585)
                  ·
                    rfl

theorem cell21_409703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 3].length) (baseStart_409703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409703 prefixEnd_409703 := by exact prefixLift 409703
  have htrace : WordTrace (prefixWord ++ tailWord_409703) baseStart_409703 baseEnd_409703 := by
    simpa [prefixWord, tailWord_409703, baseEnd_409703] using wordTrace_append hprefix tailTrace_409703
  have hstable : (prefixWord ++ tailWord_409703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409703).length < 2 ^ (prefixWord ++ tailWord_409703).sum := by decide
  have hdescent : baseEnd_409703 < baseStart_409703 := by decide
  rcases family_descends (prefixWord ++ tailWord_409703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409866 : List Nat := [3, 1, 2, 2, 1, 1, 2, 9]
def baseStart_409866 : Nat := 118140960795 + 409866 * 2 ^ 59
def prefixEnd_409866 : Nat := 4983230072969 + 3 ^ 40 * 409866 * 2
def baseEnd_409866 : Nat := 31179001768266463865195

theorem tailTrace_409866 : CollatzResearch.WordTrace tailWord_409866 prefixEnd_409866 31179001768266463865195 := by
  unfold tailWord_409866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3737260283283239096240363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9966027422088637589974301 3737260283283239096240363)
  ·
    refine ⟨5605890424924858644360545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3737260283283239096240363 5605890424924858644360545)
    ·
      refine ⟨4204417818693643983270409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5605890424924858644360545 4204417818693643983270409)
      ·
        refine ⟨3153313364020232987452807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4204417818693643983270409 3153313364020232987452807)
        ·
          refine ⟨4729970046030349481179211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3153313364020232987452807 4729970046030349481179211)
          ·
            refine ⟨7094955069045524221768817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4729970046030349481179211 7094955069045524221768817)
            ·
              refine ⟨5321216301784143166326613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7094955069045524221768817 5321216301784143166326613)
              ·
                refine ⟨31179001768266463865195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5321216301784143166326613 31179001768266463865195)
                ·
                  rfl

theorem cell21_409866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_409866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409866 prefixEnd_409866 := by exact prefixLift 409866
  have htrace : WordTrace (prefixWord ++ tailWord_409866) baseStart_409866 baseEnd_409866 := by
    simpa [prefixWord, tailWord_409866, baseEnd_409866] using wordTrace_append hprefix tailTrace_409866
  have hstable : (prefixWord ++ tailWord_409866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409866).length < 2 ^ (prefixWord ++ tailWord_409866).sum := by decide
  have hdescent : baseEnd_409866 < baseStart_409866 := by decide
  rcases family_descends (prefixWord ++ tailWord_409866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409886 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_409886 : Nat := 118140960795 + 409886 * 2 ^ 59
def prefixEnd_409886 : Nat := 4983230072969 + 3 ^ 40 * 409886 * 2
def baseEnd_409886 : Nat := 93541569577283801262211

theorem tailTrace_409886 : CollatzResearch.WordTrace tailWord_409886 prefixEnd_409886 93541569577283801262211 := by
  unfold tailWord_409886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868721324132562475086189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9966513728706999867126341 1868721324132562475086189)
  ·
    refine ⟨700770496549710928157321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1868721324132562475086189 700770496549710928157321)
    ·
      refine ⟨525577872412283196117991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 700770496549710928157321 525577872412283196117991)
      ·
        refine ⟨788366808618424794176987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525577872412283196117991 788366808618424794176987)
        ·
          refine ⟨1182550212927637191265481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788366808618424794176987 1182550212927637191265481)
          ·
            refine ⟨886912659695727893449111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1182550212927637191265481 886912659695727893449111)
            ·
              refine ⟨1330368989543591840173667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886912659695727893449111 1330368989543591840173667)
              ·
                refine ⟨1995553484315387760260501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330368989543591840173667 1995553484315387760260501)
                ·
                  refine ⟨93541569577283801262211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1995553484315387760260501 93541569577283801262211)
                  ·
                    rfl

theorem cell21_409886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_409886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409886 prefixEnd_409886 := by exact prefixLift 409886
  have htrace : WordTrace (prefixWord ++ tailWord_409886) baseStart_409886 baseEnd_409886 := by
    simpa [prefixWord, tailWord_409886, baseEnd_409886] using wordTrace_append hprefix tailTrace_409886
  have hstable : (prefixWord ++ tailWord_409886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409886).length < 2 ^ (prefixWord ++ tailWord_409886).sum := by decide
  have hdescent : baseEnd_409886 < baseStart_409886 := by decide
  rcases family_descends (prefixWord ++ tailWord_409886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409948 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 5]
def baseStart_409948 : Nat := 118140960795 + 409948 * 2 ^ 59
def prefixEnd_409948 : Nat := 4983230072969 + 3 ^ 40 * 409948 * 2
def baseEnd_409948 : Nat := 93555718821985471228751

theorem tailTrace_409948 : CollatzResearch.WordTrace tailWord_409948 prefixEnd_409948 93555718821985471228751 := by
  unfold tailWord_409948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476015959417942194723249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9968021279223922926297665 7476015959417942194723249)
  ·
    refine ⟨5607011969563456646042437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7476015959417942194723249 5607011969563456646042437)
    ·
      refine ⟨1051314744293148121132957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5607011969563456646042437 1051314744293148121132957)
      ·
        refine ⟨394243029109930545424859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1051314744293148121132957 394243029109930545424859)
        ·
          refine ⟨591364543664895818137289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394243029109930545424859 591364543664895818137289)
          ·
            refine ⟨443523407748671863602967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591364543664895818137289 443523407748671863602967)
            ·
              refine ⟨665285111623007795404451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443523407748671863602967 665285111623007795404451)
              ·
                refine ⟨997927667434511693106677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 665285111623007795404451 997927667434511693106677)
                ·
                  refine ⟨93555718821985471228751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 997927667434511693106677 93555718821985471228751)
                  ·
                    rfl

theorem cell21_409948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_409948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409948 prefixEnd_409948 := by exact prefixLift 409948
  have htrace : WordTrace (prefixWord ++ tailWord_409948) baseStart_409948 baseEnd_409948 := by
    simpa [prefixWord, tailWord_409948, baseEnd_409948] using wordTrace_append hprefix tailTrace_409948
  have hstable : (prefixWord ++ tailWord_409948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409948).length < 2 ^ (prefixWord ++ tailWord_409948).sum := by decide
  have hdescent : baseEnd_409948 < baseStart_409948 := by decide
  rcases family_descends (prefixWord ++ tailWord_409948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409959 : List Nat := [1, 1, 5, 1, 3, 2, 2, 6]
def baseStart_409959 : Nat := 118140960795 + 409959 * 2 ^ 59
def prefixEnd_409959 : Nat := 4983230072969 + 3 ^ 40 * 409959 * 2
def baseEnd_409959 : Nat := 31186076390617298848465

theorem tailTrace_409959 : CollatzResearch.WordTrace tailWord_409959 prefixEnd_409959 31186076390617298848465 := by
  unfold tailWord_409959
  simp only [CollatzResearch.WordTrace]
  refine ⟨14952433121796033268096931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9968288747864022178731287 14952433121796033268096931)
  ·
    refine ⟨22428649682694049902145397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14952433121796033268096931 22428649682694049902145397)
    ·
      refine ⟨2102685907752567178326131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22428649682694049902145397 2102685907752567178326131)
      ·
        refine ⟨3154028861628850767489197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102685907752567178326131 3154028861628850767489197)
        ·
          refine ⟨1182760823110819037808449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3154028861628850767489197 1182760823110819037808449)
          ·
            refine ⟨887070617333114278356337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1182760823110819037808449 887070617333114278356337)
            ·
              refine ⟨665302962999835708767253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887070617333114278356337 665302962999835708767253)
              ·
                refine ⟨31186076390617298848465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 665302962999835708767253 31186076390617298848465)
                ·
                  rfl

theorem cell21_409959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 6].length) (baseStart_409959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409959 prefixEnd_409959 := by exact prefixLift 409959
  have htrace : WordTrace (prefixWord ++ tailWord_409959) baseStart_409959 baseEnd_409959 := by
    simpa [prefixWord, tailWord_409959, baseEnd_409959] using wordTrace_append hprefix tailTrace_409959
  have hstable : (prefixWord ++ tailWord_409959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409959).length < 2 ^ (prefixWord ++ tailWord_409959).sum := by decide
  have hdescent : baseEnd_409959 < baseStart_409959 := by decide
  rcases family_descends (prefixWord ++ tailWord_409959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409962 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_409962 : Nat := 118140960795 + 409962 * 2 ^ 59
def prefixEnd_409962 : Nat := 4983230072969 + 3 ^ 40 * 409962 * 2
def baseEnd_409962 : Nat := 93558913812724557995389

theorem tailTrace_409962 : CollatzResearch.WordTrace tailWord_409962 prefixEnd_409962 93558913812724557995389 := by
  unfold tailWord_409962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3738135635196291195114035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9968361693856776520304093 3738135635196291195114035)
  ·
    refine ⟨5607203452794436792671053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3738135635196291195114035 5607203452794436792671053)
    ·
      refine ⟨2102701294797913797251645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5607203452794436792671053 2102701294797913797251645)
      ·
        refine ⟨788512985549217673969367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2102701294797913797251645 788512985549217673969367)
        ·
          refine ⟨1182769478323826510954051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788512985549217673969367 1182769478323826510954051)
          ·
            refine ⟨1774154217485739766431077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182769478323826510954051 1774154217485739766431077)
            ·
              refine ⟨332653915778576206205827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1774154217485739766431077 332653915778576206205827)
              ·
                refine ⟨498980873667864309308741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332653915778576206205827 498980873667864309308741)
                ·
                  refine ⟨93558913812724557995389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 498980873667864309308741 93558913812724557995389)
                  ·
                    rfl

theorem cell21_409962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_409962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_409962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_409962 prefixEnd_409962 := by exact prefixLift 409962
  have htrace : WordTrace (prefixWord ++ tailWord_409962) baseStart_409962 baseEnd_409962 := by
    simpa [prefixWord, tailWord_409962, baseEnd_409962] using wordTrace_append hprefix tailTrace_409962
  have hstable : (prefixWord ++ tailWord_409962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409962).length < 2 ^ (prefixWord ++ tailWord_409962).sum := by decide
  have hdescent : baseEnd_409962 < baseStart_409962 := by decide
  rcases family_descends (prefixWord ++ tailWord_409962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410007 : List Nat := [1, 1, 3, 3, 1, 1, 6, 2, 3]
def baseStart_410007 : Nat := 118140960795 + 410007 * 2 ^ 59
def prefixEnd_410007 : Nat := 4983230072969 + 3 ^ 40 * 410007 * 2
def baseEnd_410007 : Nat := 93569183425814479745297

theorem tailTrace_410007 : CollatzResearch.WordTrace tailWord_410007 prefixEnd_410007 93569183425814479745297 := by
  unfold tailWord_410007
  simp only [CollatzResearch.WordTrace]
  refine ⟨14954183825622137465844275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9969455883748091643896183 14954183825622137465844275)
  ·
    refine ⟨22431275738433206198766413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14954183825622137465844275 22431275738433206198766413)
    ·
      refine ⟨8411728401912452324537405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22431275738433206198766413 8411728401912452324537405)
      ·
        refine ⟨3154398150717169621701527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8411728401912452324537405 3154398150717169621701527)
        ·
          refine ⟨4731597226075754432552291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154398150717169621701527 4731597226075754432552291)
          ·
            refine ⟨7097395839113631648828437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4731597226075754432552291 7097395839113631648828437)
            ·
              refine ⟨332690429958451483538833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7097395839113631648828437 332690429958451483538833)
              ·
                refine ⟨249517822468838612654125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 332690429958451483538833 249517822468838612654125)
                ·
                  refine ⟨93569183425814479745297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249517822468838612654125 93569183425814479745297)
                  ·
                    rfl

theorem cell21_410007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 3].length) (baseStart_410007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410007 prefixEnd_410007 := by exact prefixLift 410007
  have htrace : WordTrace (prefixWord ++ tailWord_410007) baseStart_410007 baseEnd_410007 := by
    simpa [prefixWord, tailWord_410007, baseEnd_410007] using wordTrace_append hprefix tailTrace_410007
  have hstable : (prefixWord ++ tailWord_410007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410007).length < 2 ^ (prefixWord ++ tailWord_410007).sum := by decide
  have hdescent : baseEnd_410007 < baseStart_410007 := by decide
  rcases family_descends (prefixWord ++ tailWord_410007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410173 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 4]
def baseStart_410173 : Nat := 118140960795 + 410173 * 2 ^ 59
def prefixEnd_410173 : Nat := 4983230072969 + 3 ^ 40 * 410173 * 2
def baseEnd_410173 : Nat := 93607066887435079978291

theorem tailTrace_410173 : CollatzResearch.WordTrace tailWord_410173 prefixEnd_410173 93607066887435079978291 := by
  unfold tailWord_410173
  simp only [CollatzResearch.WordTrace]
  refine ⟨14960238343020747816387173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9973492228680498544258115 14960238343020747816387173)
  ·
    refine ⟨2805044689316390215572595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14960238343020747816387173 2805044689316390215572595)
    ·
      refine ⟨4207567033974585323358893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2805044689316390215572595 4207567033974585323358893)
      ·
        refine ⟨1577837637740469496259585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4207567033974585323358893 1577837637740469496259585)
        ·
          refine ⟨1183378228305352122194689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1577837637740469496259585 1183378228305352122194689)
          ·
            refine ⟨887533671229014091646017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1183378228305352122194689 887533671229014091646017)
            ·
              refine ⟨665650253421760568734513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887533671229014091646017 665650253421760568734513)
              ·
                refine ⟨499237690066320426550885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665650253421760568734513 499237690066320426550885)
                ·
                  refine ⟨93607066887435079978291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 499237690066320426550885 93607066887435079978291)
                  ·
                    rfl

theorem cell21_410173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_410173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410173 prefixEnd_410173 := by exact prefixLift 410173
  have htrace : WordTrace (prefixWord ++ tailWord_410173) baseStart_410173 baseEnd_410173 := by
    simpa [prefixWord, tailWord_410173, baseEnd_410173] using wordTrace_append hprefix tailTrace_410173
  have hstable : (prefixWord ++ tailWord_410173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410173).length < 2 ^ (prefixWord ++ tailWord_410173).sum := by decide
  have hdescent : baseEnd_410173 < baseStart_410173 := by decide
  rcases family_descends (prefixWord ++ tailWord_410173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410184 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_410184 : Nat := 118140960795 + 410184 * 2 ^ 59
def prefixEnd_410184 : Nat := 4983230072969 + 3 ^ 40 * 410184 * 2
def baseEnd_410184 : Nat := 93609577237301505294935

theorem tailTrace_410184 : CollatzResearch.WordTrace tailWord_410184 prefixEnd_410184 93609577237301505294935 := by
  unfold tailWord_410184
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480319772990448347518803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9973759697320597796691737 7480319772990448347518803)
  ·
    refine ⟨11220479659485672521278205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7480319772990448347518803 11220479659485672521278205)
    ·
      refine ⟨4207679872307127195479327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11220479659485672521278205 4207679872307127195479327)
      ·
        refine ⟨6311519808460690793218991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4207679872307127195479327 6311519808460690793218991)
        ·
          refine ⟨9467279712691036189828487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6311519808460690793218991 9467279712691036189828487)
          ·
            refine ⟨14200919569036554284742731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9467279712691036189828487 14200919569036554284742731)
            ·
              refine ⟨21301379353554831427114097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14200919569036554284742731 21301379353554831427114097)
              ·
                refine ⟨15976034515166123570335573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21301379353554831427114097 15976034515166123570335573)
                ·
                  refine ⟨93609577237301505294935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15976034515166123570335573 93609577237301505294935)
                  ·
                    rfl

theorem cell21_410184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_410184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410184 prefixEnd_410184 := by exact prefixLift 410184
  have htrace : WordTrace (prefixWord ++ tailWord_410184) baseStart_410184 baseEnd_410184 := by
    simpa [prefixWord, tailWord_410184, baseEnd_410184] using wordTrace_append hprefix tailTrace_410184
  have hstable : (prefixWord ++ tailWord_410184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410184).length < 2 ^ (prefixWord ++ tailWord_410184).sum := by decide
  have hdescent : baseEnd_410184 < baseStart_410184 := by decide
  rcases family_descends (prefixWord ++ tailWord_410184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410204 : List Nat := [2, 2, 4, 1, 3, 1, 3, 5]
def baseStart_410204 : Nat := 118140960795 + 410204 * 2 ^ 59
def prefixEnd_410204 : Nat := 4983230072969 + 3 ^ 40 * 410204 * 2
def baseEnd_410204 : Nat := 31204713836595304987187

theorem tailTrace_410204 : CollatzResearch.WordTrace tailWord_410204 prefixEnd_410204 31204713836595304987187 := by
  unfold tailWord_410204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480684502954220055382833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9974246003938960073843777 7480684502954220055382833)
  ·
    refine ⟨5610513377215665041537125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7480684502954220055382833 5610513377215665041537125)
    ·
      refine ⟨1051971258227937195288211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5610513377215665041537125 1051971258227937195288211)
      ·
        refine ⟨1577956887341905792932317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051971258227937195288211 1577956887341905792932317)
        ·
          refine ⟨591733832753214672349619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1577956887341905792932317 591733832753214672349619)
          ·
            refine ⟨887600749129822008524429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591733832753214672349619 887600749129822008524429)
            ·
              refine ⟨332850280923683253196661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 887600749129822008524429 332850280923683253196661)
              ·
                refine ⟨31204713836595304987187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 332850280923683253196661 31204713836595304987187)
                ·
                  rfl

theorem cell21_410204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_410204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410204 prefixEnd_410204 := by exact prefixLift 410204
  have htrace : WordTrace (prefixWord ++ tailWord_410204) baseStart_410204 baseEnd_410204 := by
    simpa [prefixWord, tailWord_410204, baseEnd_410204] using wordTrace_append hprefix tailTrace_410204
  have hstable : (prefixWord ++ tailWord_410204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410204).length < 2 ^ (prefixWord ++ tailWord_410204).sum := by decide
  have hdescent : baseEnd_410204 < baseStart_410204 := by decide
  rcases family_descends (prefixWord ++ tailWord_410204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410215 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 6]
def baseStart_410215 : Nat := 118140960795 + 410215 * 2 ^ 59
def prefixEnd_410215 : Nat := 4983230072969 + 3 ^ 40 * 410215 * 2
def baseEnd_410215 : Nat := 93616651859652340278205

theorem tailTrace_410215 : CollatzResearch.WordTrace tailWord_410215 prefixEnd_410215 93616651859652340278205 := by
  unfold tailWord_410215
  simp only [CollatzResearch.WordTrace]
  refine ⟨14961770208868588989416099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9974513472579059326277399 14961770208868588989416099)
  ·
    refine ⟨22442655313302883484124149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14961770208868588989416099 22442655313302883484124149)
    ·
      refine ⟨2103998935622145326636639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22442655313302883484124149 2103998935622145326636639)
      ·
        refine ⟨3155998403433217989954959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103998935622145326636639 3155998403433217989954959)
        ·
          refine ⟨4733997605149826984932439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3155998403433217989954959 4733997605149826984932439)
          ·
            refine ⟨7100996407724740477398659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733997605149826984932439 7100996407724740477398659)
            ·
              refine ⟨10651494611587110716097989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7100996407724740477398659 10651494611587110716097989)
              ·
                refine ⟨1997155239672583259268373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10651494611587110716097989 1997155239672583259268373)
                ·
                  refine ⟨93616651859652340278205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1997155239672583259268373 93616651859652340278205)
                  ·
                    rfl

theorem cell21_410215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_410215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410215 prefixEnd_410215 := by exact prefixLift 410215
  have htrace : WordTrace (prefixWord ++ tailWord_410215) baseStart_410215 baseEnd_410215 := by
    simpa [prefixWord, tailWord_410215, baseEnd_410215] using wordTrace_append hprefix tailTrace_410215
  have hstable : (prefixWord ++ tailWord_410215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410215).length < 2 ^ (prefixWord ++ tailWord_410215).sum := by decide
  have hdescent : baseEnd_410215 < baseStart_410215 := by decide
  rcases family_descends (prefixWord ++ tailWord_410215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410291 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 6]
def baseStart_410291 : Nat := 118140960795 + 410291 * 2 ^ 59
def prefixEnd_410291 : Nat := 4983230072969 + 3 ^ 40 * 410291 * 2
def baseEnd_410291 : Nat := 93633996095093097011383

theorem tailTrace_410291 : CollatzResearch.WordTrace tailWord_410291 prefixEnd_410291 93633996095093097011383 := by
  unfold tailWord_410291
  simp only [CollatzResearch.WordTrace]
  refine ⟨14964542156593253969182727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9976361437728835979455151 14964542156593253969182727)
  ·
    refine ⟨22446813234889880953774091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14964542156593253969182727 22446813234889880953774091)
    ·
      refine ⟨33670219852334821430661137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22446813234889880953774091 33670219852334821430661137)
      ·
        refine ⟨25252664889251116072995853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33670219852334821430661137 25252664889251116072995853)
        ·
          refine ⟨9469749333469168527373445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25252664889251116072995853 9469749333469168527373445)
          ·
            refine ⟨1775578000025469098882521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9469749333469168527373445 1775578000025469098882521)
            ·
              refine ⟨1331683500019101824161891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1775578000025469098882521 1331683500019101824161891)
              ·
                refine ⟨1997525250028652736242837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331683500019101824161891 1997525250028652736242837)
                ·
                  refine ⟨93633996095093097011383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1997525250028652736242837 93633996095093097011383)
                  ·
                    rfl

theorem cell21_410291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_410291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410291 prefixEnd_410291 := by exact prefixLift 410291
  have htrace : WordTrace (prefixWord ++ tailWord_410291) baseStart_410291 baseEnd_410291 := by
    simpa [prefixWord, tailWord_410291, baseEnd_410291] using wordTrace_append hprefix tailTrace_410291
  have hstable : (prefixWord ++ tailWord_410291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410291).length < 2 ^ (prefixWord ++ tailWord_410291).sum := by decide
  have hdescent : baseEnd_410291 < baseStart_410291 := by decide
  rcases family_descends (prefixWord ++ tailWord_410291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410370 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_410370 : Nat := 118140960795 + 410370 * 2 ^ 59
def prefixEnd_410370 : Nat := 4983230072969 + 3 ^ 40 * 410370 * 2
def baseEnd_410370 : Nat := 93652024971406515194555

theorem tailTrace_410370 : CollatzResearch.WordTrace tailWord_410370 prefixEnd_410370 93652024971406515194555 := by
  unfold tailWord_410370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3741855880826762615327141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9978282348871366974205709 3741855880826762615327141)
  ·
    refine ⟨701597977655017990373839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3741855880826762615327141 701597977655017990373839)
    ·
      refine ⟨1052396966482526985560759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701597977655017990373839 1052396966482526985560759)
      ·
        refine ⟨1578595449723790478341139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052396966482526985560759 1578595449723790478341139)
        ·
          refine ⟨2367893174585685717511709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578595449723790478341139 2367893174585685717511709)
          ·
            refine ⟨887959940469632144066891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2367893174585685717511709 887959940469632144066891)
            ·
              refine ⟨1331939910704448216100337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887959940469632144066891 1331939910704448216100337)
              ·
                refine ⟨998954933028336162075253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331939910704448216100337 998954933028336162075253)
                ·
                  refine ⟨93652024971406515194555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 998954933028336162075253 93652024971406515194555)
                  ·
                    rfl

theorem cell21_410370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_410370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410370 prefixEnd_410370 := by exact prefixLift 410370
  have htrace : WordTrace (prefixWord ++ tailWord_410370) baseStart_410370 baseEnd_410370 := by
    simpa [prefixWord, tailWord_410370, baseEnd_410370] using wordTrace_append hprefix tailTrace_410370
  have hstable : (prefixWord ++ tailWord_410370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410370).length < 2 ^ (prefixWord ++ tailWord_410370).sum := by decide
  have hdescent : baseEnd_410370 < baseStart_410370 := by decide
  rcases family_descends (prefixWord ++ tailWord_410370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410438 : List Nat := [6, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_410438 : Nat := 118140960795 + 410438 * 2 ^ 59
def prefixEnd_410438 : Nat := 4983230072969 + 3 ^ 40 * 410438 * 2
def baseEnd_410438 : Nat := 93667543497853508061083

theorem tailTrace_410438 : CollatzResearch.WordTrace tailWord_410438 prefixEnd_410438 93667543497853508061083 := by
  unfold tailWord_410438
  simp only [CollatzResearch.WordTrace]
  refine ⟨467809490220646814836999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9979935791373798716522645 467809490220646814836999)
  ·
    refine ⟨701714235330970222255499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 467809490220646814836999 701714235330970222255499)
    ·
      refine ⟨1052571352996455333383249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701714235330970222255499 1052571352996455333383249)
      ·
        refine ⟨789428514747341500037437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1052571352996455333383249 789428514747341500037437)
        ·
          refine ⟨296035693030253062514039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 789428514747341500037437 296035693030253062514039)
          ·
            refine ⟨444053539545379593771059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296035693030253062514039 444053539545379593771059)
            ·
              refine ⟨666080309318069390656589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444053539545379593771059 666080309318069390656589)
              ·
                refine ⟨249780115994276021496221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 666080309318069390656589 249780115994276021496221)
                ·
                  refine ⟨93667543497853508061083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249780115994276021496221 93667543497853508061083)
                  ·
                    rfl

theorem cell21_410438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_410438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410438 prefixEnd_410438 := by exact prefixLift 410438
  have htrace : WordTrace (prefixWord ++ tailWord_410438) baseStart_410438 baseEnd_410438 := by
    simpa [prefixWord, tailWord_410438, baseEnd_410438] using wordTrace_append hprefix tailTrace_410438
  have hstable : (prefixWord ++ tailWord_410438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410438).length < 2 ^ (prefixWord ++ tailWord_410438).sum := by decide
  have hdescent : baseEnd_410438 < baseStart_410438 := by decide
  rcases family_descends (prefixWord ++ tailWord_410438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410457 : List Nat := [1, 2, 1, 2, 2, 4, 9]
def baseStart_410457 : Nat := 118140960795 + 410457 * 2 ^ 59
def prefixEnd_410457 : Nat := 4983230072969 + 3 ^ 40 * 410457 * 2
def baseEnd_410457 : Nat := 10407986617412633027153

theorem tailTrace_410457 : CollatzResearch.WordTrace tailWord_410457 prefixEnd_410457 10407986617412633027153 := by
  unfold tailWord_410457
  simp only [CollatzResearch.WordTrace]
  refine ⟨14970596673991864319725625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9980397782661242879817083 14970596673991864319725625)
  ·
    refine ⟨11227947505493898239794219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14970596673991864319725625 11227947505493898239794219)
    ·
      refine ⟨16841921258240847359691329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11227947505493898239794219 16841921258240847359691329)
      ·
        refine ⟨12631440943680635519768497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16841921258240847359691329 12631440943680635519768497)
        ·
          refine ⟨9473580707760476639826373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12631440943680635519768497 9473580707760476639826373)
          ·
            refine ⟨1776296382705089369967445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9473580707760476639826373 1776296382705089369967445)
            ·
              refine ⟨10407986617412633027153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1776296382705089369967445 10407986617412633027153)
              ·
                rfl

theorem cell21_410457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 9].length) (baseStart_410457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410457 prefixEnd_410457 := by exact prefixLift 410457
  have htrace : WordTrace (prefixWord ++ tailWord_410457) baseStart_410457 baseEnd_410457 := by
    simpa [prefixWord, tailWord_410457, baseEnd_410457] using wordTrace_append hprefix tailTrace_410457
  have hstable : (prefixWord ++ tailWord_410457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410457).length < 2 ^ (prefixWord ++ tailWord_410457).sum := by decide
  have hdescent : baseEnd_410457 < baseStart_410457 := by decide
  rcases family_descends (prefixWord ++ tailWord_410457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410460 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 6]
def baseStart_410460 : Nat := 118140960795 + 410460 * 2 ^ 59
def prefixEnd_410460 : Nat := 4983230072969 + 3 ^ 40 * 410460 * 2
def baseEnd_410460 : Nat := 93672564197586358694371

theorem tailTrace_410460 : CollatzResearch.WordTrace tailWord_410460 prefixEnd_410460 93672564197586358694371 := by
  unfold tailWord_410460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7485353046490497916042417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9980470728653997221389889 7485353046490497916042417)
  ·
    refine ⟨5614014784867873437031813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7485353046490497916042417 5614014784867873437031813)
    ·
      refine ⟨1052627772162726269443465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5614014784867873437031813 1052627772162726269443465)
      ·
        refine ⟨789470829122044702082599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1052627772162726269443465 789470829122044702082599)
        ·
          refine ⟨1184206243683067053123899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789470829122044702082599 1184206243683067053123899)
          ·
            refine ⟨1776309365524600579685849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184206243683067053123899 1776309365524600579685849)
            ·
              refine ⟨1332232024143450434764387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776309365524600579685849 1332232024143450434764387)
              ·
                refine ⟨1998348036215175652146581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1332232024143450434764387 1998348036215175652146581)
                ·
                  refine ⟨93672564197586358694371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1998348036215175652146581 93672564197586358694371)
                  ·
                    rfl

theorem cell21_410460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_410460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410460 prefixEnd_410460 := by exact prefixLift 410460
  have htrace : WordTrace (prefixWord ++ tailWord_410460) baseStart_410460 baseEnd_410460 := by
    simpa [prefixWord, tailWord_410460, baseEnd_410460] using wordTrace_append hprefix tailTrace_410460
  have hstable : (prefixWord ++ tailWord_410460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410460).length < 2 ^ (prefixWord ++ tailWord_410460).sum := by decide
  have hdescent : baseEnd_410460 < baseStart_410460 := by decide
  rcases family_descends (prefixWord ++ tailWord_410460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410685 : List Nat := [1, 4, 1, 3, 1, 11]
def baseStart_410685 : Nat := 118140960795 + 410685 * 2 ^ 59
def prefixEnd_410685 : Nat := 4983230072969 + 3 ^ 40 * 410685 * 2
def baseEnd_410685 : Nat := 3471256009742072868293

theorem tailTrace_410685 : CollatzResearch.WordTrace tailWord_410685 prefixEnd_410685 3471256009742072868293 := by
  unfold tailWord_410685
  simp only [CollatzResearch.WordTrace]
  refine ⟨14978912517165859259025509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9985941678110572839350339 14978912517165859259025509)
  ·
    refine ⟨2808546096968598611067283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14978912517165859259025509 2808546096968598611067283)
    ·
      refine ⟨4212819145452897916600925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2808546096968598611067283 4212819145452897916600925)
      ·
        refine ⟨1579807179544836718725347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4212819145452897916600925 1579807179544836718725347)
        ·
          refine ⟨2369710769317255078088021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579807179544836718725347 2369710769317255078088021)
          ·
            refine ⟨3471256009742072868293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2369710769317255078088021 3471256009742072868293)
            ·
              rfl

theorem cell21_410685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 11].length) (baseStart_410685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410685 prefixEnd_410685 := by exact prefixLift 410685
  have htrace : WordTrace (prefixWord ++ tailWord_410685) baseStart_410685 baseEnd_410685 := by
    simpa [prefixWord, tailWord_410685, baseEnd_410685] using wordTrace_append hprefix tailTrace_410685
  have hstable : (prefixWord ++ tailWord_410685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410685).length < 2 ^ (prefixWord ++ tailWord_410685).sum := by decide
  have hdescent : baseEnd_410685 < baseStart_410685 := by decide
  rcases family_descends (prefixWord ++ tailWord_410685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410778 : List Nat := [3, 1, 1, 5, 1, 2, 1, 7]
def baseStart_410778 : Nat := 118140960795 + 410778 * 2 ^ 59
def prefixEnd_410778 : Nat := 4983230072969 + 3 ^ 40 * 410778 * 2
def baseEnd_410778 : Nat := 31248378710029490797907

theorem tailTrace_410778 : CollatzResearch.WordTrace tailWord_410778 prefixEnd_410778 31248378710029490797907 := by
  unfold tailWord_410778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745576126457234035540247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9988203003885957428107325 3745576126457234035540247)
  ·
    refine ⟨5618364189685851053310371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745576126457234035540247 5618364189685851053310371)
    ·
      refine ⟨8427546284528776579965557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5618364189685851053310371 8427546284528776579965557)
      ·
        refine ⟨790082464174572804371771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8427546284528776579965557 790082464174572804371771)
        ·
          refine ⟨1185123696261859206557657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790082464174572804371771 1185123696261859206557657)
          ·
            refine ⟨888842772196394404918243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185123696261859206557657 888842772196394404918243)
            ·
              refine ⟨1333264158294591607377365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888842772196394404918243 1333264158294591607377365)
              ·
                refine ⟨31248378710029490797907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1333264158294591607377365 31248378710029490797907)
                ·
                  rfl

theorem cell21_410778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_410778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410778 prefixEnd_410778 := by exact prefixLift 410778
  have htrace : WordTrace (prefixWord ++ tailWord_410778) baseStart_410778 baseEnd_410778 := by
    simpa [prefixWord, tailWord_410778, baseEnd_410778] using wordTrace_append hprefix tailTrace_410778
  have hstable : (prefixWord ++ tailWord_410778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410778).length < 2 ^ (prefixWord ++ tailWord_410778).sum := by decide
  have hdescent : baseEnd_410778 < baseStart_410778 := by decide
  rcases family_descends (prefixWord ++ tailWord_410778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410809 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 5]
def baseStart_410809 : Nat := 118140960795 + 410809 * 2 ^ 59
def prefixEnd_410809 : Nat := 4983230072969 + 3 ^ 40 * 410809 * 2
def baseEnd_410809 : Nat := 93752210752439307376991

theorem tailTrace_410809 : CollatzResearch.WordTrace tailWord_410809 prefixEnd_410809 93752210752439307376991 := by
  unfold tailWord_410809
  simp only [CollatzResearch.WordTrace]
  refine ⟨14983435168716628436539481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9988956779144418957692987 14983435168716628436539481)
  ·
    refine ⟨11237576376537471327404611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14983435168716628436539481 11237576376537471327404611)
    ·
      refine ⟨16856364564806206991106917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11237576376537471327404611 16856364564806206991106917)
      ·
        refine ⟨3160568355901163810832547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16856364564806206991106917 3160568355901163810832547)
        ·
          refine ⟨4740852533851745716248821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3160568355901163810832547 4740852533851745716248821)
          ·
            refine ⟨444454925048601160898327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4740852533851745716248821 444454925048601160898327)
            ·
              refine ⟨666682387572901741347491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444454925048601160898327 666682387572901741347491)
              ·
                refine ⟨1000023581359352612021237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666682387572901741347491 1000023581359352612021237)
                ·
                  refine ⟨93752210752439307376991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1000023581359352612021237 93752210752439307376991)
                  ·
                    rfl

theorem cell21_410809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_410809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410809 prefixEnd_410809 := by exact prefixLift 410809
  have htrace : WordTrace (prefixWord ++ tailWord_410809) baseStart_410809 baseEnd_410809 := by
    simpa [prefixWord, tailWord_410809, baseEnd_410809] using wordTrace_append hprefix tailTrace_410809
  have hstable : (prefixWord ++ tailWord_410809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410809).length < 2 ^ (prefixWord ++ tailWord_410809).sum := by decide
  have hdescent : baseEnd_410809 < baseStart_410809 := by decide
  rcases family_descends (prefixWord ++ tailWord_410809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410958 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_410958 : Nat := 118140960795 + 410958 * 2 ^ 59
def prefixEnd_410958 : Nat := 4983230072969 + 3 ^ 40 * 410958 * 2
def baseEnd_410958 : Nat := 93786214582448159393353

theorem tailTrace_410958 : CollatzResearch.WordTrace tailWord_410958 prefixEnd_410958 93786214582448159393353 := by
  unfold tailWord_410958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873608705647103360464191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9992579763451217922475685 1873608705647103360464191)
  ·
    refine ⟨2810413058470655040696287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1873608705647103360464191 2810413058470655040696287)
    ·
      refine ⟨4215619587705982561044431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2810413058470655040696287 4215619587705982561044431)
      ·
        refine ⟨6323429381558973841566647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4215619587705982561044431 6323429381558973841566647)
        ·
          refine ⟨9485144072338460762349971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6323429381558973841566647 9485144072338460762349971)
          ·
            refine ⟨14227716108507691143524957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9485144072338460762349971 14227716108507691143524957)
            ·
              refine ⟨5335393540690384178821859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14227716108507691143524957 5335393540690384178821859)
              ·
                refine ⟨8003090311035576268232789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5335393540690384178821859 8003090311035576268232789)
                ·
                  refine ⟨93786214582448159393353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8003090311035576268232789 93786214582448159393353)
                  ·
                    rfl

theorem cell21_410958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_410958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410958 prefixEnd_410958 := by exact prefixLift 410958
  have htrace : WordTrace (prefixWord ++ tailWord_410958) baseStart_410958 baseEnd_410958 := by
    simpa [prefixWord, tailWord_410958, baseEnd_410958] using wordTrace_append hprefix tailTrace_410958
  have hstable : (prefixWord ++ tailWord_410958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410958).length < 2 ^ (prefixWord ++ tailWord_410958).sum := by decide
  have hdescent : baseEnd_410958 < baseStart_410958 := by decide
  rcases family_descends (prefixWord ++ tailWord_410958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410989 : List Nat := [1, 5, 1, 1, 1, 3, 1, 8]
def baseStart_410989 : Nat := 118140960795 + 410989 * 2 ^ 59
def prefixEnd_410989 : Nat := 4983230072969 + 3 ^ 40 * 410989 * 2
def baseEnd_410989 : Nat := 31264429734932998125541

theorem tailTrace_410989 : CollatzResearch.WordTrace tailWord_410989 prefixEnd_410989 31264429734932998125541 := by
  unfold tailWord_410989
  simp only [CollatzResearch.WordTrace]
  refine ⟨14990000308064519178092021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9993333538709679452061347 14990000308064519178092021)
  ·
    refine ⟨1405312528881048672946127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14990000308064519178092021 1405312528881048672946127)
    ·
      refine ⟨2107968793321573009419191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1405312528881048672946127 2107968793321573009419191)
      ·
        refine ⟨3161953189982359514128787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107968793321573009419191 3161953189982359514128787)
        ·
          refine ⟨4742929784973539271193181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3161953189982359514128787 4742929784973539271193181)
          ·
            refine ⟨1778598669365077226697443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4742929784973539271193181 1778598669365077226697443)
            ·
              refine ⟨2667898004047615840046165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1778598669365077226697443 2667898004047615840046165)
              ·
                refine ⟨31264429734932998125541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2667898004047615840046165 31264429734932998125541)
                ·
                  rfl

theorem cell21_410989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 8].length) (baseStart_410989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_410989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_410989 prefixEnd_410989 := by exact prefixLift 410989
  have htrace : WordTrace (prefixWord ++ tailWord_410989) baseStart_410989 baseEnd_410989 := by
    simpa [prefixWord, tailWord_410989, baseEnd_410989] using wordTrace_append hprefix tailTrace_410989
  have hstable : (prefixWord ++ tailWord_410989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410989).length < 2 ^ (prefixWord ++ tailWord_410989).sum := by decide
  have hdescent : baseEnd_410989 < baseStart_410989 := by decide
  rcases family_descends (prefixWord ++ tailWord_410989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411003 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 7]
def baseStart_411003 : Nat := 118140960795 + 411003 * 2 ^ 59
def prefixEnd_411003 : Nat := 4983230072969 + 3 ^ 40 * 411003 * 2
def baseEnd_411003 : Nat := 93796484195538081143261

theorem tailTrace_411003 : CollatzResearch.WordTrace tailWord_411003 prefixEnd_411003 93796484195538081143261 := by
  unfold tailWord_411003
  simp only [CollatzResearch.WordTrace]
  refine ⟨14990510930013799569101663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9993673953342533046067775 14990510930013799569101663)
  ·
    refine ⟨22485766395020699353652495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14990510930013799569101663 22485766395020699353652495)
    ·
      refine ⟨33728649592531049030478743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22485766395020699353652495 33728649592531049030478743)
      ·
        refine ⟨50592974388796573545718115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33728649592531049030478743 50592974388796573545718115)
        ·
          refine ⟨75889461583194860318577173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50592974388796573545718115 75889461583194860318577173)
          ·
            refine ⟨3557318511712259077433305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75889461583194860318577173 3557318511712259077433305)
            ·
              refine ⟨2667988883784194308074979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3557318511712259077433305 2667988883784194308074979)
              ·
                refine ⟨4001983325676291462112469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667988883784194308074979 4001983325676291462112469)
                ·
                  refine ⟨93796484195538081143261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4001983325676291462112469 93796484195538081143261)
                  ·
                    rfl

theorem cell21_411003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_411003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411003 prefixEnd_411003 := by exact prefixLift 411003
  have htrace : WordTrace (prefixWord ++ tailWord_411003) baseStart_411003 baseEnd_411003 := by
    simpa [prefixWord, tailWord_411003, baseEnd_411003] using wordTrace_append hprefix tailTrace_411003
  have hstable : (prefixWord ++ tailWord_411003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411003).length < 2 ^ (prefixWord ++ tailWord_411003).sum := by decide
  have hdescent : baseEnd_411003 < baseStart_411003 := by decide
  rcases family_descends (prefixWord ++ tailWord_411003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411079 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 7]
def baseStart_411079 : Nat := 118140960795 + 411079 * 2 ^ 59
def prefixEnd_411079 : Nat := 4983230072969 + 3 ^ 40 * 411079 * 2
def baseEnd_411079 : Nat := 93813828430978837876439

theorem tailTrace_411079 : CollatzResearch.WordTrace tailWord_411079 prefixEnd_411079 93813828430978837876439 := by
  unfold tailWord_411079
  simp only [CollatzResearch.WordTrace]
  refine ⟨14993282877738464548868291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9995521918492309699245527 14993282877738464548868291)
  ·
    refine ⟨22489924316607696823302437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14993282877738464548868291 22489924316607696823302437)
    ·
      refine ⟨4216860809363943154369207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22489924316607696823302437 4216860809363943154369207)
      ·
        refine ⟨6325291214045914731553811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216860809363943154369207 6325291214045914731553811)
        ·
          refine ⟨9487936821068872097330717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6325291214045914731553811 9487936821068872097330717)
          ·
            refine ⟨3557976307900827036499019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9487936821068872097330717 3557976307900827036499019)
            ·
              refine ⟨5336964461851240554748529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3557976307900827036499019 5336964461851240554748529)
              ·
                refine ⟨4002723346388430416061397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5336964461851240554748529 4002723346388430416061397)
                ·
                  refine ⟨93813828430978837876439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4002723346388430416061397 93813828430978837876439)
                  ·
                    rfl

theorem cell21_411079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_411079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411079 prefixEnd_411079 := by exact prefixLift 411079
  have htrace : WordTrace (prefixWord ++ tailWord_411079) baseStart_411079 baseEnd_411079 := by
    simpa [prefixWord, tailWord_411079, baseEnd_411079] using wordTrace_append hprefix tailTrace_411079
  have hstable : (prefixWord ++ tailWord_411079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411079).length < 2 ^ (prefixWord ++ tailWord_411079).sum := by decide
  have hdescent : baseEnd_411079 < baseStart_411079 := by decide
  rcases family_descends (prefixWord ++ tailWord_411079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411265 : List Nat := [1, 2, 4, 2, 1, 2, 2, 4, 3]
def baseStart_411265 : Nat := 118140960795 + 411265 * 2 ^ 59
def prefixEnd_411265 : Nat := 4983230072969 + 3 ^ 40 * 411265 * 2
def baseEnd_411265 : Nat := 93856276165083847776059

theorem tailTrace_411265 : CollatzResearch.WordTrace tailWord_411265 prefixEnd_411265 93856276165083847776059 := by
  unfold tailWord_411265
  simp only [CollatzResearch.WordTrace]
  refine ⟨15000066855064618315139249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10000044570043078876759499 15000066855064618315139249)
  ·
    refine ⟨11250050141298463736354437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15000066855064618315139249 11250050141298463736354437)
    ·
      refine ⟨2109384401493461950566457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11250050141298463736354437 2109384401493461950566457)
      ·
        refine ⟨1582038301120096462924843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2109384401493461950566457 1582038301120096462924843)
        ·
          refine ⟨2373057451680144694387265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582038301120096462924843 2373057451680144694387265)
          ·
            refine ⟨1779793088760108520790449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2373057451680144694387265 1779793088760108520790449)
            ·
              refine ⟨1334844816570081390592837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1779793088760108520790449 1334844816570081390592837)
              ·
                refine ⟨250283403106890260736157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1334844816570081390592837 250283403106890260736157)
                ·
                  refine ⟨93856276165083847776059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250283403106890260736157 93856276165083847776059)
                  ·
                    rfl

theorem cell21_411265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 4, 3].length) (baseStart_411265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411265 prefixEnd_411265 := by exact prefixLift 411265
  have htrace : WordTrace (prefixWord ++ tailWord_411265) baseStart_411265 baseEnd_411265 := by
    simpa [prefixWord, tailWord_411265, baseEnd_411265] using wordTrace_append hprefix tailTrace_411265
  have hstable : (prefixWord ++ tailWord_411265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411265).length < 2 ^ (prefixWord ++ tailWord_411265).sum := by decide
  have hdescent : baseEnd_411265 < baseStart_411265 := by decide
  rcases family_descends (prefixWord ++ tailWord_411265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411276 : List Nat := [2, 2, 1, 2, 1, 1, 4, 8]
def baseStart_411276 : Nat := 118140960795 + 411276 * 2 ^ 59
def prefixEnd_411276 : Nat := 4983230072969 + 3 ^ 40 * 411276 * 2
def baseEnd_411276 : Nat := 31286262171650091030901

theorem tailTrace_411276 : CollatzResearch.WordTrace tailWord_411276 prefixEnd_411276 31286262171650091030901 := by
  unfold tailWord_411276
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500234029012383596894841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10000312038683178129193121 7500234029012383596894841)
  ·
    refine ⟨5625175521759287697671131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7500234029012383596894841 5625175521759287697671131)
    ·
      refine ⟨8437763282638931546506697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5625175521759287697671131 8437763282638931546506697)
      ·
        refine ⟨6328322461979198659880023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8437763282638931546506697 6328322461979198659880023)
        ·
          refine ⟨9492483692968797989820035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6328322461979198659880023 9492483692968797989820035)
          ·
            refine ⟨14238725539453196984730053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9492483692968797989820035 14238725539453196984730053)
            ·
              refine ⟨2669761038647474434636885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14238725539453196984730053 2669761038647474434636885)
              ·
                refine ⟨31286262171650091030901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2669761038647474434636885 31286262171650091030901)
                ·
                  rfl

theorem cell21_411276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_411276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411276 prefixEnd_411276 := by exact prefixLift 411276
  have htrace : WordTrace (prefixWord ++ tailWord_411276) baseStart_411276 baseEnd_411276 := by
    simpa [prefixWord, tailWord_411276, baseEnd_411276] using wordTrace_append hprefix tailTrace_411276
  have hstable : (prefixWord ++ tailWord_411276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411276).length < 2 ^ (prefixWord ++ tailWord_411276).sum := by decide
  have hdescent : baseEnd_411276 < baseStart_411276 := by decide
  rcases family_descends (prefixWord ++ tailWord_411276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411324 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 5]
def baseStart_411324 : Nat := 118140960795 + 411324 * 2 ^ 59
def prefixEnd_411324 : Nat := 4983230072969 + 3 ^ 40 * 411324 * 2
def baseEnd_411324 : Nat := 93869740768912856292605

theorem tailTrace_411324 : CollatzResearch.WordTrace tailWord_411324 prefixEnd_411324 93869740768912856292605 := by
  unfold tailWord_411324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7501109380925435695768513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10001479174567247594358017 7501109380925435695768513)
  ·
    refine ⟨5625832035694076771826385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7501109380925435695768513 5625832035694076771826385)
    ·
      refine ⟨4219374026770557578869789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5625832035694076771826385 4219374026770557578869789)
      ·
        refine ⟨1582265260038959092076171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4219374026770557578869789 1582265260038959092076171)
        ·
          refine ⟨2373397890058438638114257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582265260038959092076171 2373397890058438638114257)
          ·
            refine ⟨1780048417543828978585693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2373397890058438638114257 1780048417543828978585693)
            ·
              refine ⟨667518156578935866969635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1780048417543828978585693 667518156578935866969635)
              ·
                refine ⟨1001277234868403800454453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667518156578935866969635 1001277234868403800454453)
                ·
                  refine ⟨93869740768912856292605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1001277234868403800454453 93869740768912856292605)
                  ·
                    rfl

theorem cell21_411324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_411324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411324 prefixEnd_411324 := by exact prefixLift 411324
  have htrace : WordTrace (prefixWord ++ tailWord_411324) baseStart_411324 baseEnd_411324 := by
    simpa [prefixWord, tailWord_411324, baseEnd_411324] using wordTrace_append hprefix tailTrace_411324
  have hstable : (prefixWord ++ tailWord_411324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411324).length < 2 ^ (prefixWord ++ tailWord_411324).sum := by decide
  have hdescent : baseEnd_411324 < baseStart_411324 := by decide
  rcases family_descends (prefixWord ++ tailWord_411324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411330 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_411330 : Nat := 118140960795 + 411330 * 2 ^ 59
def prefixEnd_411330 : Nat := 4983230072969 + 3 ^ 40 * 411330 * 2
def baseEnd_411330 : Nat := 93871110050658179192593

theorem tailTrace_411330 : CollatzResearch.WordTrace tailWord_411330 prefixEnd_411330 93871110050658179192593 := by
  unfold tailWord_411330
  simp only [CollatzResearch.WordTrace]
  refine ⟨3750609399957283604063861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10001625066552756277503629 3750609399957283604063861)
  ·
    refine ⟨351619631245995337880987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3750609399957283604063861 351619631245995337880987)
    ·
      refine ⟨527429446868993006821481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351619631245995337880987 527429446868993006821481)
      ·
        refine ⟨395572085151744755116111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527429446868993006821481 395572085151744755116111)
        ·
          refine ⟨593358127727617132674167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395572085151744755116111 593358127727617132674167)
          ·
            refine ⟨890037191591425699011251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593358127727617132674167 890037191591425699011251)
            ·
              refine ⟨1335055787387138548516877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890037191591425699011251 1335055787387138548516877)
              ·
                refine ⟨500645920270176955693829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1335055787387138548516877 500645920270176955693829)
                ·
                  refine ⟨93871110050658179192593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 500645920270176955693829 93871110050658179192593)
                  ·
                    rfl

theorem cell21_411330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_411330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411330 prefixEnd_411330 := by exact prefixLift 411330
  have htrace : WordTrace (prefixWord ++ tailWord_411330) baseStart_411330 baseEnd_411330 := by
    simpa [prefixWord, tailWord_411330, baseEnd_411330] using wordTrace_append hprefix tailTrace_411330
  have hstable : (prefixWord ++ tailWord_411330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411330).length < 2 ^ (prefixWord ++ tailWord_411330).sum := by decide
  have hdescent : baseEnd_411330 < baseStart_411330 := by decide
  rcases family_descends (prefixWord ++ tailWord_411330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411352 : List Nat := [2, 1, 2, 2, 3, 1, 1, 9]
def baseStart_411352 : Nat := 118140960795 + 411352 * 2 ^ 59
def prefixEnd_411352 : Nat := 4983230072969 + 3 ^ 40 * 411352 * 2
def baseEnd_411352 : Nat := 31292043583463676608627

theorem tailTrace_411352 : CollatzResearch.WordTrace tailWord_411352 prefixEnd_411352 31292043583463676608627 := by
  unfold tailWord_411352
  simp only [CollatzResearch.WordTrace]
  refine ⟨7501620002874716086778155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10002160003832954782370873 7501620002874716086778155)
  ·
    refine ⟨11252430004312074130167233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7501620002874716086778155 11252430004312074130167233)
    ·
      refine ⟨8439322503234055597625425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11252430004312074130167233 8439322503234055597625425)
      ·
        refine ⟨6329491877425541698219069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8439322503234055597625425 6329491877425541698219069)
        ·
          refine ⟨2373559454034578136832151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6329491877425541698219069 2373559454034578136832151)
          ·
            refine ⟨3560339181051867205248227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373559454034578136832151 3560339181051867205248227)
            ·
              refine ⟨5340508771577800807872341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560339181051867205248227 5340508771577800807872341)
              ·
                refine ⟨31292043583463676608627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5340508771577800807872341 31292043583463676608627)
                ·
                  rfl

theorem cell21_411352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_411352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411352 prefixEnd_411352 := by exact prefixLift 411352
  have htrace : WordTrace (prefixWord ++ tailWord_411352) baseStart_411352 baseEnd_411352 := by
    simpa [prefixWord, tailWord_411352, baseEnd_411352] using wordTrace_append hprefix tailTrace_411352
  have hstable : (prefixWord ++ tailWord_411352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411352).length < 2 ^ (prefixWord ++ tailWord_411352).sum := by decide
  have hdescent : baseEnd_411352 < baseStart_411352 := by decide
  rcases family_descends (prefixWord ++ tailWord_411352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411397 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 10]
def baseStart_411397 : Nat := 118140960795 + 411397 * 2 ^ 59
def prefixEnd_411397 : Nat := 4983230072969 + 3 ^ 40 * 411397 * 2
def baseEnd_411397 : Nat := 93886400363480951575789

theorem tailTrace_411397 : CollatzResearch.WordTrace tailWord_411397 prefixEnd_411397 93886400363480951575789 := by
  unfold tailWord_411397
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004881290586404858944445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10003254193724269905962963 15004881290586404858944445)
  ·
    refine ⟨5626830483969901822104167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15004881290586404858944445 5626830483969901822104167)
    ·
      refine ⟨8440245725954852733156251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5626830483969901822104167 8440245725954852733156251)
      ·
        refine ⟨12660368588932279099734377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8440245725954852733156251 12660368588932279099734377)
        ·
          refine ⟨9495276441699209324800783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12660368588932279099734377 9495276441699209324800783)
          ·
            refine ⟨14242914662548813987201175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9495276441699209324800783 14242914662548813987201175)
            ·
              refine ⟨21364371993823220980801763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14242914662548813987201175 21364371993823220980801763)
              ·
                refine ⟨32046557990734831471202645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21364371993823220980801763 32046557990734831471202645)
                ·
                  refine ⟨93886400363480951575789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 32046557990734831471202645 93886400363480951575789)
                  ·
                    rfl

theorem cell21_411397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_411397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411397 prefixEnd_411397 := by exact prefixLift 411397
  have htrace : WordTrace (prefixWord ++ tailWord_411397) baseStart_411397 baseEnd_411397 := by
    simpa [prefixWord, tailWord_411397, baseEnd_411397] using wordTrace_append hprefix tailTrace_411397
  have hstable : (prefixWord ++ tailWord_411397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411397).length < 2 ^ (prefixWord ++ tailWord_411397).sum := by decide
  have hdescent : baseEnd_411397 < baseStart_411397 := by decide
  rcases family_descends (prefixWord ++ tailWord_411397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411459 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 5]
def baseStart_411459 : Nat := 118140960795 + 411459 * 2 ^ 59
def prefixEnd_411459 : Nat := 4983230072969 + 3 ^ 40 * 411459 * 2
def baseEnd_411459 : Nat := 93900549608182621542329

theorem tailTrace_411459 : CollatzResearch.WordTrace tailWord_411459 prefixEnd_411459 93900549608182621542329 := by
  unfold tailWord_411459
  simp only [CollatzResearch.WordTrace]
  refine ⟨15007142616361789447701431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10004761744241192965134287 15007142616361789447701431)
  ·
    refine ⟨22510713924542684171552147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15007142616361789447701431 22510713924542684171552147)
    ·
      refine ⟨33766070886814026257328221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22510713924542684171552147 33766070886814026257328221)
      ·
        refine ⟨12662276582555259846498083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33766070886814026257328221 12662276582555259846498083)
        ·
          refine ⟨18993414873832889769747125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12662276582555259846498083 18993414873832889769747125)
          ·
            refine ⟨1780632644421833415913793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18993414873832889769747125 1780632644421833415913793)
            ·
              refine ⟨1335474483316375061935345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1780632644421833415913793 1335474483316375061935345)
              ·
                refine ⟨1001605862487281296451509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335474483316375061935345 1001605862487281296451509)
                ·
                  refine ⟨93900549608182621542329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1001605862487281296451509 93900549608182621542329)
                  ·
                    rfl

theorem cell21_411459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_411459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411459 prefixEnd_411459 := by exact prefixLift 411459
  have htrace : WordTrace (prefixWord ++ tailWord_411459) baseStart_411459 baseEnd_411459 := by
    simpa [prefixWord, tailWord_411459, baseEnd_411459] using wordTrace_append hprefix tailTrace_411459
  have hstable : (prefixWord ++ tailWord_411459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411459).length < 2 ^ (prefixWord ++ tailWord_411459).sum := by decide
  have hdescent : baseEnd_411459 < baseStart_411459 := by decide
  rcases family_descends (prefixWord ++ tailWord_411459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411544 : List Nat := [2, 1, 2, 6, 2, 1, 2, 2, 3]
def baseStart_411544 : Nat := 118140960795 + 411544 * 2 ^ 59
def prefixEnd_411544 : Nat := 4983230072969 + 3 ^ 40 * 411544 * 2
def baseEnd_411544 : Nat := 93919947766241362625489

theorem tailTrace_411544 : CollatzResearch.WordTrace tailWord_411544 prefixEnd_411544 93919947766241362625489 := by
  unfold tailWord_411544
  simp only [CollatzResearch.WordTrace]
  refine ⟨7505121410526924482272843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10006828547369232643030457 7505121410526924482272843)
  ·
    refine ⟨11257682115790386723409265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7505121410526924482272843 11257682115790386723409265)
    ·
      refine ⟨8443261586842790042556949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11257682115790386723409265 8443261586842790042556949)
      ·
        refine ⟨395777886883255783244857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8443261586842790042556949 395777886883255783244857)
        ·
          refine ⟨296833415162441837433643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395777886883255783244857 296833415162441837433643)
          ·
            refine ⟨445250122743662756150465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296833415162441837433643 445250122743662756150465)
            ·
              refine ⟨333937592057747067112849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445250122743662756150465 333937592057747067112849)
              ·
                refine ⟨250453194043310300334637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333937592057747067112849 250453194043310300334637)
                ·
                  refine ⟨93919947766241362625489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250453194043310300334637 93919947766241362625489)
                  ·
                    rfl

theorem cell21_411544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 3].length) (baseStart_411544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411544 prefixEnd_411544 := by exact prefixLift 411544
  have htrace : WordTrace (prefixWord ++ tailWord_411544) baseStart_411544 baseEnd_411544 := by
    simpa [prefixWord, tailWord_411544, baseEnd_411544] using wordTrace_append hprefix tailTrace_411544
  have hstable : (prefixWord ++ tailWord_411544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411544).length < 2 ^ (prefixWord ++ tailWord_411544).sum := by decide
  have hdescent : baseEnd_411544 < baseStart_411544 := by decide
  rcases family_descends (prefixWord ++ tailWord_411544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411676 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 4]
def baseStart_411676 : Nat := 118140960795 + 411676 * 2 ^ 59
def prefixEnd_411676 : Nat := 4983230072969 + 3 ^ 40 * 411676 * 2
def baseEnd_411676 : Nat := 93950071964638466425219

theorem tailTrace_411676 : CollatzResearch.WordTrace tailWord_411676 prefixEnd_411676 93950071964638466425219 := by
  unfold tailWord_411676
  simp only [CollatzResearch.WordTrace]
  refine ⟨7507528628287817754175441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10010038171050423672233921 7507528628287817754175441)
  ·
    refine ⟨5630646471215863315631581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7507528628287817754175441 5630646471215863315631581)
    ·
      refine ⟨2111492426705948743361843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5630646471215863315631581 2111492426705948743361843)
      ·
        refine ⟨3167238640058923115042765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2111492426705948743361843 3167238640058923115042765)
        ·
          refine ⟨1187714490022096168141037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3167238640058923115042765 1187714490022096168141037)
          ·
            refine ⟨445392933758286063052889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1187714490022096168141037 445392933758286063052889)
            ·
              refine ⟨334044700318714547289667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445392933758286063052889 334044700318714547289667)
              ·
                refine ⟨501067050478071820934501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334044700318714547289667 501067050478071820934501)
                ·
                  refine ⟨93950071964638466425219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 501067050478071820934501 93950071964638466425219)
                  ·
                    rfl

theorem cell21_411676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_411676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411676 prefixEnd_411676 := by exact prefixLift 411676
  have htrace : WordTrace (prefixWord ++ tailWord_411676) baseStart_411676 baseEnd_411676 := by
    simpa [prefixWord, tailWord_411676, baseEnd_411676] using wordTrace_append hprefix tailTrace_411676
  have hstable : (prefixWord ++ tailWord_411676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411676).length < 2 ^ (prefixWord ++ tailWord_411676).sum := by decide
  have hdescent : baseEnd_411676 < baseStart_411676 := by decide
  rcases family_descends (prefixWord ++ tailWord_411676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411701 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 8]
def baseStart_411701 : Nat := 118140960795 + 411701 * 2 ^ 59
def prefixEnd_411701 : Nat := 4983230072969 + 3 ^ 40 * 411701 * 2
def baseEnd_411701 : Nat := 93955777305243978508501

theorem tailTrace_411701 : CollatzResearch.WordTrace tailWord_411701 prefixEnd_411701 93955777305243978508501 := by
  unfold tailWord_411701
  simp only [CollatzResearch.WordTrace]
  refine ⟨15015969081485064778010957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10010646054323376518673971 15015969081485064778010957)
  ·
    refine ⟨5630988405556899291754109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15015969081485064778010957 5630988405556899291754109)
    ·
      refine ⟨2111620652083837234407791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5630988405556899291754109 2111620652083837234407791)
      ·
        refine ⟨3167430978125755851611687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2111620652083837234407791 3167430978125755851611687)
        ·
          refine ⟨4751146467188633777417531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167430978125755851611687 4751146467188633777417531)
          ·
            refine ⟨7126719700782950666126297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4751146467188633777417531 7126719700782950666126297)
            ·
              refine ⟨5345039775587212999594723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7126719700782950666126297 5345039775587212999594723)
              ·
                refine ⟨8017559663380819499392085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5345039775587212999594723 8017559663380819499392085)
                ·
                  refine ⟨93955777305243978508501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8017559663380819499392085 93955777305243978508501)
                  ·
                    rfl

theorem cell21_411701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_411701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411701 prefixEnd_411701 := by exact prefixLift 411701
  have htrace : WordTrace (prefixWord ++ tailWord_411701) baseStart_411701 baseEnd_411701 := by
    simpa [prefixWord, tailWord_411701, baseEnd_411701] using wordTrace_append hprefix tailTrace_411701
  have hstable : (prefixWord ++ tailWord_411701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411701).length < 2 ^ (prefixWord ++ tailWord_411701).sum := by decide
  have hdescent : baseEnd_411701 < baseStart_411701 := by decide
  rcases family_descends (prefixWord ++ tailWord_411701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411749 : List Nat := [1, 3, 1, 3, 2, 3, 3, 5]
def baseStart_411749 : Nat := 118140960795 + 411749 * 2 ^ 59
def prefixEnd_411749 : Nat := 4983230072969 + 3 ^ 40 * 411749 * 2
def baseEnd_411749 : Nat := 31322243853068853902801

theorem tailTrace_411749 : CollatzResearch.WordTrace tailWord_411749 prefixEnd_411749 31322243853068853902801 := by
  unfold tailWord_411749
  simp only [CollatzResearch.WordTrace]
  refine ⟨15017719785311168975758301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10011813190207445983838867 15017719785311168975758301)
  ·
    refine ⟨5631644919491688365909363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15017719785311168975758301 5631644919491688365909363)
    ·
      refine ⟨8447467379237532548864045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5631644919491688365909363 8447467379237532548864045)
      ·
        refine ⟨3167800267214074705824017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8447467379237532548864045 3167800267214074705824017)
        ·
          refine ⟨2375850200410556029368013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3167800267214074705824017 2375850200410556029368013)
          ·
            refine ⟨890943825153958511013005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2375850200410556029368013 890943825153958511013005)
            ·
              refine ⟨334103934432734441629877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 890943825153958511013005 334103934432734441629877)
              ·
                refine ⟨31322243853068853902801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 334103934432734441629877 31322243853068853902801)
                ·
                  rfl

theorem cell21_411749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 5].length) (baseStart_411749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411749 prefixEnd_411749 := by exact prefixLift 411749
  have htrace : WordTrace (prefixWord ++ tailWord_411749) baseStart_411749 baseEnd_411749 := by
    simpa [prefixWord, tailWord_411749, baseEnd_411749] using wordTrace_append hprefix tailTrace_411749
  have hstable : (prefixWord ++ tailWord_411749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411749).length < 2 ^ (prefixWord ++ tailWord_411749).sum := by decide
  have hdescent : baseEnd_411749 < baseStart_411749 := by decide
  rcases family_descends (prefixWord ++ tailWord_411749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411780 : List Nat := [2, 3, 2, 1, 2, 1, 1, 6, 3]
def baseStart_411780 : Nat := 118140960795 + 411780 * 2 ^ 59
def prefixEnd_411780 : Nat := 4983230072969 + 3 ^ 40 * 411780 * 2
def baseEnd_411780 : Nat := 93973806181557396691673

theorem tailTrace_411780 : CollatzResearch.WordTrace tailWord_411780 prefixEnd_411780 93973806181557396691673 := by
  unfold tailWord_411780
  simp only [CollatzResearch.WordTrace]
  refine ⟨7509425224099430635068397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10012566965465907513424529 7509425224099430635068397)
  ·
    refine ⟨2816034459037286488150649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7509425224099430635068397 2816034459037286488150649)
    ·
      refine ⟨2112025844277964866112987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2816034459037286488150649 2112025844277964866112987)
      ·
        refine ⟨3168038766416947299169481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112025844277964866112987 3168038766416947299169481)
        ·
          refine ⟨2376029074812710474377111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3168038766416947299169481 2376029074812710474377111)
          ·
            refine ⟨3564043612219065711565667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2376029074812710474377111 3564043612219065711565667)
            ·
              refine ⟨5346065418328598567348501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564043612219065711565667 5346065418328598567348501)
              ·
                refine ⟨250596816484153057844461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5346065418328598567348501 250596816484153057844461)
                ·
                  refine ⟨93973806181557396691673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250596816484153057844461 93973806181557396691673)
                  ·
                    rfl

theorem cell21_411780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_411780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411780 prefixEnd_411780 := by exact prefixLift 411780
  have htrace : WordTrace (prefixWord ++ tailWord_411780) baseStart_411780 baseEnd_411780 := by
    simpa [prefixWord, tailWord_411780, baseEnd_411780] using wordTrace_append hprefix tailTrace_411780
  have hstable : (prefixWord ++ tailWord_411780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411780).length < 2 ^ (prefixWord ++ tailWord_411780).sum := by decide
  have hdescent : baseEnd_411780 < baseStart_411780 := by decide
  rcases family_descends (prefixWord ++ tailWord_411780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411808 : List Nat := [2, 1, 1, 4, 2, 3, 1, 7]
def baseStart_411808 : Nat := 118140960795 + 411808 * 2 ^ 59
def prefixEnd_411808 : Nat := 4983230072969 + 3 ^ 40 * 411808 * 2
def baseEnd_411808 : Nat := 31326732054345190074983

theorem tailTrace_411808 : CollatzResearch.WordTrace tailWord_411808 prefixEnd_411808 31326732054345190074983 := by
  unfold tailWord_411808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7509935846048711026078039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10013247794731614701437385 7509935846048711026078039)
  ·
    refine ⟨11264903769073066539117059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7509935846048711026078039 11264903769073066539117059)
    ·
      refine ⟨16897355653609599808675589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11264903769073066539117059 16897355653609599808675589)
      ·
        refine ⟨3168254185051799964126673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16897355653609599808675589 3168254185051799964126673)
        ·
          refine ⟨2376190638788849973095005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3168254185051799964126673 2376190638788849973095005)
          ·
            refine ⟨891071489545818739910627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2376190638788849973095005 891071489545818739910627)
            ·
              refine ⟨1336607234318728109865941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891071489545818739910627 1336607234318728109865941)
              ·
                refine ⟨31326732054345190074983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1336607234318728109865941 31326732054345190074983)
                ·
                  rfl

theorem cell21_411808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_411808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411808 prefixEnd_411808 := by exact prefixLift 411808
  have htrace : WordTrace (prefixWord ++ tailWord_411808) baseStart_411808 baseEnd_411808 := by
    simpa [prefixWord, tailWord_411808, baseEnd_411808] using wordTrace_append hprefix tailTrace_411808
  have hstable : (prefixWord ++ tailWord_411808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411808).length < 2 ^ (prefixWord ++ tailWord_411808).sum := by decide
  have hdescent : baseEnd_411808 < baseStart_411808 := by decide
  rcases family_descends (prefixWord ++ tailWord_411808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411825 : List Nat := [1, 2, 2, 5, 2, 2, 7]
def baseStart_411825 : Nat := 118140960795 + 411825 * 2 ^ 59
def prefixEnd_411825 : Nat := 4983230072969 + 3 ^ 40 * 411825 * 2
def baseEnd_411825 : Nat := 10442675088294146493509

theorem tailTrace_411825 : CollatzResearch.WordTrace tailWord_411825 prefixEnd_411825 10442675088294146493509 := by
  unfold tailWord_411825
  simp only [CollatzResearch.WordTrace]
  refine ⟨15020491733035833955524929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10013661155357222637016619 15020491733035833955524929)
  ·
    refine ⟨11265368799776875466643697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15020491733035833955524929 11265368799776875466643697)
    ·
      refine ⟨8449026599832656599982773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11265368799776875466643697 8449026599832656599982773)
      ·
        refine ⟨792096243734311556248385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8449026599832656599982773 792096243734311556248385)
        ·
          refine ⟨594072182800733667186289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792096243734311556248385 594072182800733667186289)
          ·
            refine ⟨445554137100550250389717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594072182800733667186289 445554137100550250389717)
            ·
              refine ⟨10442675088294146493509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 445554137100550250389717 10442675088294146493509)
              ·
                rfl

theorem cell21_411825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 7].length) (baseStart_411825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411825 prefixEnd_411825 := by exact prefixLift 411825
  have htrace : WordTrace (prefixWord ++ tailWord_411825) baseStart_411825 baseEnd_411825 := by
    simpa [prefixWord, tailWord_411825, baseEnd_411825] using wordTrace_append hprefix tailTrace_411825
  have hstable : (prefixWord ++ tailWord_411825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411825).length < 2 ^ (prefixWord ++ tailWord_411825).sum := by decide
  have hdescent : baseEnd_411825 < baseStart_411825 := by decide
  rcases family_descends (prefixWord ++ tailWord_411825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411842 : List Nat := [3, 5, 1, 1, 1, 1, 1, 8]
def baseStart_411842 : Nat := 118140960795 + 411842 * 2 ^ 59
def prefixEnd_411842 : Nat := 4983230072969 + 3 ^ 40 * 411842 * 2
def baseEnd_411842 : Nat := 31329318475419688886071

theorem tailTrace_411842 : CollatzResearch.WordTrace tailWord_411842 prefixEnd_411842 31329318475419688886071 := by
  unfold tailWord_411842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755277943493561464723445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10014074515982830572595853 3755277943493561464723445)
  ·
    refine ⟨352057307202521387317823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3755277943493561464723445 352057307202521387317823)
    ·
      refine ⟨528085960803782080976735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352057307202521387317823 528085960803782080976735)
      ·
        refine ⟨792128941205673121465103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528085960803782080976735 792128941205673121465103)
        ·
          refine ⟨1188193411808509682197655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792128941205673121465103 1188193411808509682197655)
          ·
            refine ⟨1782290117712764523296483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188193411808509682197655 1782290117712764523296483)
            ·
              refine ⟨2673435176569146784944725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782290117712764523296483 2673435176569146784944725)
              ·
                refine ⟨31329318475419688886071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2673435176569146784944725 31329318475419688886071)
                ·
                  rfl

theorem cell21_411842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_411842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411842 prefixEnd_411842 := by exact prefixLift 411842
  have htrace : WordTrace (prefixWord ++ tailWord_411842) baseStart_411842 baseEnd_411842 := by
    simpa [prefixWord, tailWord_411842, baseEnd_411842] using wordTrace_append hprefix tailTrace_411842
  have hstable : (prefixWord ++ tailWord_411842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411842).length < 2 ^ (prefixWord ++ tailWord_411842).sum := by decide
  have hdescent : baseEnd_411842 < baseStart_411842 := by decide
  rcases family_descends (prefixWord ++ tailWord_411842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411890 : List Nat := [3, 2, 1, 3, 2, 3, 2, 2, 3]
def baseStart_411890 : Nat := 118140960795 + 411890 * 2 ^ 59
def prefixEnd_411890 : Nat := 4983230072969 + 3 ^ 40 * 411890 * 2
def baseEnd_411890 : Nat := 93998909680221649858115

theorem tailTrace_411890 : CollatzResearch.WordTrace tailWord_411890 prefixEnd_411890 93998909680221649858115 := by
  unfold tailWord_411890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755715619450087514160281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10015241651866900037760749 3755715619450087514160281)
  ·
    refine ⟨2816786714587565635620211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3755715619450087514160281 2816786714587565635620211)
    ·
      refine ⟨4225180071881348453430317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816786714587565635620211 4225180071881348453430317)
      ·
        refine ⟨1584442526955505670036369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4225180071881348453430317 1584442526955505670036369)
        ·
          refine ⟨1188331895216629252527277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1584442526955505670036369 1188331895216629252527277)
          ·
            refine ⟨445624460706235969697729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1188331895216629252527277 445624460706235969697729)
            ·
              refine ⟨334218345529676977273297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445624460706235969697729 334218345529676977273297)
              ·
                refine ⟨250663759147257732954973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334218345529676977273297 250663759147257732954973)
                ·
                  refine ⟨93998909680221649858115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250663759147257732954973 93998909680221649858115)
                  ·
                    rfl

theorem cell21_411890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_411890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411890 prefixEnd_411890 := by exact prefixLift 411890
  have htrace : WordTrace (prefixWord ++ tailWord_411890) baseStart_411890 baseEnd_411890 := by
    simpa [prefixWord, tailWord_411890, baseEnd_411890] using wordTrace_append hprefix tailTrace_411890
  have hstable : (prefixWord ++ tailWord_411890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411890).length < 2 ^ (prefixWord ++ tailWord_411890).sum := by decide
  have hdescent : baseEnd_411890 < baseStart_411890 := by decide
  rcases family_descends (prefixWord ++ tailWord_411890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411949 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 5]
def baseStart_411949 : Nat := 118140960795 + 411949 * 2 ^ 59
def prefixEnd_411949 : Nat := 4983230072969 + 3 ^ 40 * 411949 * 2
def baseEnd_411949 : Nat := 94012374284050658374661

theorem tailTrace_411949 : CollatzResearch.WordTrace tailWord_411949 prefixEnd_411949 94012374284050658374661 := by
  unfold tailWord_411949
  simp only [CollatzResearch.WordTrace]
  refine ⟨15025014384586603133038901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10016676256391068755359267 15025014384586603133038901)
  ·
    refine ⟨1408595098554994043722397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15025014384586603133038901 1408595098554994043722397)
    ·
      refine ⟨528223161958122766395899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1408595098554994043722397 528223161958122766395899)
      ·
        refine ⟨792334742937184149593849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528223161958122766395899 792334742937184149593849)
        ·
          refine ⟨594251057202888112195387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792334742937184149593849 594251057202888112195387)
          ·
            refine ⟨891376585804332168293081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594251057202888112195387 891376585804332168293081)
            ·
              refine ⟨668532439353249126219811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891376585804332168293081 668532439353249126219811)
              ·
                refine ⟨1002798659029873689329717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668532439353249126219811 1002798659029873689329717)
                ·
                  refine ⟨94012374284050658374661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1002798659029873689329717 94012374284050658374661)
                  ·
                    rfl

theorem cell21_411949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_411949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_411949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_411949 prefixEnd_411949 := by exact prefixLift 411949
  have htrace : WordTrace (prefixWord ++ tailWord_411949) baseStart_411949 baseEnd_411949 := by
    simpa [prefixWord, tailWord_411949, baseEnd_411949] using wordTrace_append hprefix tailTrace_411949
  have hstable : (prefixWord ++ tailWord_411949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411949).length < 2 ^ (prefixWord ++ tailWord_411949).sum := by decide
  have hdescent : baseEnd_411949 < baseStart_411949 := by decide
  rcases family_descends (prefixWord ++ tailWord_411949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412005 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 6]
def baseStart_412005 : Nat := 118140960795 + 412005 * 2 ^ 59
def prefixEnd_412005 : Nat := 4983230072969 + 3 ^ 40 * 412005 * 2
def baseEnd_412005 : Nat := 94025154247007005441213

theorem tailTrace_412005 : CollatzResearch.WordTrace tailWord_412005 prefixEnd_412005 94025154247007005441213 := by
  unfold tailWord_412005
  simp only [CollatzResearch.WordTrace]
  refine ⟨15027056872383724697077469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10018037914922483131384979 15027056872383724697077469)
  ·
    refine ⟨5635146327143896761404051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15027056872383724697077469 5635146327143896761404051)
    ·
      refine ⟨8452719490715845142106077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5635146327143896761404051 8452719490715845142106077)
      ·
        refine ⟨3169769809018441928289779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8452719490715845142106077 3169769809018441928289779)
        ·
          refine ⟨4754654713527662892434669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3169769809018441928289779 4754654713527662892434669)
          ·
            refine ⟨1782995517572873584663001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4754654713527662892434669 1782995517572873584663001)
            ·
              refine ⟨1337246638179655188497251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1782995517572873584663001 1337246638179655188497251)
              ·
                refine ⟨2005869957269482782745877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337246638179655188497251 2005869957269482782745877)
                ·
                  refine ⟨94025154247007005441213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2005869957269482782745877 94025154247007005441213)
                  ·
                    rfl

theorem cell21_412005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_412005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412005 prefixEnd_412005 := by exact prefixLift 412005
  have htrace : WordTrace (prefixWord ++ tailWord_412005) baseStart_412005 baseEnd_412005 := by
    simpa [prefixWord, tailWord_412005, baseEnd_412005] using wordTrace_append hprefix tailTrace_412005
  have hstable : (prefixWord ++ tailWord_412005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412005).length < 2 ^ (prefixWord ++ tailWord_412005).sum := by decide
  have hdescent : baseEnd_412005 < baseStart_412005 := by decide
  rcases family_descends (prefixWord ++ tailWord_412005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412008 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 5]
def baseStart_412008 : Nat := 118140960795 + 412008 * 2 ^ 59
def prefixEnd_412008 : Nat := 4983230072969 + 3 ^ 40 * 412008 * 2
def baseEnd_412008 : Nat := 94025838887879666891207

theorem tailTrace_412008 : CollatzResearch.WordTrace tailWord_412008 prefixEnd_412008 94025838887879666891207 := by
  unfold tailWord_412008
  simp only [CollatzResearch.WordTrace]
  refine ⟨7513583145686428104718339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10018110860915237472957785 7513583145686428104718339)
  ·
    refine ⟨11270374718529642157077509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7513583145686428104718339 11270374718529642157077509)
    ·
      refine ⟨2113195259724307904452033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11270374718529642157077509 2113195259724307904452033)
      ·
        refine ⟨1584896444793230928339025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2113195259724307904452033 1584896444793230928339025)
        ·
          refine ⟨1188672333594923196254269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1584896444793230928339025 1188672333594923196254269)
          ·
            refine ⟨445752125098096198595351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1188672333594923196254269 445752125098096198595351)
            ·
              refine ⟨668628187647144297893027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445752125098096198595351 668628187647144297893027)
              ·
                refine ⟨1002942281470716446839541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668628187647144297893027 1002942281470716446839541)
                ·
                  refine ⟨94025838887879666891207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1002942281470716446839541 94025838887879666891207)
                  ·
                    rfl

theorem cell21_412008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_412008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412008 prefixEnd_412008 := by exact prefixLift 412008
  have htrace : WordTrace (prefixWord ++ tailWord_412008) baseStart_412008 baseEnd_412008 := by
    simpa [prefixWord, tailWord_412008, baseEnd_412008] using wordTrace_append hprefix tailTrace_412008
  have hstable : (prefixWord ++ tailWord_412008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412008).length < 2 ^ (prefixWord ++ tailWord_412008).sum := by decide
  have hdescent : baseEnd_412008 < baseStart_412008 := by decide
  rcases family_descends (prefixWord ++ tailWord_412008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412146 : List Nat := [3, 2, 1, 4, 2, 2, 2, 5]
def baseStart_412146 : Nat := 118140960795 + 412146 * 2 ^ 59
def prefixEnd_412146 : Nat := 4983230072969 + 3 ^ 40 * 412146 * 2
def baseEnd_412146 : Nat := 31352444122674031196975

theorem tailTrace_412146 : CollatzResearch.WordTrace tailWord_412146 prefixEnd_412146 31352444122674031196975 := by
  unfold tailWord_412146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3758049891218226444490073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10021466376581937185306861 3758049891218226444490073)
  ·
    refine ⟨2818537418413669833367555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3758049891218226444490073 2818537418413669833367555)
    ·
      refine ⟨4227806127620504750051333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2818537418413669833367555 4227806127620504750051333)
      ·
        refine ⟨792713648928844640634625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4227806127620504750051333 792713648928844640634625)
        ·
          refine ⟨594535236696633480475969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792713648928844640634625 594535236696633480475969)
          ·
            refine ⟨445901427522475110356977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594535236696633480475969 445901427522475110356977)
            ·
              refine ⟨334426070641856332767733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445901427522475110356977 334426070641856332767733)
              ·
                refine ⟨31352444122674031196975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 334426070641856332767733 31352444122674031196975)
                ·
                  rfl

theorem cell21_412146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_412146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412146 prefixEnd_412146 := by exact prefixLift 412146
  have htrace : WordTrace (prefixWord ++ tailWord_412146) baseStart_412146 baseEnd_412146 := by
    simpa [prefixWord, tailWord_412146, baseEnd_412146] using wordTrace_append hprefix tailTrace_412146
  have hstable : (prefixWord ++ tailWord_412146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412146).length < 2 ^ (prefixWord ++ tailWord_412146).sum := by decide
  have hdescent : baseEnd_412146 < baseStart_412146 := by decide
  rcases family_descends (prefixWord ++ tailWord_412146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412171 : List Nat := [1, 1, 1, 1, 7, 1, 9]
def baseStart_412171 : Nat := 118140960795 + 412171 * 2 ^ 59
def prefixEnd_412171 : Nat := 4983230072969 + 3 ^ 40 * 412171 * 2
def baseEnd_412171 : Nat := 10451448634291956186023

theorem tailTrace_412171 : CollatzResearch.WordTrace tailWord_412171 prefixEnd_412171 10451448634291956186023 := by
  unfold tailWord_412171
  simp only [CollatzResearch.WordTrace]
  refine ⟨15033111389782335047620367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10022074259854890031746911 15033111389782335047620367)
  ·
    refine ⟨22549667084673502571430551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15033111389782335047620367 22549667084673502571430551)
    ·
      refine ⟨33824500627010253857145827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22549667084673502571430551 33824500627010253857145827)
      ·
        refine ⟨50736750940515380785718741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33824500627010253857145827 50736750940515380785718741)
        ·
          refine ⟨1189142600168329237165283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50736750940515380785718741 1189142600168329237165283)
          ·
            refine ⟨1783713900252493855747925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189142600168329237165283 1783713900252493855747925)
            ·
              refine ⟨10451448634291956186023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1783713900252493855747925 10451448634291956186023)
              ·
                rfl

theorem cell21_412171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 9].length) (baseStart_412171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412171 prefixEnd_412171 := by exact prefixLift 412171
  have htrace : WordTrace (prefixWord ++ tailWord_412171) baseStart_412171 baseEnd_412171 := by
    simpa [prefixWord, tailWord_412171, baseEnd_412171] using wordTrace_append hprefix tailTrace_412171
  have hstable : (prefixWord ++ tailWord_412171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412171).length < 2 ^ (prefixWord ++ tailWord_412171).sum := by decide
  have hdescent : baseEnd_412171 < baseStart_412171 := by decide
  rcases family_descends (prefixWord ++ tailWord_412171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412188 : List Nat := [2, 2, 3, 1, 2, 3, 2, 6]
def baseStart_412188 : Nat := 118140960795 + 412188 * 2 ^ 59
def prefixEnd_412188 : Nat := 4983230072969 + 3 ^ 40 * 412188 * 2
def baseEnd_412188 : Nat := 31355639113413117963613

theorem tailTrace_412188 : CollatzResearch.WordTrace tailWord_412188 prefixEnd_412188 31355639113413117963613 := by
  unfold tailWord_412188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7516865715360373475494609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10022487620480497967326145 7516865715360373475494609)
  ·
    refine ⟨5637649286520280106620957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7516865715360373475494609 5637649286520280106620957)
    ·
      refine ⟨2114118482445105039982859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5637649286520280106620957 2114118482445105039982859)
      ·
        refine ⟨3171177723667657559974289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114118482445105039982859 3171177723667657559974289)
        ·
          refine ⟨2378383292750743169980717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3171177723667657559974289 2378383292750743169980717)
          ·
            refine ⟨891893734781528688742769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2378383292750743169980717 891893734781528688742769)
            ·
              refine ⟨668920301086146516557077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891893734781528688742769 668920301086146516557077)
              ·
                refine ⟨31355639113413117963613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 668920301086146516557077 31355639113413117963613)
                ·
                  rfl

theorem cell21_412188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_412188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412188 prefixEnd_412188 := by exact prefixLift 412188
  have htrace : WordTrace (prefixWord ++ tailWord_412188) baseStart_412188 baseEnd_412188 := by
    simpa [prefixWord, tailWord_412188, baseEnd_412188] using wordTrace_append hprefix tailTrace_412188
  have hstable : (prefixWord ++ tailWord_412188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412188).length < 2 ^ (prefixWord ++ tailWord_412188).sum := by decide
  have hdescent : baseEnd_412188 < baseStart_412188 := by decide
  rcases family_descends (prefixWord ++ tailWord_412188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412228 : List Nat := [2, 3, 5, 1, 1, 2, 2, 2, 3]
def baseStart_412228 : Nat := 118140960795 + 412228 * 2 ^ 59
def prefixEnd_412228 : Nat := 4983230072969 + 3 ^ 40 * 412228 * 2
def baseEnd_412228 : Nat := 94076045885208173224091

theorem tailTrace_412228 : CollatzResearch.WordTrace tailWord_412228 prefixEnd_412228 94076045885208173224091 := by
  unfold tailWord_412228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7517595175287916891222669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10023460233717222521630225 7517595175287916891222669)
  ·
    refine ⟨2819098190732968834208501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7517595175287916891222669 2819098190732968834208501)
    ·
      refine ⟨264290455381215828207047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2819098190732968834208501 264290455381215828207047)
      ·
        refine ⟨396435683071823742310571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264290455381215828207047 396435683071823742310571)
        ·
          refine ⟨594653524607735613465857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396435683071823742310571 594653524607735613465857)
          ·
            refine ⟨445990143455801710099393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594653524607735613465857 445990143455801710099393)
            ·
              refine ⟨334492607591851282574545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445990143455801710099393 334492607591851282574545)
              ·
                refine ⟨250869455693888461930909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334492607591851282574545 250869455693888461930909)
                ·
                  refine ⟨94076045885208173224091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250869455693888461930909 94076045885208173224091)
                  ·
                    rfl

theorem cell21_412228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_412228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412228 prefixEnd_412228 := by exact prefixLift 412228
  have htrace : WordTrace (prefixWord ++ tailWord_412228) baseStart_412228 baseEnd_412228 := by
    simpa [prefixWord, tailWord_412228, baseEnd_412228] using wordTrace_append hprefix tailTrace_412228
  have hstable : (prefixWord ++ tailWord_412228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412228).length < 2 ^ (prefixWord ++ tailWord_412228).sum := by decide
  have hdescent : baseEnd_412228 < baseStart_412228 := by decide
  rcases family_descends (prefixWord ++ tailWord_412228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412295 : List Nat := [1, 1, 4, 2, 1, 2, 1, 6, 3]
def baseStart_412295 : Nat := 118140960795 + 412295 * 2 ^ 59
def prefixEnd_412295 : Nat := 4983230072969 + 3 ^ 40 * 412295 * 2
def baseEnd_412295 : Nat := 94091336198030945607287

theorem tailTrace_412295 : CollatzResearch.WordTrace tailWord_412295 prefixEnd_412295 94091336198030945607287 := by
  unfold tailWord_412295
  simp only [CollatzResearch.WordTrace]
  refine ⟨15037634041333104225134339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10025089360888736150089559 15037634041333104225134339)
  ·
    refine ⟨22556451061999656337701509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15037634041333104225134339 22556451061999656337701509)
    ·
      refine ⟨4229334574124935563319033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22556451061999656337701509 4229334574124935563319033)
      ·
        refine ⟨3172000930593701672489275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4229334574124935563319033 3172000930593701672489275)
        ·
          refine ⟨4758001395890552508733913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3172000930593701672489275 4758001395890552508733913)
          ·
            refine ⟨3568501046917914381550435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4758001395890552508733913 3568501046917914381550435)
            ·
              refine ⟨5352751570376871572325653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3568501046917914381550435 5352751570376871572325653)
              ·
                refine ⟨250910229861415854952765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5352751570376871572325653 250910229861415854952765)
                ·
                  refine ⟨94091336198030945607287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250910229861415854952765 94091336198030945607287)
                  ·
                    rfl

theorem cell21_412295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 3].length) (baseStart_412295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412295 prefixEnd_412295 := by exact prefixLift 412295
  have htrace : WordTrace (prefixWord ++ tailWord_412295) baseStart_412295 baseEnd_412295 := by
    simpa [prefixWord, tailWord_412295, baseEnd_412295] using wordTrace_append hprefix tailTrace_412295
  have hstable : (prefixWord ++ tailWord_412295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412295).length < 2 ^ (prefixWord ++ tailWord_412295).sum := by decide
  have hdescent : baseEnd_412295 < baseStart_412295 := by decide
  rcases family_descends (prefixWord ++ tailWord_412295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412402 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_412402 : Nat := 118140960795 + 412402 * 2 ^ 59
def prefixEnd_412402 : Nat := 4983230072969 + 3 ^ 40 * 412402 * 2
def baseEnd_412402 : Nat := 94115755055822537323735

theorem tailTrace_412402 : CollatzResearch.WordTrace tailWord_412402 prefixEnd_412402 94115755055822537323735 := by
  unfold tailWord_412402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760384162986365374819865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10027691101296974332852973 3760384162986365374819865)
  ·
    refine ⟨2820288122239774031114899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3760384162986365374819865 2820288122239774031114899)
    ·
      refine ⟨4230432183359661046672349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2820288122239774031114899 4230432183359661046672349)
      ·
        refine ⟨1586412068759872892502131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4230432183359661046672349 1586412068759872892502131)
        ·
          refine ⟨2379618103139809338753197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586412068759872892502131 2379618103139809338753197)
          ·
            refine ⟨892356788677428502032449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2379618103139809338753197 892356788677428502032449)
            ·
              refine ⟨669267591508071376524337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892356788677428502032449 669267591508071376524337)
              ·
                refine ⟨501950693631053532393253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669267591508071376524337 501950693631053532393253)
                ·
                  refine ⟨94115755055822537323735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 501950693631053532393253 94115755055822537323735)
                  ·
                    rfl

theorem cell21_412402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_412402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_412402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_412402 prefixEnd_412402 := by exact prefixLift 412402
  have htrace : WordTrace (prefixWord ++ tailWord_412402) baseStart_412402 baseEnd_412402 := by
    simpa [prefixWord, tailWord_412402, baseEnd_412402] using wordTrace_append hprefix tailTrace_412402
  have hstable : (prefixWord ++ tailWord_412402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412402).length < 2 ^ (prefixWord ++ tailWord_412402).sum := by decide
  have hdescent : baseEnd_412402 < baseStart_412402 := by decide
  rcases family_descends (prefixWord ++ tailWord_412402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
