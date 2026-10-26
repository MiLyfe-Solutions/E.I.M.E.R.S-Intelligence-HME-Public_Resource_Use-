import V185TrunkScan22Chunk357

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3193874 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3193874 : Nat := 118140960795 + 3193874 * 2 ^ 59
def prefixEnd_3193874 : Nat := 4983230072969 + 3 ^ 40 * 3193874 * 2
def baseEnd_3193874 : Nat := 1093328341265428124657765

theorem tailTrace_3193874 : CollatzResearch.WordTrace tailWord_3193874 prefixEnd_3193874 1093328341265428124657765 := by
  unfold tailWord_3193874
  simp only [CollatzResearch.WordTrace]
  refine ⟨29122538707786860774301169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77660103220764962064803117 29122538707786860774301169)
  ·
    refine ⟨21841904030840145580725877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29122538707786860774301169 21841904030840145580725877)
    ·
      refine ⟨2047678502891263648193051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21841904030840145580725877 2047678502891263648193051)
      ·
        refine ⟨3071517754336895472289577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2047678502891263648193051 3071517754336895472289577)
        ·
          refine ⟨2303638315752671604217183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3071517754336895472289577 2303638315752671604217183)
          ·
            refine ⟨3455457473629007406325775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303638315752671604217183 3455457473629007406325775)
            ·
              refine ⟨5183186210443511109488663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455457473629007406325775 5183186210443511109488663)
              ·
                refine ⟨7774779315665266664232995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183186210443511109488663 7774779315665266664232995)
                ·
                  refine ⟨11662168973497899996349493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7774779315665266664232995 11662168973497899996349493)
                  ·
                    refine ⟨1093328341265428124657765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11662168973497899996349493 1093328341265428124657765)
                    ·
                      rfl

theorem cell22_3193874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3193874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193874 prefixEnd_3193874 := by exact prefixLift 3193874
  have htrace : WordTrace (prefixWord ++ tailWord_3193874) baseStart_3193874 baseEnd_3193874 := by
    simpa [prefixWord, tailWord_3193874, baseEnd_3193874] using wordTrace_append hprefix tailTrace_3193874
  have hstable : (prefixWord ++ tailWord_3193874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193874).length < 2 ^ (prefixWord ++ tailWord_3193874).sum := by decide
  have hdescent : baseEnd_3193874 < baseStart_3193874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193941 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_3193941 : Nat := 118140960795 + 3193941 * 2 ^ 59
def prefixEnd_3193941 : Nat := 4983230072969 + 3 ^ 40 * 3193941 * 2
def baseEnd_3193941 : Nat := 1093351276734662283232559

theorem tailTrace_3193941 : CollatzResearch.WordTrace tailWord_3193941 prefixEnd_3193941 1093351276734662283232559 := by
  unfold tailWord_3193941
  simp only [CollatzResearch.WordTrace]
  refine ⟨116492598521904713539893677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77661732347936475693262451 116492598521904713539893677)
  ·
    refine ⟨43684724445714267577460129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116492598521904713539893677 43684724445714267577460129)
    ·
      refine ⟨32763543334285700683095097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43684724445714267577460129 32763543334285700683095097)
      ·
        refine ⟨24572657500714275512321323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32763543334285700683095097 24572657500714275512321323)
        ·
          refine ⟨36858986251071413268481985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24572657500714275512321323 36858986251071413268481985)
          ·
            refine ⟨27644239688303559951361489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36858986251071413268481985 27644239688303559951361489)
            ·
              refine ⟨20733179766227669963521117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27644239688303559951361489 20733179766227669963521117)
              ·
                refine ⟨7774942412335376236320419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20733179766227669963521117 7774942412335376236320419)
                ·
                  refine ⟨11662413618503064354480629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7774942412335376236320419 11662413618503064354480629)
                  ·
                    refine ⟨1093351276734662283232559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11662413618503064354480629 1093351276734662283232559)
                    ·
                      rfl

theorem cell22_3193941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_3193941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193941 prefixEnd_3193941 := by exact prefixLift 3193941
  have htrace : WordTrace (prefixWord ++ tailWord_3193941) baseStart_3193941 baseEnd_3193941 := by
    simpa [prefixWord, tailWord_3193941, baseEnd_3193941] using wordTrace_append hprefix tailTrace_3193941
  have hstable : (prefixWord ++ tailWord_3193941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193941).length < 2 ^ (prefixWord ++ tailWord_3193941).sum := by decide
  have hdescent : baseEnd_3193941 < baseStart_3193941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193977 : List Nat := [1, 2, 1, 3, 5, 2, 2, 2, 4]
def baseStart_3193977 : Nat := 118140960795 + 3193977 * 2 ^ 59
def prefixEnd_3193977 : Nat := 4983230072969 + 3 ^ 40 * 3193977 * 2
def baseEnd_3193977 : Nat := 364454533423456729777483

theorem tailTrace_3193977 : CollatzResearch.WordTrace tailWord_3193977 prefixEnd_3193977 364454533423456729777483 := by
  unfold tailWord_3193977
  simp only [CollatzResearch.WordTrace]
  refine ⟨116493911549774291688204185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77662607699849527792136123 116493911549774291688204185)
  ·
    refine ⟨87370433662330718766153139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116493911549774291688204185 87370433662330718766153139)
    ·
      refine ⟨131055650493496078149229709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87370433662330718766153139 131055650493496078149229709)
      ·
        refine ⟨49145868935061029305961141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131055650493496078149229709 49145868935061029305961141)
        ·
          refine ⟨4607425212661971497433857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49145868935061029305961141 4607425212661971497433857)
          ·
            refine ⟨3455568909496478623075393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4607425212661971497433857 3455568909496478623075393)
            ·
              refine ⟨2591676682122358967306545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3455568909496478623075393 2591676682122358967306545)
              ·
                refine ⟨1943757511591769225479909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591676682122358967306545 1943757511591769225479909)
                ·
                  refine ⟨364454533423456729777483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1943757511591769225479909 364454533423456729777483)
                  ·
                    rfl

theorem cell22_3193977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 4].length) (baseStart_3193977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193977 prefixEnd_3193977 := by exact prefixLift 3193977
  have htrace : WordTrace (prefixWord ++ tailWord_3193977) baseStart_3193977 baseEnd_3193977 := by
    simpa [prefixWord, tailWord_3193977, baseEnd_3193977] using wordTrace_append hprefix tailTrace_3193977
  have hstable : (prefixWord ++ tailWord_3193977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193977).length < 2 ^ (prefixWord ++ tailWord_3193977).sum := by decide
  have hdescent : baseEnd_3193977 < baseStart_3193977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3193988 : List Nat := [2, 3, 2, 1, 2, 4, 1, 7]
def baseStart_3193988 : Nat := 118140960795 + 3193988 * 2 ^ 59
def prefixEnd_3193988 : Nat := 4983230072969 + 3 ^ 40 * 3193988 * 2
def baseEnd_3193988 : Nat := 121485262866129980811935

theorem tailTrace_3193988 : CollatzResearch.WordTrace tailWord_3193988 prefixEnd_3193988 121485262866129980811935 := by
  unfold tailWord_3193988
  simp only [CollatzResearch.WordTrace]
  refine ⟨58247156376367220283427309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77662875168489627044569745 58247156376367220283427309)
  ·
    refine ⟨21842683641137707606285241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58247156376367220283427309 21842683641137707606285241)
    ·
      refine ⟨16382012730853280704713931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21842683641137707606285241 16382012730853280704713931)
      ·
        refine ⟨24573019096279921057070897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16382012730853280704713931 24573019096279921057070897)
        ·
          refine ⟨18429764322209940792803173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24573019096279921057070897 18429764322209940792803173)
          ·
            refine ⟨3455580810414363898650595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18429764322209940792803173 3455580810414363898650595)
            ·
              refine ⟨5183371215621545847975893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455580810414363898650595 5183371215621545847975893)
              ·
                refine ⟨121485262866129980811935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5183371215621545847975893 121485262866129980811935)
                ·
                  rfl

theorem cell22_3193988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 7].length) (baseStart_3193988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3193988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3193988 prefixEnd_3193988 := by exact prefixLift 3193988
  have htrace : WordTrace (prefixWord ++ tailWord_3193988) baseStart_3193988 baseEnd_3193988 := by
    simpa [prefixWord, tailWord_3193988, baseEnd_3193988] using wordTrace_append hprefix tailTrace_3193988
  have hstable : (prefixWord ++ tailWord_3193988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3193988).length < 2 ^ (prefixWord ++ tailWord_3193988).sum := by decide
  have hdescent : baseEnd_3193988 < baseStart_3193988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3193988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194016 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 7]
def baseStart_3194016 : Nat := 118140960795 + 3194016 * 2 ^ 59
def prefixEnd_3194016 : Nat := 4983230072969 + 3 ^ 40 * 3194016 * 2
def baseEnd_3194016 : Nat := 364458983589129029202443

theorem tailTrace_3194016 : CollatzResearch.WordTrace tailWord_3194016 prefixEnd_3194016 364458983589129029202443 := by
  unfold tailWord_3194016
  simp only [CollatzResearch.WordTrace]
  refine ⟨58247666998316500674436951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77663555997755334232582601 58247666998316500674436951)
  ·
    refine ⟨87371500497474751011655427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58247666998316500674436951 87371500497474751011655427)
    ·
      refine ⟨131057250746212126517483141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87371500497474751011655427 131057250746212126517483141)
      ·
        refine ⟨24573234514914773722028089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131057250746212126517483141 24573234514914773722028089)
        ·
          refine ⟨18429925886186080291521067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24573234514914773722028089 18429925886186080291521067)
          ·
            refine ⟨27644888829279120437281601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18429925886186080291521067 27644888829279120437281601)
            ·
              refine ⟨20733666621959340327961201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27644888829279120437281601 20733666621959340327961201)
              ·
                refine ⟨15550249966469505245970901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20733666621959340327961201 15550249966469505245970901)
                ·
                  refine ⟨364458983589129029202443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15550249966469505245970901 364458983589129029202443)
                  ·
                    rfl

theorem cell22_3194016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_3194016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194016 prefixEnd_3194016 := by exact prefixLift 3194016
  have htrace : WordTrace (prefixWord ++ tailWord_3194016) baseStart_3194016 baseEnd_3194016 := by
    simpa [prefixWord, tailWord_3194016, baseEnd_3194016] using wordTrace_append hprefix tailTrace_3194016
  have hstable : (prefixWord ++ tailWord_3194016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194016).length < 2 ^ (prefixWord ++ tailWord_3194016).sum := by decide
  have hdescent : baseEnd_3194016 < baseStart_3194016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194031 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 2, 5]
def baseStart_3194031 : Nat := 118140960795 + 3194031 * 2 ^ 59
def prefixEnd_3194031 : Nat := 4983230072969 + 3 ^ 40 * 3194031 * 2
def baseEnd_3194031 : Nat := 1093382085573932048482283

theorem tailTrace_3194031 : CollatzResearch.WordTrace tailWord_3194031 prefixEnd_3194031 1093382085573932048482283 := by
  unfold tailWord_3194031
  simp only [CollatzResearch.WordTrace]
  refine ⟨116495881091578658910669947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77663920727719105940446631 116495881091578658910669947)
  ·
    refine ⟨174743821637367988366004921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116495881091578658910669947 174743821637367988366004921)
    ·
      refine ⟨131057866228025991274503691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174743821637367988366004921 131057866228025991274503691)
      ·
        refine ⟨196586799342038986911755537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131057866228025991274503691 196586799342038986911755537)
        ·
          refine ⟨147440099506529240183816653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196586799342038986911755537 147440099506529240183816653)
          ·
            refine ⟨55290037314948465068931245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147440099506529240183816653 55290037314948465068931245)
            ·
              refine ⟨20733763993105674400849217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55290037314948465068931245 20733763993105674400849217)
              ·
                refine ⟨15550322994829255800636913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20733763993105674400849217 15550322994829255800636913)
                ·
                  refine ⟨11662742246121941850477685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15550322994829255800636913 11662742246121941850477685)
                  ·
                    refine ⟨1093382085573932048482283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11662742246121941850477685 1093382085573932048482283)
                    ·
                      rfl

theorem cell22_3194031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_3194031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194031 prefixEnd_3194031 := by exact prefixLift 3194031
  have htrace : WordTrace (prefixWord ++ tailWord_3194031) baseStart_3194031 baseEnd_3194031 := by
    simpa [prefixWord, tailWord_3194031, baseEnd_3194031] using wordTrace_append hprefix tailTrace_3194031
  have hstable : (prefixWord ++ tailWord_3194031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194031).length < 2 ^ (prefixWord ++ tailWord_3194031).sum := by decide
  have hdescent : baseEnd_3194031 < baseStart_3194031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194033 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 7]
def baseStart_3194033 : Nat := 118140960795 + 3194033 * 2 ^ 59
def prefixEnd_3194033 : Nat := 4983230072969 + 3 ^ 40 * 3194033 * 2
def baseEnd_3194033 : Nat := 364460923404934903310759

theorem tailTrace_3194033 : CollatzResearch.WordTrace tailWord_3194033 prefixEnd_3194033 364460923404934903310759 := by
  unfold tailWord_3194033
  simp only [CollatzResearch.WordTrace]
  refine ⟨116495954037571413252242753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77663969358380942168161835 116495954037571413252242753)
  ·
    refine ⟨87371965528178559939182065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116495954037571413252242753 87371965528178559939182065)
    ·
      refine ⟨65528974146133919954386549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87371965528178559939182065 65528974146133919954386549)
      ·
        refine ⟨6143341326200054995723739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65528974146133919954386549 6143341326200054995723739)
        ·
          refine ⟨9215011989300082493585609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6143341326200054995723739 9215011989300082493585609)
          ·
            refine ⟨6911258991975061870189207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9215011989300082493585609 6911258991975061870189207)
            ·
              refine ⟨10366888487962592805283811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6911258991975061870189207 10366888487962592805283811)
              ·
                refine ⟨15550332731943889207925717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10366888487962592805283811 15550332731943889207925717)
                ·
                  refine ⟨364460923404934903310759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15550332731943889207925717 364460923404934903310759)
                  ·
                    rfl

theorem cell22_3194033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_3194033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194033 prefixEnd_3194033 := by exact prefixLift 3194033
  have htrace : WordTrace (prefixWord ++ tailWord_3194033) baseStart_3194033 baseEnd_3194033 := by
    simpa [prefixWord, tailWord_3194033, baseEnd_3194033] using wordTrace_append hprefix tailTrace_3194033
  have hstable : (prefixWord ++ tailWord_3194033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194033).length < 2 ^ (prefixWord ++ tailWord_3194033).sum := by decide
  have hdescent : baseEnd_3194033 < baseStart_3194033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194095 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 6]
def baseStart_3194095 : Nat := 118140960795 + 3194095 * 2 ^ 59
def prefixEnd_3194095 : Nat := 4983230072969 + 3 ^ 40 * 3194095 * 2
def baseEnd_3194095 : Nat := 364467998027285738294029

theorem tailTrace_3194095 : CollatzResearch.WordTrace tailWord_3194095 prefixEnd_3194095 364467998027285738294029 := by
  unfold tailWord_3194095
  simp only [CollatzResearch.WordTrace]
  refine ⟨116498215363346797840999739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77665476908897865227333159 116498215363346797840999739)
  ·
    refine ⟨174747323045020196761499609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116498215363346797840999739 174747323045020196761499609)
    ·
      refine ⟨131060492283765147571124707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174747323045020196761499609 131060492283765147571124707)
      ·
        refine ⟨196590738425647721356687061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131060492283765147571124707 196590738425647721356687061)
        ·
          refine ⟨4607595431851118469297353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 196590738425647721356687061 4607595431851118469297353)
          ·
            refine ⟨3455696573888338851973015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4607595431851118469297353 3455696573888338851973015)
            ·
              refine ⟨5183544860832508277959523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455696573888338851973015 5183544860832508277959523)
              ·
                refine ⟨7775317291248762416939285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183544860832508277959523 7775317291248762416939285)
                ·
                  refine ⟨364467998027285738294029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7775317291248762416939285 364467998027285738294029)
                  ·
                    rfl

theorem cell22_3194095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 6].length) (baseStart_3194095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194095 prefixEnd_3194095 := by exact prefixLift 3194095
  have htrace : WordTrace (prefixWord ++ tailWord_3194095) baseStart_3194095 baseEnd_3194095 := by
    simpa [prefixWord, tailWord_3194095, baseEnd_3194095] using wordTrace_append hprefix tailTrace_3194095
  have hstable : (prefixWord ++ tailWord_3194095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194095).length < 2 ^ (prefixWord ++ tailWord_3194095).sum := by decide
  have hdescent : baseEnd_3194095 < baseStart_3194095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194114 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3194114 : Nat := 118140960795 + 3194114 * 2 ^ 59
def prefixEnd_3194114 : Nat := 4983230072969 + 3 ^ 40 * 3194114 * 2
def baseEnd_3194114 : Nat := 1093410498170147498657029

theorem tailTrace_3194114 : CollatzResearch.WordTrace tailWord_3194114 prefixEnd_3194114 1093410498170147498657029 := by
  unfold tailWord_3194114
  simp only [CollatzResearch.WordTrace]
  refine ⟨29124727087569491021485349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77665938900185309390627597 29124727087569491021485349)
  ·
    refine ⟨5460886328919279566528503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29124727087569491021485349 5460886328919279566528503)
    ·
      refine ⟨8191329493378919349792755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5460886328919279566528503 8191329493378919349792755)
      ·
        refine ⟨12286994240068379024689133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8191329493378919349792755 12286994240068379024689133)
        ·
          refine ⟨4607622840025642134258425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12286994240068379024689133 4607622840025642134258425)
          ·
            refine ⟨3455717130019231600693819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4607622840025642134258425 3455717130019231600693819)
            ·
              refine ⟨5183575695028847401040729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455717130019231600693819 5183575695028847401040729)
              ·
                refine ⟨3887681771271635550780547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5183575695028847401040729 3887681771271635550780547)
                ·
                  refine ⟨5831522656907453326170821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3887681771271635550780547 5831522656907453326170821)
                  ·
                    refine ⟨1093410498170147498657029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5831522656907453326170821 1093410498170147498657029)
                    ·
                      rfl

theorem cell22_3194114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3194114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194114 prefixEnd_3194114 := by exact prefixLift 3194114
  have htrace : WordTrace (prefixWord ++ tailWord_3194114) baseStart_3194114 baseEnd_3194114 := by
    simpa [prefixWord, tailWord_3194114, baseEnd_3194114] using wordTrace_append hprefix tailTrace_3194114
  have hstable : (prefixWord ++ tailWord_3194114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194114).length < 2 ^ (prefixWord ++ tailWord_3194114).sum := by decide
  have hdescent : baseEnd_3194114 < baseStart_3194114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194146 : List Nat := [3, 3, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3194146 : Nat := 118140960795 + 3194146 * 2 ^ 59
def prefixEnd_3194146 : Nat := 4983230072969 + 3 ^ 40 * 3194146 * 2
def baseEnd_3194146 : Nat := 364473817474703360618977

theorem tailTrace_3194146 : CollatzResearch.WordTrace tailWord_3194146 prefixEnd_3194146 364473817474703360618977 := by
  unfold tailWord_3194146
  simp only [CollatzResearch.WordTrace]
  refine ⟨29125018871540508387776573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77666716990774689034070861 29125018871540508387776573)
  ·
    refine ⟨10921882076827690645416215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29125018871540508387776573 10921882076827690645416215)
    ·
      refine ⟨16382823115241535968124323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10921882076827690645416215 16382823115241535968124323)
      ·
        refine ⟨24574234672862303952186485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16382823115241535968124323 24574234672862303952186485)
        ·
          refine ⟨2303834500580840995517483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24574234672862303952186485 2303834500580840995517483)
          ·
            refine ⟨3455751750871261493276225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303834500580840995517483 3455751750871261493276225)
            ·
              refine ⟨2591813813153446119957169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3455751750871261493276225 2591813813153446119957169)
              ·
                refine ⟨1943860359865084589967877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2591813813153446119957169 1943860359865084589967877)
                ·
                  refine ⟨364473817474703360618977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1943860359865084589967877 364473817474703360618977)
                  ·
                    rfl

theorem cell22_3194146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3194146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194146 prefixEnd_3194146 := by exact prefixLift 3194146
  have htrace : WordTrace (prefixWord ++ tailWord_3194146) baseStart_3194146 baseEnd_3194146 := by
    simpa [prefixWord, tailWord_3194146, baseEnd_3194146] using wordTrace_append hprefix tailTrace_3194146
  have hstable : (prefixWord ++ tailWord_3194146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194146).length < 2 ^ (prefixWord ++ tailWord_3194146).sum := by decide
  have hdescent : baseEnd_3194146 < baseStart_3194146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194157 : List Nat := [1, 5, 3, 1, 1, 3, 1, 7]
def baseStart_3194157 : Nat := 118140960795 + 3194157 * 2 ^ 59
def prefixEnd_3194157 : Nat := 4983230072969 + 3 ^ 40 * 3194157 * 2
def baseEnd_3194157 : Nat := 121491690883212191092433

theorem tailTrace_3194157 : CollatzResearch.WordTrace tailWord_3194157 prefixEnd_3194157 121491690883212191092433 := by
  unfold tailWord_3194157
  simp only [CollatzResearch.WordTrace]
  refine ⟨116500476689122182429756725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77666984459414788286504483 116500476689122182429756725)
  ·
    refine ⟨10921919689605204602789693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116500476689122182429756725 10921919689605204602789693)
    ·
      refine ⟨4095719883601951726046135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10921919689605204602789693 4095719883601951726046135)
      ·
        refine ⟨6143579825402927589069203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4095719883601951726046135 6143579825402927589069203)
        ·
          refine ⟨9215369738104391383603805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6143579825402927589069203 9215369738104391383603805)
          ·
            refine ⟨3455763651789146768851427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9215369738104391383603805 3455763651789146768851427)
            ·
              refine ⟨5183645477683720153277141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455763651789146768851427 5183645477683720153277141)
              ·
                refine ⟨121491690883212191092433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5183645477683720153277141 121491690883212191092433)
                ·
                  rfl

theorem cell22_3194157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 7].length) (baseStart_3194157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194157 prefixEnd_3194157 := by exact prefixLift 3194157
  have htrace : WordTrace (prefixWord ++ tailWord_3194157) baseStart_3194157 baseEnd_3194157 := by
    simpa [prefixWord, tailWord_3194157, baseEnd_3194157] using wordTrace_append hprefix tailTrace_3194157
  have hstable : (prefixWord ++ tailWord_3194157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194157).length < 2 ^ (prefixWord ++ tailWord_3194157).sum := by decide
  have hdescent : baseEnd_3194157 < baseStart_3194157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194245 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 4, 3]
def baseStart_3194245 : Nat := 118140960795 + 3194245 * 2 ^ 59
def prefixEnd_3194245 : Nat := 4983230072969 + 3 ^ 40 * 3194245 * 2
def baseEnd_3194245 : Nat := 1093455342147306823631627

theorem tailTrace_3194245 : CollatzResearch.WordTrace tailWord_3194245 prefixEnd_3194245 1093455342147306823631627 := by
  unfold tailWord_3194245
  simp only [CollatzResearch.WordTrace]
  refine ⟨116503686312803373458960189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77669124208535582305973459 116503686312803373458960189)
  ·
    refine ⟨43688882367301265047110071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116503686312803373458960189 43688882367301265047110071)
    ·
      refine ⟨65533323550951897570665107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43688882367301265047110071 65533323550951897570665107)
      ·
        refine ⟨98299985326427846355997661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65533323550951897570665107 98299985326427846355997661)
        ·
          refine ⟨36862494497410442383499123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98299985326427846355997661 36862494497410442383499123)
          ·
            refine ⟨55293741746115663575248685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36862494497410442383499123 55293741746115663575248685)
            ·
              refine ⟨20735153154793373840718257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55293741746115663575248685 20735153154793373840718257)
              ·
                refine ⟨15551364866095030380538693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20735153154793373840718257 15551364866095030380538693)
                ·
                  refine ⟨2915880912392818196351005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15551364866095030380538693 2915880912392818196351005)
                  ·
                    refine ⟨1093455342147306823631627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2915880912392818196351005 1093455342147306823631627)
                    ·
                      rfl

theorem cell22_3194245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_3194245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194245 prefixEnd_3194245 := by exact prefixLift 3194245
  have htrace : WordTrace (prefixWord ++ tailWord_3194245) baseStart_3194245 baseEnd_3194245 := by
    simpa [prefixWord, tailWord_3194245, baseEnd_3194245] using wordTrace_append hprefix tailTrace_3194245
  have hstable : (prefixWord ++ tailWord_3194245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194245).length < 2 ^ (prefixWord ++ tailWord_3194245).sum := by decide
  have hdescent : baseEnd_3194245 < baseStart_3194245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194247 : List Nat := [1, 1, 4, 2, 2, 2, 3, 3, 4]
def baseStart_3194247 : Nat := 118140960795 + 3194247 * 2 ^ 59
def prefixEnd_3194247 : Nat := 4983230072969 + 3 ^ 40 * 3194247 * 2
def baseEnd_3194247 : Nat := 364485342262726495027207

theorem tailTrace_3194247 : CollatzResearch.WordTrace tailWord_3194247 prefixEnd_3194247 364485342262726495027207 := by
  unfold tailWord_3194247
  simp only [CollatzResearch.WordTrace]
  refine ⟨116503759258796127800532995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77669172839197418533688663 116503759258796127800532995)
  ·
    refine ⟨174755638888194191700799493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116503759258796127800532995 174755638888194191700799493)
    ·
      refine ⟨32766682291536410943899905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174755638888194191700799493 32766682291536410943899905)
      ·
        refine ⟨24575011718652308207924929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32766682291536410943899905 24575011718652308207924929)
        ·
          refine ⟨18431258788989231155943697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24575011718652308207924929 18431258788989231155943697)
          ·
            refine ⟨13823444091741923366957773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18431258788989231155943697 13823444091741923366957773)
            ·
              refine ⟨5183791534403221262609165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13823444091741923366957773 5183791534403221262609165)
              ·
                refine ⟨1943921825401207973478437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5183791534403221262609165 1943921825401207973478437)
                ·
                  refine ⟨364485342262726495027207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1943921825401207973478437 364485342262726495027207)
                  ·
                    rfl

theorem cell22_3194247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 4].length) (baseStart_3194247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194247 prefixEnd_3194247 := by exact prefixLift 3194247
  have htrace : WordTrace (prefixWord ++ tailWord_3194247) baseStart_3194247 baseEnd_3194247 := by
    simpa [prefixWord, tailWord_3194247, baseEnd_3194247] using wordTrace_append hprefix tailTrace_3194247
  have hstable : (prefixWord ++ tailWord_3194247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194247).length < 2 ^ (prefixWord ++ tailWord_3194247).sum := by decide
  have hdescent : baseEnd_3194247 < baseStart_3194247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194264 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 6]
def baseStart_3194264 : Nat := 118140960795 + 3194264 * 2 ^ 59
def prefixEnd_3194264 : Nat := 4983230072969 + 3 ^ 40 * 3194264 * 2
def baseEnd_3194264 : Nat := 364487282078532369135523

theorem tailTrace_3194264 : CollatzResearch.WordTrace tailWord_3194264 prefixEnd_3194264 364487282078532369135523 := by
  unfold tailWord_3194264
  simp only [CollatzResearch.WordTrace]
  refine ⟨58252189649867269851950923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77669586199823026469267897 58252189649867269851950923)
  ·
    refine ⟨87378284474800904777926385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58252189649867269851950923 87378284474800904777926385)
    ·
      refine ⟨65533713356100678583444789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87378284474800904777926385 65533713356100678583444789)
      ·
        refine ⟨6143785627134438617197949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65533713356100678583444789 6143785627134438617197949)
        ·
          refine ⟨2303919610175414481449231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6143785627134438617197949 2303919610175414481449231)
          ·
            refine ⟨3455879415263121722173847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2303919610175414481449231 3455879415263121722173847)
            ·
              refine ⟨5183819122894682583260771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3455879415263121722173847 5183819122894682583260771)
              ·
                refine ⟨7775728684342023874891157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5183819122894682583260771 7775728684342023874891157)
                ·
                  refine ⟨364487282078532369135523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7775728684342023874891157 364487282078532369135523)
                  ·
                    rfl

theorem cell22_3194264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 6].length) (baseStart_3194264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194264 prefixEnd_3194264 := by exact prefixLift 3194264
  have htrace : WordTrace (prefixWord ++ tailWord_3194264) baseStart_3194264 baseEnd_3194264 := by
    simpa [prefixWord, tailWord_3194264, baseEnd_3194264] using wordTrace_append hprefix tailTrace_3194264
  have hstable : (prefixWord ++ tailWord_3194264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194264).length < 2 ^ (prefixWord ++ tailWord_3194264).sum := by decide
  have hdescent : baseEnd_3194264 < baseStart_3194264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194288 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_3194288 : Nat := 118140960795 + 3194288 * 2 ^ 59
def prefixEnd_3194288 : Nat := 4983230072969 + 3 ^ 40 * 3194288 * 2
def baseEnd_3194288 : Nat := 1093470061926069044806495

theorem tailTrace_3194288 : CollatzResearch.WordTrace tailWord_3194288 prefixEnd_3194288 1093470061926069044806495 := by
  unfold tailWord_3194288
  simp only [CollatzResearch.WordTrace]
  refine ⟨58252627325823795901387759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77670169767765061201850345 58252627325823795901387759)
  ·
    refine ⟨87378940988735693852081639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58252627325823795901387759 87378940988735693852081639)
    ·
      refine ⟨131068411483103540778122459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87378940988735693852081639 131068411483103540778122459)
      ·
        refine ⟨196602617224655311167183689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131068411483103540778122459 196602617224655311167183689)
        ·
          refine ⟨147451962918491483375387767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196602617224655311167183689 147451962918491483375387767)
          ·
            refine ⟨221177944377737225063081651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147451962918491483375387767 221177944377737225063081651)
            ·
              refine ⟨331766916566605837594622477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221177944377737225063081651 331766916566605837594622477)
              ·
                refine ⟨124412593712477189097983429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331766916566605837594622477 124412593712477189097983429)
                ·
                  refine ⟨23327361321089472955871893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 124412593712477189097983429 23327361321089472955871893)
                  ·
                    refine ⟨1093470061926069044806495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23327361321089472955871893 1093470061926069044806495)
                    ·
                      rfl

theorem cell22_3194288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_3194288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194288 prefixEnd_3194288 := by exact prefixLift 3194288
  have htrace : WordTrace (prefixWord ++ tailWord_3194288) baseStart_3194288 baseEnd_3194288 := by
    simpa [prefixWord, tailWord_3194288, baseEnd_3194288] using wordTrace_append hprefix tailTrace_3194288
  have hstable : (prefixWord ++ tailWord_3194288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194288).length < 2 ^ (prefixWord ++ tailWord_3194288).sum := by decide
  have hdescent : baseEnd_3194288 < baseStart_3194288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194303 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 9]
def baseStart_3194303 : Nat := 118140960795 + 3194303 * 2 ^ 59
def prefixEnd_3194303 : Nat := 4983230072969 + 3 ^ 40 * 3194303 * 2
def baseEnd_3194303 : Nat := 364491732244204668560483

theorem tailTrace_3194303 : CollatzResearch.WordTrace tailWord_3194303 prefixEnd_3194303 364491732244204668560483 := by
  unfold tailWord_3194303
  simp only [CollatzResearch.WordTrace]
  refine ⟨116505801746593249364571563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77670534497728832909714375 116505801746593249364571563)
  ·
    refine ⟨174758702619889874046857345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116505801746593249364571563 174758702619889874046857345)
    ·
      refine ⟨131069026964917405535143009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174758702619889874046857345 131069026964917405535143009)
      ·
        refine ⟨98301770223688054151357257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131069026964917405535143009 98301770223688054151357257)
        ·
          refine ⟨73726327667766040613517943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98301770223688054151357257 73726327667766040613517943)
          ·
            refine ⟨110589491501649060920276915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73726327667766040613517943 110589491501649060920276915)
            ·
              refine ⟨165884237252473591380415373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110589491501649060920276915 165884237252473591380415373)
              ·
                refine ⟨62206588969677596767655765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165884237252473591380415373 62206588969677596767655765)
                ·
                  refine ⟨364491732244204668560483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62206588969677596767655765 364491732244204668560483)
                  ·
                    rfl

theorem cell22_3194303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 9].length) (baseStart_3194303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194303 prefixEnd_3194303 := by exact prefixLift 3194303
  have htrace : WordTrace (prefixWord ++ tailWord_3194303) baseStart_3194303 baseEnd_3194303 := by
    simpa [prefixWord, tailWord_3194303, baseEnd_3194303] using wordTrace_append hprefix tailTrace_3194303
  have hstable : (prefixWord ++ tailWord_3194303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194303).length < 2 ^ (prefixWord ++ tailWord_3194303).sum := by decide
  have hdescent : baseEnd_3194303 < baseStart_3194303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194335 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 2, 5]
def baseStart_3194335 : Nat := 118140960795 + 3194335 * 2 ^ 59
def prefixEnd_3194335 : Nat := 4983230072969 + 3 ^ 40 * 3194335 * 2
def baseEnd_3194335 : Nat := 1093486150986576588881351

theorem tailTrace_3194335 : CollatzResearch.WordTrace tailWord_3194335 prefixEnd_3194335 1093486150986576588881351 := by
  unfold tailWord_3194335
  simp only [CollatzResearch.WordTrace]
  refine ⟨116506968882477318829736459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77671312588318212553157639 116506968882477318829736459)
  ·
    refine ⟨174760453323715978244604689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116506968882477318829736459 174760453323715978244604689)
    ·
      refine ⟨131070339992786983683453517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174760453323715978244604689 131070339992786983683453517)
      ·
        refine ⟨49151377497295118881295069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131070339992786983683453517 49151377497295118881295069)
        ·
          refine ⟨18431766561485669580485651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49151377497295118881295069 18431766561485669580485651)
          ·
            refine ⟨27647649842228504370728477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18431766561485669580485651 27647649842228504370728477)
            ·
              refine ⟨10367868690835689139023179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27647649842228504370728477 10367868690835689139023179)
              ·
                refine ⟨15551803036253533708534769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10367868690835689139023179 15551803036253533708534769)
                ·
                  refine ⟨11663852277190150281401077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15551803036253533708534769 11663852277190150281401077)
                  ·
                    refine ⟨1093486150986576588881351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11663852277190150281401077 1093486150986576588881351)
                    ·
                      rfl

theorem cell22_3194335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_3194335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194335 prefixEnd_3194335 := by exact prefixLift 3194335
  have htrace : WordTrace (prefixWord ++ tailWord_3194335) baseStart_3194335 baseEnd_3194335 := by
    simpa [prefixWord, tailWord_3194335, baseEnd_3194335] using wordTrace_append hprefix tailTrace_3194335
  have hstable : (prefixWord ++ tailWord_3194335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194335).length < 2 ^ (prefixWord ++ tailWord_3194335).sum := by decide
  have hdescent : baseEnd_3194335 < baseStart_3194335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194414 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_3194414 : Nat := 118140960795 + 3194414 * 2 ^ 59
def prefixEnd_3194414 : Nat := 4983230072969 + 3 ^ 40 * 3194414 * 2
def baseEnd_3194414 : Nat := 1093513194301046716156109

theorem tailTrace_3194414 : CollatzResearch.WordTrace tailWord_3194414 prefixEnd_3194414 1093513194301046716156109 := by
  unfold tailWord_3194414
  simp only [CollatzResearch.WordTrace]
  refine ⟨14563731281148889415232787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77673233499460743547908197 14563731281148889415232787)
  ·
    refine ⟨21845596921723334122849181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14563731281148889415232787 21845596921723334122849181)
    ·
      refine ⟨8192098845646250296068443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21845596921723334122849181 8192098845646250296068443)
      ·
        refine ⟨12288148268469375444102665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8192098845646250296068443 12288148268469375444102665)
        ·
          refine ⟨9216111201352031583076999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12288148268469375444102665 9216111201352031583076999)
          ·
            refine ⟨13824166802028047374615499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9216111201352031583076999 13824166802028047374615499)
            ·
              refine ⟨20736250203042071061923249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13824166802028047374615499 20736250203042071061923249)
              ·
                refine ⟨15552187652281553296442437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20736250203042071061923249 15552187652281553296442437)
                ·
                  refine ⟨2916035184802791243082957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15552187652281553296442437 2916035184802791243082957)
                  ·
                    refine ⟨1093513194301046716156109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2916035184802791243082957 1093513194301046716156109)
                    ·
                      rfl

theorem cell22_3194414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_3194414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194414 prefixEnd_3194414 := by exact prefixLift 3194414
  have htrace : WordTrace (prefixWord ++ tailWord_3194414) baseStart_3194414 baseEnd_3194414 := by
    simpa [prefixWord, tailWord_3194414, baseEnd_3194414] using wordTrace_append hprefix tailTrace_3194414
  have hstable : (prefixWord ++ tailWord_3194414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194414).length < 2 ^ (prefixWord ++ tailWord_3194414).sum := by decide
  have hdescent : baseEnd_3194414 < baseStart_3194414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194429 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_3194429 : Nat := 118140960795 + 3194429 * 2 ^ 59
def prefixEnd_3194429 : Nat := 4983230072969 + 3 ^ 40 * 3194429 * 2
def baseEnd_3194429 : Nat := 1093518329107591677031063

theorem tailTrace_3194429 : CollatzResearch.WordTrace tailWord_3194429 prefixEnd_3194429 1093518329107591677031063 := by
  unfold tailWord_3194429
  simp only [CollatzResearch.WordTrace]
  refine ⟨116510397344136772883658341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77673598229424515255772227 116510397344136772883658341)
  ·
    refine ⟨21845699502025644915685939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116510397344136772883658341 21845699502025644915685939)
    ·
      refine ⟨32768549253038467373528909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21845699502025644915685939 32768549253038467373528909)
      ·
        refine ⟨12288205969889425265073341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32768549253038467373528909 12288205969889425265073341)
        ·
          refine ⟨4608077238708534474402503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12288205969889425265073341 4608077238708534474402503)
          ·
            refine ⟨6912115858062801711603755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4608077238708534474402503 6912115858062801711603755)
            ·
              refine ⟨10368173787094202567405633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6912115858062801711603755 10368173787094202567405633)
              ·
                refine ⟨7776130340320651925554225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10368173787094202567405633 7776130340320651925554225)
                ·
                  refine ⟨5832097755240488944165669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7776130340320651925554225 5832097755240488944165669)
                  ·
                    refine ⟨1093518329107591677031063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5832097755240488944165669 1093518329107591677031063)
                    ·
                      rfl

theorem cell22_3194429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_3194429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194429 prefixEnd_3194429 := by exact prefixLift 3194429
  have htrace : WordTrace (prefixWord ++ tailWord_3194429) baseStart_3194429 baseEnd_3194429 := by
    simpa [prefixWord, tailWord_3194429, baseEnd_3194429] using wordTrace_append hprefix tailTrace_3194429
  have hstable : (prefixWord ++ tailWord_3194429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194429).length < 2 ^ (prefixWord ++ tailWord_3194429).sum := by decide
  have hdescent : baseEnd_3194429 < baseStart_3194429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194493 : List Nat := [1, 4, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_3194493 : Nat := 118140960795 + 3194493 * 2 ^ 59
def prefixEnd_3194493 : Nat := 4983230072969 + 3 ^ 40 * 3194493 * 2
def baseEnd_3194493 : Nat := 1093540237615516843430867

theorem tailTrace_3194493 : CollatzResearch.WordTrace tailWord_3194493 prefixEnd_3194493 1093540237615516843430867 := by
  unfold tailWord_3194493
  simp only [CollatzResearch.WordTrace]
  refine ⟨116512731615904911813988133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77675154410603274542658755 116512731615904911813988133)
  ·
    refine ⟨21846137177982170965122775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116512731615904911813988133 21846137177982170965122775)
    ·
      refine ⟨32769205766973256447684163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21846137177982170965122775 32769205766973256447684163)
      ·
        refine ⟨49153808650459884671526245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32769205766973256447684163 49153808650459884671526245)
        ·
          refine ⟨9216339121961228375911171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49153808650459884671526245 9216339121961228375911171)
          ·
            refine ⟨13824508682941842563866757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9216339121961228375911171 13824508682941842563866757)
            ·
              refine ⟨2592095378051595480725017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13824508682941842563866757 2592095378051595480725017)
              ·
                refine ⟨1944071533538696610543763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2592095378051595480725017 1944071533538696610543763)
                ·
                  refine ⟨2916107300308044915815645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944071533538696610543763 2916107300308044915815645)
                  ·
                    refine ⟨1093540237615516843430867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2916107300308044915815645 1093540237615516843430867)
                    ·
                      rfl

theorem cell22_3194493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_3194493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194493 prefixEnd_3194493 := by exact prefixLift 3194493
  have htrace : WordTrace (prefixWord ++ tailWord_3194493) baseStart_3194493 baseEnd_3194493 := by
    simpa [prefixWord, tailWord_3194493, baseEnd_3194493] using wordTrace_append hprefix tailTrace_3194493
  have hstable : (prefixWord ++ tailWord_3194493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194493).length < 2 ^ (prefixWord ++ tailWord_3194493).sum := by decide
  have hdescent : baseEnd_3194493 < baseStart_3194493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194547 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 4, 4]
def baseStart_3194547 : Nat := 118140960795 + 3194547 * 2 ^ 59
def prefixEnd_3194547 : Nat := 4983230072969 + 3 ^ 40 * 3194547 * 2
def baseEnd_3194547 : Nat := 1093558722919078702580701

theorem tailTrace_3194547 : CollatzResearch.WordTrace tailWord_3194547 prefixEnd_3194547 1093558722919078702580701 := by
  unfold tailWord_3194547
  simp only [CollatzResearch.WordTrace]
  refine ⟨116514701157709279036453895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77676467438472852690969263 116514701157709279036453895)
  ·
    refine ⟨174772051736563918554680843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116514701157709279036453895 174772051736563918554680843)
    ·
      refine ⟨262158077604845877832021265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174772051736563918554680843 262158077604845877832021265)
      ·
        refine ⟨196618558203634408374015949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262158077604845877832021265 196618558203634408374015949)
        ·
          refine ⟨73731959326362903140255981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196618558203634408374015949 73731959326362903140255981)
          ·
            refine ⟨27649484747386088677595993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73731959326362903140255981 27649484747386088677595993)
            ·
              refine ⟨20737113560539566508196995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27649484747386088677595993 20737113560539566508196995)
              ·
                refine ⟨31105670340809349762295493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20737113560539566508196995 31105670340809349762295493)
                ·
                  refine ⟨5832313188901753080430405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31105670340809349762295493 5832313188901753080430405)
                  ·
                    refine ⟨1093558722919078702580701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5832313188901753080430405 1093558722919078702580701)
                    ·
                      rfl

theorem cell22_3194547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 4].length) (baseStart_3194547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194547 prefixEnd_3194547 := by exact prefixLift 3194547
  have htrace : WordTrace (prefixWord ++ tailWord_3194547) baseStart_3194547 baseEnd_3194547 := by
    simpa [prefixWord, tailWord_3194547, baseEnd_3194547] using wordTrace_append hprefix tailTrace_3194547
  have hstable : (prefixWord ++ tailWord_3194547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194547).length < 2 ^ (prefixWord ++ tailWord_3194547).sum := by decide
  have hdescent : baseEnd_3194547 < baseStart_3194547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194607 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 7]
def baseStart_3194607 : Nat := 118140960795 + 3194607 * 2 ^ 59
def prefixEnd_3194607 : Nat := 4983230072969 + 3 ^ 40 * 3194607 * 2
def baseEnd_3194607 : Nat := 364526420715086182026839

theorem tailTrace_3194607 : CollatzResearch.WordTrace tailWord_3194607 prefixEnd_3194607 364526420715086182026839 := by
  unfold tailWord_3194607
  simp only [CollatzResearch.WordTrace]
  refine ⟨116516889537491909283638075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77677926358327939522425383 116516889537491909283638075)
  ·
    refine ⟨174775334306237863925457113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116516889537491909283638075 174775334306237863925457113)
    ·
      refine ⟨131081500729678397944092835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174775334306237863925457113 131081500729678397944092835)
      ·
        refine ⟨196622251094517596916139253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131081500729678397944092835 196622251094517596916139253)
        ·
          refine ⟨18433336040111024710888055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196622251094517596916139253 18433336040111024710888055)
          ·
            refine ⟨27650004060166537066332083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18433336040111024710888055 27650004060166537066332083)
            ·
              refine ⟨41475006090249805599498125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27650004060166537066332083 41475006090249805599498125)
              ·
                refine ⟨15553127283843677099811797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41475006090249805599498125 15553127283843677099811797)
                ·
                  refine ⟨364526420715086182026839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15553127283843677099811797 364526420715086182026839)
                  ·
                    rfl

theorem cell22_3194607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 7].length) (baseStart_3194607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194607 prefixEnd_3194607 := by exact prefixLift 3194607
  have htrace : WordTrace (prefixWord ++ tailWord_3194607) baseStart_3194607 baseEnd_3194607 := by
    simpa [prefixWord, tailWord_3194607, baseEnd_3194607] using wordTrace_append hprefix tailTrace_3194607
  have hstable : (prefixWord ++ tailWord_3194607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194607).length < 2 ^ (prefixWord ++ tailWord_3194607).sum := by decide
  have hdescent : baseEnd_3194607 < baseStart_3194607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194611 : List Nat := [1, 1, 1, 2, 2, 3, 2, 6, 1, 3]
def baseStart_3194611 : Nat := 118140960795 + 3194611 * 2 ^ 59
def prefixEnd_3194611 : Nat := 4983230072969 + 3 ^ 40 * 3194611 * 2
def baseEnd_3194611 : Nat := 1093580631427003868980505

theorem tailTrace_3194611 : CollatzResearch.WordTrace tailWord_3194611 prefixEnd_3194611 1093580631427003868980505 := by
  unfold tailWord_3194611
  simp only [CollatzResearch.WordTrace]
  refine ⟨116517035429477417966783687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77678023619651611977855791 116517035429477417966783687)
  ·
    refine ⟨174775553144216126950175531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116517035429477417966783687 174775553144216126950175531)
    ·
      refine ⟨262163329716324190425263297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174775553144216126950175531 262163329716324190425263297)
      ·
        refine ⟨196622497287243142818947473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262163329716324190425263297 196622497287243142818947473)
        ·
          refine ⟨147466872965432357114210605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196622497287243142818947473 147466872965432357114210605)
          ·
            refine ⟨55300077362037133917828977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147466872965432357114210605 55300077362037133917828977)
            ·
              refine ⟨41475058021527850438371733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55300077362037133917828977 41475058021527850438371733)
              ·
                refine ⟨1944143344759117989298675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41475058021527850438371733 1944143344759117989298675)
                ·
                  refine ⟨2916215017138676983948013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944143344759117989298675 2916215017138676983948013)
                  ·
                    refine ⟨1093580631427003868980505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2916215017138676983948013 1093580631427003868980505)
                    ·
                      rfl

theorem cell22_3194611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 1, 3].length) (baseStart_3194611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194611 prefixEnd_3194611 := by exact prefixLift 3194611
  have htrace : WordTrace (prefixWord ++ tailWord_3194611) baseStart_3194611 baseEnd_3194611 := by
    simpa [prefixWord, tailWord_3194611, baseEnd_3194611] using wordTrace_append hprefix tailTrace_3194611
  have hstable : (prefixWord ++ tailWord_3194611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194611).length < 2 ^ (prefixWord ++ tailWord_3194611).sum := by decide
  have hdescent : baseEnd_3194611 < baseStart_3194611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194684 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_3194684 : Nat := 118140960795 + 3194684 * 2 ^ 59
def prefixEnd_3194684 : Nat := 4983230072969 + 3 ^ 40 * 3194684 * 2
def baseEnd_3194684 : Nat := 1093605620818856011905281

theorem tailTrace_3194684 : CollatzResearch.WordTrace tailWord_3194684 prefixEnd_3194684 1093605620818856011905281 := by
  unfold tailWord_3194684
  simp only [CollatzResearch.WordTrace]
  refine ⟨58259848979106475717095553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77679798638808634289460737 58259848979106475717095553)
  ·
    refine ⟨43694886734329856787821665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58259848979106475717095553 43694886734329856787821665)
    ·
      refine ⟨32771165050747392590866249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43694886734329856787821665 32771165050747392590866249)
      ·
        refine ⟨24578373788060544443149687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32771165050747392590866249 24578373788060544443149687)
        ·
          refine ⟨36867560682090816664724531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24578373788060544443149687 36867560682090816664724531)
          ·
            refine ⟨55301341023136224997086797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36867560682090816664724531 55301341023136224997086797)
            ·
              refine ⟨20738002883676084373907549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55301341023136224997086797 20738002883676084373907549)
              ·
                refine ⟨7776751081378531640215331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20738002883676084373907549 7776751081378531640215331)
                ·
                  refine ⟨11665126622067797460322997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7776751081378531640215331 11665126622067797460322997)
                  ·
                    refine ⟨1093605620818856011905281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11665126622067797460322997 1093605620818856011905281)
                    ·
                      rfl

theorem cell22_3194684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_3194684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194684 prefixEnd_3194684 := by exact prefixLift 3194684
  have htrace : WordTrace (prefixWord ++ tailWord_3194684) baseStart_3194684 baseEnd_3194684 := by
    simpa [prefixWord, tailWord_3194684, baseEnd_3194684] using wordTrace_append hprefix tailTrace_3194684
  have hstable : (prefixWord ++ tailWord_3194684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194684).length < 2 ^ (prefixWord ++ tailWord_3194684).sum := by decide
  have hdescent : baseEnd_3194684 < baseStart_3194684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194686 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_3194686 : Nat := 118140960795 + 3194686 * 2 ^ 59
def prefixEnd_3194686 : Nat := 4983230072969 + 3 ^ 40 * 3194686 * 2
def baseEnd_3194686 : Nat := 364535435153242891118425

theorem tailTrace_3194686 : CollatzResearch.WordTrace tailWord_3194686 prefixEnd_3194686 364535435153242891118425 := by
  unfold tailWord_3194686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14564971363025713221970489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77679847269470470517175941 14564971363025713221970489)
  ·
    refine ⟨10923728522269284916477867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14564971363025713221970489 10923728522269284916477867)
    ·
      refine ⟨16385592783403927374716801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10923728522269284916477867 16385592783403927374716801)
      ·
        refine ⟨12289194587552945531037601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16385592783403927374716801 12289194587552945531037601)
        ·
          refine ⟨9216895940664709148278201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12289194587552945531037601 9216895940664709148278201)
          ·
            refine ⟨6912671955498531861208651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9216895940664709148278201 6912671955498531861208651)
            ·
              refine ⟨10369007933247797791812977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6912671955498531861208651 10369007933247797791812977)
              ·
                refine ⟨7776755949935848343859733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10369007933247797791812977 7776755949935848343859733)
                ·
                  refine ⟨364535435153242891118425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7776755949935848343859733 364535435153242891118425)
                  ·
                    rfl

theorem cell22_3194686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_3194686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194686 prefixEnd_3194686 := by exact prefixLift 3194686
  have htrace : WordTrace (prefixWord ++ tailWord_3194686) baseStart_3194686 baseEnd_3194686 := by
    simpa [prefixWord, tailWord_3194686, baseEnd_3194686] using wordTrace_append hprefix tailTrace_3194686
  have hstable : (prefixWord ++ tailWord_3194686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194686).length < 2 ^ (prefixWord ++ tailWord_3194686).sum := by decide
  have hdescent : baseEnd_3194686 < baseStart_3194686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194746 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 3, 3]
def baseStart_3194746 : Nat := 118140960795 + 3194746 * 2 ^ 59
def prefixEnd_3194746 : Nat := 4983230072969 + 3 ^ 40 * 3194746 * 2
def baseEnd_3194746 : Nat := 1093626844685908516855091

theorem tailTrace_3194746 : CollatzResearch.WordTrace tailWord_3194746 prefixEnd_3194746 1093626844685908516855091 := by
  unfold tailWord_3194746
  simp only [CollatzResearch.WordTrace]
  refine ⟨29130489820997084005737023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77681306189325557348632061 29130489820997084005737023)
  ·
    refine ⟨43695734731495626008605535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29130489820997084005737023 43695734731495626008605535)
    ·
      refine ⟨65543602097243439012908303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43695734731495626008605535 65543602097243439012908303)
      ·
        refine ⟨98315403145865158519362455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65543602097243439012908303 98315403145865158519362455)
        ·
          refine ⟨147473104718797737779043683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98315403145865158519362455 147473104718797737779043683)
          ·
            refine ⟨221209657078196606668565525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147473104718797737779043683 221209657078196606668565525)
            ·
              refine ⟨10369202675540465937589009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 221209657078196606668565525 10369202675540465937589009)
              ·
                refine ⟨7776902006655349453191757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10369202675540465937589009 7776902006655349453191757)
                ·
                  refine ⟨2916338252495756044946909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7776902006655349453191757 2916338252495756044946909)
                  ·
                    refine ⟨1093626844685908516855091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2916338252495756044946909 1093626844685908516855091)
                    ·
                      rfl

theorem cell22_3194746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_3194746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194746 prefixEnd_3194746 := by exact prefixLift 3194746
  have htrace : WordTrace (prefixWord ++ tailWord_3194746) baseStart_3194746 baseEnd_3194746 := by
    simpa [prefixWord, tailWord_3194746, baseEnd_3194746] using wordTrace_append hprefix tailTrace_3194746
  have hstable : (prefixWord ++ tailWord_3194746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194746).length < 2 ^ (prefixWord ++ tailWord_3194746).sum := by decide
  have hdescent : baseEnd_3194746 < baseStart_3194746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194780 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 3, 3]
def baseStart_3194780 : Nat := 118140960795 + 3194780 * 2 ^ 59
def prefixEnd_3194780 : Nat := 4983230072969 + 3 ^ 40 * 3194780 * 2
def baseEnd_3194780 : Nat := 1093638483580743761504987

theorem tailTrace_3194780 : CollatzResearch.WordTrace tailWord_3194780 prefixEnd_3194780 1093638483580743761504987 := by
  unfold tailWord_3194780
  simp only [CollatzResearch.WordTrace]
  refine ⟨58261599682932579914842897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77682132910576773219790529 58261599682932579914842897)
  ·
    refine ⟨43696199762199434936132173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58261599682932579914842897 43696199762199434936132173)
    ·
      refine ⟨16386074910824788101049565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43696199762199434936132173 16386074910824788101049565)
      ·
        refine ⟨6144778091559295537893587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16386074910824788101049565 6144778091559295537893587)
        ·
          refine ⟨9217167137338943306840381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6144778091559295537893587 9217167137338943306840381)
          ·
            refine ⟨3456437676502103740065143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9217167137338943306840381 3456437676502103740065143)
            ·
              refine ⟨5184656514753155610097715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3456437676502103740065143 5184656514753155610097715)
              ·
                refine ⟨7776984772129733415146573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5184656514753155610097715 7776984772129733415146573)
                ·
                  refine ⟨2916369289548650030679965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7776984772129733415146573 2916369289548650030679965)
                  ·
                    refine ⟨1093638483580743761504987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2916369289548650030679965 1093638483580743761504987)
                    ·
                      rfl

theorem cell22_3194780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_3194780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194780 prefixEnd_3194780 := by exact prefixLift 3194780
  have htrace : WordTrace (prefixWord ++ tailWord_3194780) baseStart_3194780 baseEnd_3194780 := by
    simpa [prefixWord, tailWord_3194780, baseEnd_3194780] using wordTrace_append hprefix tailTrace_3194780
  have hstable : (prefixWord ++ tailWord_3194780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194780).length < 2 ^ (prefixWord ++ tailWord_3194780).sum := by decide
  have hdescent : baseEnd_3194780 < baseStart_3194780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194836 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3194836 : Nat := 118140960795 + 3194836 * 2 ^ 59
def prefixEnd_3194836 : Nat := 4983230072969 + 3 ^ 40 * 3194836 * 2
def baseEnd_3194836 : Nat := 1093657653525178282104815

theorem tailTrace_3194836 : CollatzResearch.WordTrace tailWord_3194836 prefixEnd_3194836 1093657653525178282104815 := by
  unfold tailWord_3194836
  simp only [CollatzResearch.WordTrace]
  refine ⟨58262620926831140696862181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77683494569108187595816241 58262620926831140696862181)
  ·
    refine ⟨10924241423780838880661659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58262620926831140696862181 10924241423780838880661659)
    ·
      refine ⟨16386362135671258320992489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10924241423780838880661659 16386362135671258320992489)
      ·
        refine ⟨12289771601753443740744367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16386362135671258320992489 12289771601753443740744367)
        ·
          refine ⟨18434657402630165611116551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12289771601753443740744367 18434657402630165611116551)
          ·
            refine ⟨27651986103945248416674827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18434657402630165611116551 27651986103945248416674827)
            ·
              refine ⟨41477979155917872625012241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27651986103945248416674827 41477979155917872625012241)
              ·
                refine ⟨31108484366938404468759181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41477979155917872625012241 31108484366938404468759181)
                ·
                  refine ⟨11665681637601901675784693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31108484366938404468759181 11665681637601901675784693)
                  ·
                    refine ⟨1093657653525178282104815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11665681637601901675784693 1093657653525178282104815)
                    ·
                      rfl

theorem cell22_3194836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3194836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194836 prefixEnd_3194836 := by exact prefixLift 3194836
  have htrace : WordTrace (prefixWord ++ tailWord_3194836) baseStart_3194836 baseEnd_3194836 := by
    simpa [prefixWord, tailWord_3194836, baseEnd_3194836] using wordTrace_append hprefix tailTrace_3194836
  have hstable : (prefixWord ++ tailWord_3194836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194836).length < 2 ^ (prefixWord ++ tailWord_3194836).sum := by decide
  have hdescent : baseEnd_3194836 < baseStart_3194836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194962 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 5]
def baseStart_3194962 : Nat := 118140960795 + 3194962 * 2 ^ 59
def prefixEnd_3194962 : Nat := 4983230072969 + 3 ^ 40 * 3194962 * 2
def baseEnd_3194962 : Nat := 364566928633385317818143

theorem tailTrace_3194962 : CollatzResearch.WordTrace tailWord_3194962 prefixEnd_3194962 364566928633385317818143 := by
  unfold tailWord_3194962
  simp only [CollatzResearch.WordTrace]
  refine ⟨29132459362801451228202785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77686558300803869941874093 29132459362801451228202785)
  ·
    refine ⟨21849344522101088421152089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29132459362801451228202785 21849344522101088421152089)
    ·
      refine ⟨16387008391575816315864067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21849344522101088421152089 16387008391575816315864067)
      ·
        refine ⟨24580512587363724473796101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16387008391575816315864067 24580512587363724473796101)
        ·
          refine ⟨4608846110130698338836769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24580512587363724473796101 4608846110130698338836769)
          ·
            refine ⟨3456634582598023754127577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4608846110130698338836769 3456634582598023754127577)
            ·
              refine ⟨2592475936948517815595683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3456634582598023754127577 2592475936948517815595683)
              ·
                refine ⟨3888713905422776723393525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2592475936948517815595683 3888713905422776723393525)
                ·
                  refine ⟨364566928633385317818143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3888713905422776723393525 364566928633385317818143)
                  ·
                    rfl

theorem cell22_3194962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_3194962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194962 prefixEnd_3194962 := by exact prefixLift 3194962
  have htrace : WordTrace (prefixWord ++ tailWord_3194962) baseStart_3194962 baseEnd_3194962 := by
    simpa [prefixWord, tailWord_3194962, baseEnd_3194962] using wordTrace_append hprefix tailTrace_3194962
  have hstable : (prefixWord ++ tailWord_3194962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194962).length < 2 ^ (prefixWord ++ tailWord_3194962).sum := by decide
  have hdescent : baseEnd_3194962 < baseStart_3194962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194988 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_3194988 : Nat := 118140960795 + 3194988 * 2 ^ 59
def prefixEnd_3194988 : Nat := 4983230072969 + 3 ^ 40 * 3194988 * 2
def baseEnd_3194988 : Nat := 1093709686231500552304349

theorem tailTrace_3194988 : CollatzResearch.WordTrace tailWord_3194988 prefixEnd_3194988 1093709686231500552304349 := by
  unfold tailWord_3194988
  simp only [CollatzResearch.WordTrace]
  refine ⟨58265392874555805676628809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77687190499407740902171745 58265392874555805676628809)
  ·
    refine ⟨43699044655916854257471607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58265392874555805676628809 43699044655916854257471607)
    ·
      refine ⟨65548566983875281386207411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43699044655916854257471607 65548566983875281386207411)
      ·
        refine ⟨98322850475812922079311117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65548566983875281386207411 98322850475812922079311117)
        ·
          refine ⟨36871068928429845779741669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98322850475812922079311117 36871068928429845779741669)
          ·
            refine ⟨6913325424080596083701563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36871068928429845779741669 6913325424080596083701563)
            ·
              refine ⟨10369988136120894125552345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6913325424080596083701563 10369988136120894125552345)
              ·
                refine ⟨7777491102090670594164259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10369988136120894125552345 7777491102090670594164259)
                ·
                  refine ⟨11666236653136005891246389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7777491102090670594164259 11666236653136005891246389)
                  ·
                    refine ⟨1093709686231500552304349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11666236653136005891246389 1093709686231500552304349)
                    ·
                      rfl

theorem cell22_3194988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_3194988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194988 prefixEnd_3194988 := by exact prefixLift 3194988
  have htrace : WordTrace (prefixWord ++ tailWord_3194988) baseStart_3194988 baseEnd_3194988 := by
    simpa [prefixWord, tailWord_3194988, baseEnd_3194988] using wordTrace_append hprefix tailTrace_3194988
  have hstable : (prefixWord ++ tailWord_3194988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194988).length < 2 ^ (prefixWord ++ tailWord_3194988).sum := by decide
  have hdescent : baseEnd_3194988 < baseStart_3194988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3194990 : List Nat := [4, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_3194990 : Nat := 118140960795 + 3194990 * 2 ^ 59
def prefixEnd_3194990 : Nat := 4983230072969 + 3 ^ 40 * 3194990 * 2
def baseEnd_3194990 : Nat := 364570123624124404584781

theorem tailTrace_3194990 : CollatzResearch.WordTrace tailWord_3194990 prefixEnd_3194990 364570123624124404584781 := by
  unfold tailWord_3194990
  simp only [CollatzResearch.WordTrace]
  refine ⟨14566357336888045711853803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77687239130069577129886949 14566357336888045711853803)
  ·
    refine ⟨21849536005332068567780705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14566357336888045711853803 21849536005332068567780705)
    ·
      refine ⟨16387152003999051425835529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21849536005332068567780705 16387152003999051425835529)
      ·
        refine ⟨12290364002999288569376647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16387152003999051425835529 12290364002999288569376647)
        ·
          refine ⟨18435546004498932854064971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12290364002999288569376647 18435546004498932854064971)
          ·
            refine ⟨27653319006748399281097457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18435546004498932854064971 27653319006748399281097457)
            ·
              refine ⟨20739989255061299460823093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27653319006748399281097457 20739989255061299460823093)
              ·
                refine ⟨1944373992661996824452165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20739989255061299460823093 1944373992661996824452165)
                ·
                  refine ⟨364570123624124404584781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1944373992661996824452165 364570123624124404584781)
                  ·
                    rfl

theorem cell22_3194990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_3194990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3194990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3194990 prefixEnd_3194990 := by exact prefixLift 3194990
  have htrace : WordTrace (prefixWord ++ tailWord_3194990) baseStart_3194990 baseEnd_3194990 := by
    simpa [prefixWord, tailWord_3194990, baseEnd_3194990] using wordTrace_append hprefix tailTrace_3194990
  have hstable : (prefixWord ++ tailWord_3194990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3194990).length < 2 ^ (prefixWord ++ tailWord_3194990).sum := by decide
  have hdescent : baseEnd_3194990 < baseStart_3194990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3194990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195001 : List Nat := [1, 2, 1, 3, 4, 11]
def baseStart_3195001 : Nat := 118140960795 + 3195001 * 2 ^ 59
def prefixEnd_3195001 : Nat := 4983230072969 + 3 ^ 40 * 3195001 * 2
def baseEnd_3195001 : Nat := 13502643659224356194189

theorem tailTrace_3195001 : CollatzResearch.WordTrace tailWord_3195001 prefixEnd_3195001 13502643659224356194189 := by
  unfold tailWord_3195001
  simp only [CollatzResearch.WordTrace]
  refine ⟨116531259898064514573480857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77687506598709676382320571 116531259898064514573480857)
  ·
    refine ⟨87398444923548385930110643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116531259898064514573480857 87398444923548385930110643)
    ·
      refine ⟨131097667385322578895165965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87398444923548385930110643 131097667385322578895165965)
      ·
        refine ⟨49161625269495967085687237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131097667385322578895165965 49161625269495967085687237)
        ·
          refine ⟨9217804738030493828566357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49161625269495967085687237 9217804738030493828566357)
          ·
            refine ⟨13502643659224356194189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9217804738030493828566357 13502643659224356194189)
            ·
              rfl

theorem cell22_3195001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 11].length) (baseStart_3195001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195001 prefixEnd_3195001 := by exact prefixLift 3195001
  have htrace : WordTrace (prefixWord ++ tailWord_3195001) baseStart_3195001 baseEnd_3195001 := by
    simpa [prefixWord, tailWord_3195001, baseEnd_3195001] using wordTrace_append hprefix tailTrace_3195001
  have hstable : (prefixWord ++ tailWord_3195001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195001).length < 2 ^ (prefixWord ++ tailWord_3195001).sum := by decide
  have hdescent : baseEnd_3195001 < baseStart_3195001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195005 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_3195005 : Nat := 118140960795 + 3195005 * 2 ^ 59
def prefixEnd_3195005 : Nat := 4983230072969 + 3 ^ 40 * 3195005 * 2
def baseEnd_3195005 : Nat := 1093715505678918174629297

theorem tailTrace_3195005 : CollatzResearch.WordTrace tailWord_3195005 prefixEnd_3195005 1093715505678918174629297 := by
  unfold tailWord_3195005
  simp only [CollatzResearch.WordTrace]
  refine ⟨116531405790050023256626469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77687603860033348837750979 116531405790050023256626469)
  ·
    refine ⟨21849638585634379360617463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116531405790050023256626469 21849638585634379360617463)
    ·
      refine ⟨32774457878451569040926195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21849638585634379360617463 32774457878451569040926195)
      ·
        refine ⟨49161686817677353561389293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32774457878451569040926195 49161686817677353561389293)
        ·
          refine ⟨18435632556629007585520985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49161686817677353561389293 18435632556629007585520985)
          ·
            refine ⟨13826724417471755689140739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18435632556629007585520985 13826724417471755689140739)
            ·
              refine ⟨20740086626207633533711109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13826724417471755689140739 20740086626207633533711109)
              ·
                refine ⟨3888766242413931287570833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20740086626207633533711109 3888766242413931287570833)
                ·
                  refine ⟨2916574681810448465678125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3888766242413931287570833 2916574681810448465678125)
                  ·
                    refine ⟨1093715505678918174629297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2916574681810448465678125 1093715505678918174629297)
                    ·
                      rfl

theorem cell22_3195005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_3195005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195005 prefixEnd_3195005 := by exact prefixLift 3195005
  have htrace : WordTrace (prefixWord ++ tailWord_3195005) baseStart_3195005 baseEnd_3195005 := by
    simpa [prefixWord, tailWord_3195005, baseEnd_3195005] using wordTrace_append hprefix tailTrace_3195005
  have hstable : (prefixWord ++ tailWord_3195005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195005).length < 2 ^ (prefixWord ++ tailWord_3195005).sum := by decide
  have hdescent : baseEnd_3195005 < baseStart_3195005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195018 : List Nat := [3, 1, 2, 3, 1, 2, 3, 7]
def baseStart_3195018 : Nat := 118140960795 + 3195018 * 2 ^ 59
def prefixEnd_3195018 : Nat := 4983230072969 + 3 ^ 40 * 3195018 * 2
def baseEnd_3195018 : Nat := 121524439538287830450473

theorem tailTrace_3195018 : CollatzResearch.WordTrace tailWord_3195018 prefixEnd_3195018 121524439538287830450473 := by
  unfold tailWord_3195018
  simp only [CollatzResearch.WordTrace]
  refine ⟨29132969984750731619212427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77687919959335284317899805 29132969984750731619212427)
  ·
    refine ⟨43699454977126097428818641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29132969984750731619212427 43699454977126097428818641)
    ·
      refine ⟨32774591232844573071613981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43699454977126097428818641 32774591232844573071613981)
      ·
        refine ⟨12290471712316714901855243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32774591232844573071613981 12290471712316714901855243)
        ·
          refine ⟨18435707568475072352782865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12290471712316714901855243 18435707568475072352782865)
          ·
            refine ⟨13826780676356304264587149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18435707568475072352782865 13826780676356304264587149)
            ·
              refine ⟨5185042753633614099220181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13826780676356304264587149 5185042753633614099220181)
              ·
                refine ⟨121524439538287830450473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5185042753633614099220181 121524439538287830450473)
                ·
                  rfl

theorem cell22_3195018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 7].length) (baseStart_3195018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195018 prefixEnd_3195018 := by exact prefixLift 3195018
  have htrace : WordTrace (prefixWord ++ tailWord_3195018) baseStart_3195018 baseEnd_3195018 := by
    simpa [prefixWord, tailWord_3195018, baseEnd_3195018] using wordTrace_append hprefix tailTrace_3195018
  have hstable : (prefixWord ++ tailWord_3195018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195018).length < 2 ^ (prefixWord ++ tailWord_3195018).sum := by decide
  have hdescent : baseEnd_3195018 < baseStart_3195018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195063 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 7]
def baseStart_3195063 : Nat := 118140960795 + 3195063 * 2 ^ 59
def prefixEnd_3195063 : Nat := 4983230072969 + 3 ^ 40 * 3195063 * 2
def baseEnd_3195063 : Nat := 364578453421408452226373

theorem tailTrace_3195063 : CollatzResearch.WordTrace tailWord_3195063 prefixEnd_3195063 364578453421408452226373 := by
  unfold tailWord_3195063
  simp only [CollatzResearch.WordTrace]
  refine ⟨116533521223839899162237843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77689014149226599441491895 116533521223839899162237843)
  ·
    refine ⟨174800281835759848743356765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116533521223839899162237843 174800281835759848743356765)
    ·
      refine ⟨65550105688409943278758787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174800281835759848743356765 65550105688409943278758787)
      ·
        refine ⟨98325158532614914918138181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65550105688409943278758787 98325158532614914918138181)
        ·
          refine ⟨18435967224865296547150909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98325158532614914918138181 18435967224865296547150909)
          ·
            refine ⟨6913487709324486205181591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18435967224865296547150909 6913487709324486205181591)
            ·
              refine ⟨10370231563986729307772387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6913487709324486205181591 10370231563986729307772387)
              ·
                refine ⟨15555347345980093961658581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10370231563986729307772387 15555347345980093961658581)
                ·
                  refine ⟨364578453421408452226373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15555347345980093961658581 364578453421408452226373)
                  ·
                    rfl

theorem cell22_3195063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 7].length) (baseStart_3195063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195063 prefixEnd_3195063 := by exact prefixLift 3195063
  have htrace : WordTrace (prefixWord ++ tailWord_3195063) baseStart_3195063 baseEnd_3195063 := by
    simpa [prefixWord, tailWord_3195063, baseEnd_3195063] using wordTrace_append hprefix tailTrace_3195063
  have hstable : (prefixWord ++ tailWord_3195063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195063).length < 2 ^ (prefixWord ++ tailWord_3195063).sum := by decide
  have hdescent : baseEnd_3195063 < baseStart_3195063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195101 : List Nat := [1, 4, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_3195101 : Nat := 118140960795 + 3195101 * 2 ^ 59
def prefixEnd_3195101 : Nat := 4983230072969 + 3 ^ 40 * 3195101 * 2
def baseEnd_3195101 : Nat := 1093748368440805924229003

theorem tailTrace_3195101 : CollatzResearch.WordTrace tailWord_3195101 prefixEnd_3195101 1093748368440805924229003 := by
  unfold tailWord_3195101
  simp only [CollatzResearch.WordTrace]
  refine ⟨116534907197702231652121157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77689938131801487768080771 116534907197702231652121157)
  ·
    refine ⟨21850295099569168434772717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116534907197702231652121157 21850295099569168434772717)
    ·
      refine ⟨8193860662338438163039769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21850295099569168434772717 8193860662338438163039769)
      ·
        refine ⟨6145395496753828622279827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8193860662338438163039769 6145395496753828622279827)
        ·
          refine ⟨9218093245130742933419741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145395496753828622279827 9218093245130742933419741)
          ·
            refine ⟨3456784966924028600032403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9218093245130742933419741 3456784966924028600032403)
            ·
              refine ⟨5185177450386042900048605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3456784966924028600032403 5185177450386042900048605)
              ·
                refine ⟨1944441543894766087518227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5185177450386042900048605 1944441543894766087518227)
                ·
                  refine ⟨2916662315842149131277341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944441543894766087518227 2916662315842149131277341)
                  ·
                    refine ⟨1093748368440805924229003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2916662315842149131277341 1093748368440805924229003)
                    ·
                      rfl

theorem cell22_3195101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_3195101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195101 prefixEnd_3195101 := by exact prefixLift 3195101
  have htrace : WordTrace (prefixWord ++ tailWord_3195101) baseStart_3195101 baseEnd_3195101 := by
    simpa [prefixWord, tailWord_3195101, baseEnd_3195101] using wordTrace_append hprefix tailTrace_3195101
  have hstable : (prefixWord ++ tailWord_3195101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195101).length < 2 ^ (prefixWord ++ tailWord_3195101).sum := by decide
  have hdescent : baseEnd_3195101 < baseStart_3195101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195153 : List Nat := [1, 2, 2, 1, 1, 5, 2, 8]
def baseStart_3195153 : Nat := 118140960795 + 3195153 * 2 ^ 59
def prefixEnd_3195153 : Nat := 4983230072969 + 3 ^ 40 * 3195153 * 2
def baseEnd_3195153 : Nat := 121529574344832791325427

theorem tailTrace_3195153 : CollatzResearch.WordTrace tailWord_3195153 prefixEnd_3195153 121529574344832791325427 := by
  unfold tailWord_3195153
  simp only [CollatzResearch.WordTrace]
  refine ⟨116536803793513844533014113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77691202529009229688676075 116536803793513844533014113)
  ·
    refine ⟨87402602845135383399760585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116536803793513844533014113 87402602845135383399760585)
    ·
      refine ⟨65551952133851537549820439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87402602845135383399760585 65551952133851537549820439)
      ·
        refine ⟨98327928200777306324730659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65551952133851537549820439 98327928200777306324730659)
        ·
          refine ⟨147491892301165959487095989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98327928200777306324730659 147491892301165959487095989)
          ·
            refine ⟨13827364903234308701915249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 147491892301165959487095989 13827364903234308701915249)
            ·
              refine ⟨10370523677425731526436437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13827364903234308701915249 10370523677425731526436437)
              ·
                refine ⟨121529574344832791325427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10370523677425731526436437 121529574344832791325427)
                ·
                  rfl

theorem cell22_3195153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 8].length) (baseStart_3195153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195153 prefixEnd_3195153 := by exact prefixLift 3195153
  have htrace : WordTrace (prefixWord ++ tailWord_3195153) baseStart_3195153 baseEnd_3195153 := by
    simpa [prefixWord, tailWord_3195153, baseEnd_3195153] using wordTrace_append hprefix tailTrace_3195153
  have hstable : (prefixWord ++ tailWord_3195153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195153).length < 2 ^ (prefixWord ++ tailWord_3195153).sum := by decide
  have hdescent : baseEnd_3195153 < baseStart_3195153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195176 : List Nat := [2, 1, 5, 1, 3, 2, 2, 2, 4]
def baseStart_3195176 : Nat := 118140960795 + 3195176 * 2 ^ 59
def prefixEnd_3195176 : Nat := 4983230072969 + 3 ^ 40 * 3195176 * 2
def baseEnd_3195176 : Nat := 364591347491176909534591

theorem tailTrace_3195176 : CollatzResearch.WordTrace tailWord_3195176 prefixEnd_3195176 364591347491176909534591 := by
  unfold tailWord_3195176
  simp only [CollatzResearch.WordTrace]
  refine ⟨58268821336215259730550691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77691761781620346307400921 58268821336215259730550691)
  ·
    refine ⟨87403232004322889595826037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58268821336215259730550691 87403232004322889595826037)
    ·
      refine ⟨8194053000405270899608691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87403232004322889595826037 8194053000405270899608691)
      ·
        refine ⟨12291079500607906349413037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8194053000405270899608691 12291079500607906349413037)
        ·
          refine ⟨4609154812727964881029889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12291079500607906349413037 4609154812727964881029889)
          ·
            refine ⟨3456866109545973660772417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4609154812727964881029889 3456866109545973660772417)
            ·
              refine ⟨2592649582159480245579313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3456866109545973660772417 2592649582159480245579313)
              ·
                refine ⟨1944487186619610184184485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2592649582159480245579313 1944487186619610184184485)
                ·
                  refine ⟨364591347491176909534591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1944487186619610184184485 364591347491176909534591)
                  ·
                    rfl

theorem cell22_3195176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 4].length) (baseStart_3195176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195176 prefixEnd_3195176 := by exact prefixLift 3195176
  have htrace : WordTrace (prefixWord ++ tailWord_3195176) baseStart_3195176 baseEnd_3195176 := by
    simpa [prefixWord, tailWord_3195176, baseEnd_3195176] using wordTrace_append hprefix tailTrace_3195176
  have hstable : (prefixWord ++ tailWord_3195176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195176).length < 2 ^ (prefixWord ++ tailWord_3195176).sum := by decide
  have hdescent : baseEnd_3195176 < baseStart_3195176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195183 : List Nat := [1, 1, 2, 1, 2, 1, 5, 1, 2, 6]
def baseStart_3195183 : Nat := 118140960795 + 3195183 * 2 ^ 59
def prefixEnd_3195183 : Nat := 4983230072969 + 3 ^ 40 * 3195183 * 2
def baseEnd_3195183 : Nat := 1093776438716585043678751

theorem tailTrace_3195183 : CollatzResearch.WordTrace tailWord_3195183 prefixEnd_3195183 1093776438716585043678751 := by
  unfold tailWord_3195183
  simp only [CollatzResearch.WordTrace]
  refine ⟨116537897983405159656606203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77691931988936773104404135 116537897983405159656606203)
  ·
    refine ⟨174806846975107739484909305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116537897983405159656606203 174806846975107739484909305)
    ·
      refine ⟨131105135231330804613681979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174806846975107739484909305 131105135231330804613681979)
      ·
        refine ⟨196657702846996206920522969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131105135231330804613681979 196657702846996206920522969)
        ·
          refine ⟨147493277135247155190392227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196657702846996206920522969 147493277135247155190392227)
          ·
            refine ⟨221239915702870732785588341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147493277135247155190392227 221239915702870732785588341)
            ·
              refine ⟨20741242097144131198648907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221239915702870732785588341 20741242097144131198648907)
              ·
                refine ⟨31111863145716196797973361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20741242097144131198648907 31111863145716196797973361)
                ·
                  refine ⟨23333897359287147598480021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31111863145716196797973361 23333897359287147598480021)
                  ·
                    refine ⟨1093776438716585043678751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23333897359287147598480021 1093776438716585043678751)
                    ·
                      rfl

theorem cell22_3195183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_3195183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195183 prefixEnd_3195183 := by exact prefixLift 3195183
  have htrace : WordTrace (prefixWord ++ tailWord_3195183) baseStart_3195183 baseEnd_3195183 := by
    simpa [prefixWord, tailWord_3195183, baseEnd_3195183] using wordTrace_append hprefix tailTrace_3195183
  have hstable : (prefixWord ++ tailWord_3195183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195183).length < 2 ^ (prefixWord ++ tailWord_3195183).sum := by decide
  have hdescent : baseEnd_3195183 < baseStart_3195183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195204 : List Nat := [2, 3, 4, 1, 2, 1, 3, 6]
def baseStart_3195204 : Nat := 118140960795 + 3195204 * 2 ^ 59
def prefixEnd_3195204 : Nat := 4983230072969 + 3 ^ 40 * 3195204 * 2
def baseEnd_3195204 : Nat := 121531514160638665433743

theorem tailTrace_3195204 : CollatzResearch.WordTrace tailWord_3195204 prefixEnd_3195204 121531514160638665433743 := by
  unfold tailWord_3195204
  simp only [CollatzResearch.WordTrace]
  refine ⟨58269331958164540121560333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77692442610886053495413777 58269331958164540121560333)
  ·
    refine ⟨21850999484311702545585125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58269331958164540121560333 21850999484311702545585125)
    ·
      refine ⟨4097062403308444227297211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21850999484311702545585125 4097062403308444227297211)
      ·
        refine ⟨6145593604962666340945817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4097062403308444227297211 6145593604962666340945817)
        ·
          refine ⟨4609195203721999755709363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6145593604962666340945817 4609195203721999755709363)
          ·
            refine ⟨6913792805582999633564045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609195203721999755709363 6913792805582999633564045)
            ·
              refine ⟨2592672302093624862586517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6913792805582999633564045 2592672302093624862586517)
              ·
                refine ⟨121531514160638665433743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2592672302093624862586517 121531514160638665433743)
                ·
                  rfl

theorem cell22_3195204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 6].length) (baseStart_3195204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195204 prefixEnd_3195204 := by exact prefixLift 3195204
  have htrace : WordTrace (prefixWord ++ tailWord_3195204) baseStart_3195204 baseEnd_3195204 := by
    simpa [prefixWord, tailWord_3195204, baseEnd_3195204] using wordTrace_append hprefix tailTrace_3195204
  have hstable : (prefixWord ++ tailWord_3195204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195204).length < 2 ^ (prefixWord ++ tailWord_3195204).sum := by decide
  have hdescent : baseEnd_3195204 < baseStart_3195204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195243 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 10]
def baseStart_3195243 : Nat := 118140960795 + 3195243 * 2 ^ 59
def prefixEnd_3195243 : Nat := 4983230072969 + 3 ^ 40 * 3195243 * 2
def baseEnd_3195243 : Nat := 364598992647588295726189

theorem tailTrace_3195243 : CollatzResearch.WordTrace tailWord_3195243 prefixEnd_3195243 364598992647588295726189 := by
  unfold tailWord_3195243
  simp only [CollatzResearch.WordTrace]
  refine ⟨116540086363187789903790383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77693390908791859935860255 116540086363187789903790383)
  ·
    refine ⟨174810129544781684855685575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116540086363187789903790383 174810129544781684855685575)
    ·
      refine ⟨262215194317172527283528363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174810129544781684855685575 262215194317172527283528363)
      ·
        refine ⟨393322791475758790925292545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262215194317172527283528363 393322791475758790925292545)
        ·
          refine ⟨294992093606819093193969409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393322791475758790925292545 294992093606819093193969409)
          ·
            refine ⟨221244070205114319895477057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294992093606819093193969409 221244070205114319895477057)
            ·
              refine ⟨165933052653835739921607793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221244070205114319895477057 165933052653835739921607793)
              ·
                refine ⟨124449789490376804941205845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165933052653835739921607793 124449789490376804941205845)
                ·
                  refine ⟨364598992647588295726189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 124449789490376804941205845 364598992647588295726189)
                  ·
                    rfl

theorem cell22_3195243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 10].length) (baseStart_3195243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195243 prefixEnd_3195243 := by exact prefixLift 3195243
  have htrace : WordTrace (prefixWord ++ tailWord_3195243) baseStart_3195243 baseEnd_3195243 := by
    simpa [prefixWord, tailWord_3195243, baseEnd_3195243] using wordTrace_append hprefix tailTrace_3195243
  have hstable : (prefixWord ++ tailWord_3195243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195243).length < 2 ^ (prefixWord ++ tailWord_3195243).sum := by decide
  have hdescent : baseEnd_3195243 < baseStart_3195243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195294 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_3195294 : Nat := 118140960795 + 3195294 * 2 ^ 59
def prefixEnd_3195294 : Nat := 4983230072969 + 3 ^ 40 * 3195294 * 2
def baseEnd_3195294 : Nat := 364604812095005918051137

theorem tailTrace_3195294 : CollatzResearch.WordTrace tailWord_3195294 prefixEnd_3195294 364604812095005918051137 := by
  unfold tailWord_3195294
  simp only [CollatzResearch.WordTrace]
  refine ⟨14567743310750378201737117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77694630990668683742597957 14567743310750378201737117)
  ·
    refine ⟨5462903741531391825651419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14567743310750378201737117 5462903741531391825651419)
    ·
      refine ⟨8194355612297087738477129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5462903741531391825651419 8194355612297087738477129)
      ·
        refine ⟨6145766709222815803857847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8194355612297087738477129 6145766709222815803857847)
        ·
          refine ⟨9218650063834223705786771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145766709222815803857847 9218650063834223705786771)
          ·
            refine ⟨13827975095751335558680157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218650063834223705786771 13827975095751335558680157)
            ·
              refine ⟨5185490660906750834505059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13827975095751335558680157 5185490660906750834505059)
              ·
                refine ⟨7778235991360126251757589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5185490660906750834505059 7778235991360126251757589)
                ·
                  refine ⟨364604812095005918051137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7778235991360126251757589 364604812095005918051137)
                  ·
                    rfl

theorem cell22_3195294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_3195294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195294 prefixEnd_3195294 := by exact prefixLift 3195294
  have htrace : WordTrace (prefixWord ++ tailWord_3195294) baseStart_3195294 baseEnd_3195294 := by
    simpa [prefixWord, tailWord_3195294, baseEnd_3195294] using wordTrace_append hprefix tailTrace_3195294
  have hstable : (prefixWord ++ tailWord_3195294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195294).length < 2 ^ (prefixWord ++ tailWord_3195294).sum := by decide
  have hdescent : baseEnd_3195294 < baseStart_3195294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195324 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_3195324 : Nat := 118140960795 + 3195324 * 2 ^ 59
def prefixEnd_3195324 : Nat := 4983230072969 + 3 ^ 40 * 3195324 * 2
def baseEnd_3195324 : Nat := 1093824705898107675903319

theorem tailTrace_3195324 : CollatzResearch.WordTrace tailWord_3195324 prefixEnd_3195324 1093824705898107675903319 := by
  unfold tailWord_3195324
  simp only [CollatzResearch.WordTrace]
  refine ⟨58271520337947170368744513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77695360450596227158326017 58271520337947170368744513)
  ·
    refine ⟨43703640253460377776558385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58271520337947170368744513 43703640253460377776558385)
    ·
      refine ⟨32777730190095283332418789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43703640253460377776558385 32777730190095283332418789)
      ·
        refine ⟨6145824410642865624828523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32777730190095283332418789 6145824410642865624828523)
        ·
          refine ⟨9218736615964298437242785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145824410642865624828523 9218736615964298437242785)
          ·
            refine ⟨6914052461973223827932089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9218736615964298437242785 6914052461973223827932089)
            ·
              refine ⟨5185539346479917870949067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6914052461973223827932089 5185539346479917870949067)
              ·
                refine ⟨7778309019719876806423601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5185539346479917870949067 7778309019719876806423601)
                ·
                  refine ⟨5833731764789907604817701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7778309019719876806423601 5833731764789907604817701)
                  ·
                    refine ⟨1093824705898107675903319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5833731764789907604817701 1093824705898107675903319)
                    ·
                      rfl

theorem cell22_3195324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_3195324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195324 prefixEnd_3195324 := by exact prefixLift 3195324
  have htrace : WordTrace (prefixWord ++ tailWord_3195324) baseStart_3195324 baseEnd_3195324 := by
    simpa [prefixWord, tailWord_3195324, baseEnd_3195324] using wordTrace_append hprefix tailTrace_3195324
  have hstable : (prefixWord ++ tailWord_3195324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195324).length < 2 ^ (prefixWord ++ tailWord_3195324).sum := by decide
  have hdescent : baseEnd_3195324 < baseStart_3195324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195367 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 5]
def baseStart_3195367 : Nat := 118140960795 + 3195367 * 2 ^ 59
def prefixEnd_3195367 : Nat := 4983230072969 + 3 ^ 40 * 3195367 * 2
def baseEnd_3195367 : Nat := 364613141892289965692729

theorem tailTrace_3195367 : CollatzResearch.WordTrace tailWord_3195367 prefixEnd_3195367 364613141892289965692729 := by
  unfold tailWord_3195367
  simp only [CollatzResearch.WordTrace]
  refine ⟨116544609014738559081304355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77696406009825706054202903 116544609014738559081304355)
  ·
    refine ⟨174816913522107838621956533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116544609014738559081304355 174816913522107838621956533)
    ·
      refine ⟨16389085642697609870808425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174816913522107838621956533 16389085642697609870808425)
      ·
        refine ⟨12291814232023207403106319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16389085642697609870808425 12291814232023207403106319)
        ·
          refine ⟨18437721348034811104659479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12291814232023207403106319 18437721348034811104659479)
          ·
            refine ⟨27656582022052216656989219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18437721348034811104659479 27656582022052216656989219)
            ·
              refine ⟨41484873033078324985483829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27656582022052216656989219 41484873033078324985483829)
              ·
                refine ⟨3889206846851092967389109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41484873033078324985483829 3889206846851092967389109)
                ·
                  refine ⟨364613141892289965692729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3889206846851092967389109 364613141892289965692729)
                  ·
                    rfl

theorem cell22_3195367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 5].length) (baseStart_3195367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195367 prefixEnd_3195367 := by exact prefixLift 3195367
  have htrace : WordTrace (prefixWord ++ tailWord_3195367) baseStart_3195367 baseEnd_3195367 := by
    simpa [prefixWord, tailWord_3195367, baseEnd_3195367] using wordTrace_append hprefix tailTrace_3195367
  have hstable : (prefixWord ++ tailWord_3195367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195367).length < 2 ^ (prefixWord ++ tailWord_3195367).sum := by decide
  have hdescent : baseEnd_3195367 < baseStart_3195367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195382 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_3195382 : Nat := 118140960795 + 3195382 * 2 ^ 59
def prefixEnd_3195382 : Nat := 4983230072969 + 3 ^ 40 * 3195382 * 2
def baseEnd_3195382 : Nat := 1093844560483414857953141

theorem tailTrace_3195382 : CollatzResearch.WordTrace tailWord_3195382 prefixEnd_3195382 1093844560483414857953141 := by
  unfold tailWord_3195382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7284072256855263540193775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77696770739789477762066933 7284072256855263540193775)
  ·
    refine ⟨10926108385282895310290663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7284072256855263540193775 10926108385282895310290663)
    ·
      refine ⟨16389162577924342965435995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10926108385282895310290663 16389162577924342965435995)
      ·
        refine ⟨24583743866886514448153993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16389162577924342965435995 24583743866886514448153993)
        ·
          refine ⟨18437807900164885836115495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24583743866886514448153993 18437807900164885836115495)
          ·
            refine ⟨27656711850247328754173243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18437807900164885836115495 27656711850247328754173243)
            ·
              refine ⟨41485067775370993131259865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27656711850247328754173243 41485067775370993131259865)
              ·
                refine ⟨31113800831528244848444899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41485067775370993131259865 31113800831528244848444899)
                ·
                  refine ⟨46670701247292367272667349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31113800831528244848444899 46670701247292367272667349)
                  ·
                    refine ⟨1093844560483414857953141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46670701247292367272667349 1093844560483414857953141)
                    ·
                      rfl

theorem cell22_3195382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_3195382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195382 prefixEnd_3195382 := by exact prefixLift 3195382
  have htrace : WordTrace (prefixWord ++ tailWord_3195382) baseStart_3195382 baseEnd_3195382 := by
    simpa [prefixWord, tailWord_3195382, baseEnd_3195382] using wordTrace_append hprefix tailTrace_3195382
  have hstable : (prefixWord ++ tailWord_3195382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195382).length < 2 ^ (prefixWord ++ tailWord_3195382).sum := by decide
  have hdescent : baseEnd_3195382 < baseStart_3195382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195395 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 8]
def baseStart_3195395 : Nat := 118140960795 + 3195395 * 2 ^ 59
def prefixEnd_3195395 : Nat := 4983230072969 + 3 ^ 40 * 3195395 * 2
def baseEnd_3195395 : Nat := 364616336883029052459367

theorem tailTrace_3195395 : CollatzResearch.WordTrace tailWord_3195395 prefixEnd_3195395 364616336883029052459367 := by
  unfold tailWord_3195395
  simp only [CollatzResearch.WordTrace]
  refine ⟨116545630258637119863323639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77697086839091413242215759 116545630258637119863323639)
  ·
    refine ⟨174818445387955679794985459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116545630258637119863323639 174818445387955679794985459)
    ·
      refine ⟨262227668081933519692478189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174818445387955679794985459 262227668081933519692478189)
      ·
        refine ⟨98335375530725069884679321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262227668081933519692478189 98335375530725069884679321)
        ·
          refine ⟨73751531648043802413509491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98335375530725069884679321 73751531648043802413509491)
          ·
            refine ⟨110627297472065703620264237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73751531648043802413509491 110627297472065703620264237)
            ·
              refine ⟨41485236552024638857599089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110627297472065703620264237 41485236552024638857599089)
              ·
                refine ⟨31113927414018479143199317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41485236552024638857599089 31113927414018479143199317)
                ·
                  refine ⟨364616336883029052459367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31113927414018479143199317 364616336883029052459367)
                  ·
                    rfl

theorem cell22_3195395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 8].length) (baseStart_3195395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195395 prefixEnd_3195395 := by exact prefixLift 3195395
  have htrace : WordTrace (prefixWord ++ tailWord_3195395) baseStart_3195395 baseEnd_3195395 := by
    simpa [prefixWord, tailWord_3195395, baseEnd_3195395] using wordTrace_append hprefix tailTrace_3195395
  have hstable : (prefixWord ++ tailWord_3195395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195395).length < 2 ^ (prefixWord ++ tailWord_3195395).sum := by decide
  have hdescent : baseEnd_3195395 < baseStart_3195395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195405 : List Nat := [1, 7, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3195405 : Nat := 118140960795 + 3195405 * 2 ^ 59
def prefixEnd_3195405 : Nat := 4983230072969 + 3 ^ 40 * 3195405 * 2
def baseEnd_3195405 : Nat := 1093852433853450464628071

theorem tailTrace_3195405 : CollatzResearch.WordTrace tailWord_3195405 prefixEnd_3195405 1093852433853450464628071 := by
  unfold tailWord_3195405
  simp only [CollatzResearch.WordTrace]
  refine ⟨116545994988600891571187669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77697329992400594380791779 116545994988600891571187669)
  ·
    refine ⟨2731546757545333396199711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 116545994988600891571187669 2731546757545333396199711)
    ·
      refine ⟨4097320136318000094299567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2731546757545333396199711 4097320136318000094299567)
      ·
        refine ⟨6145980204477000141449351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4097320136318000094299567 6145980204477000141449351)
        ·
          refine ⟨9218970306715500212174027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6145980204477000141449351 9218970306715500212174027)
          ·
            refine ⟨13828455460073250318261041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218970306715500212174027 13828455460073250318261041)
            ·
              refine ⟨10371341595054937738695781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13828455460073250318261041 10371341595054937738695781)
              ·
                refine ⟨1944626549072800826005459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10371341595054937738695781 1944626549072800826005459)
                ·
                  refine ⟨2916939823609201239008189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944626549072800826005459 2916939823609201239008189)
                  ·
                    refine ⟨1093852433853450464628071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2916939823609201239008189 1093852433853450464628071)
                    ·
                      rfl

theorem cell22_3195405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3195405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195405 prefixEnd_3195405 := by exact prefixLift 3195405
  have htrace : WordTrace (prefixWord ++ tailWord_3195405) baseStart_3195405 baseEnd_3195405 := by
    simpa [prefixWord, tailWord_3195405, baseEnd_3195405] using wordTrace_append hprefix tailTrace_3195405
  have hstable : (prefixWord ++ tailWord_3195405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195405).length < 2 ^ (prefixWord ++ tailWord_3195405).sum := by decide
  have hdescent : baseEnd_3195405 < baseStart_3195405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195442 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_3195442 : Nat := 118140960795 + 3195442 * 2 ^ 59
def prefixEnd_3195442 : Nat := 4983230072969 + 3 ^ 40 * 3195442 * 2
def baseEnd_3195442 : Nat := 1093865099709594701452957

theorem tailTrace_3195442 : CollatzResearch.WordTrace tailWord_3195442 prefixEnd_3195442 1093865099709594701452957 := by
  unfold tailWord_3195442
  simp only [CollatzResearch.WordTrace]
  refine ⟨29136836122366711722571145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77698229659644564593523053 29136836122366711722571145)
  ·
    refine ⟨21852627091775033791928359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29136836122366711722571145 21852627091775033791928359)
    ·
      refine ⟨32778940637662550687892539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21852627091775033791928359 32778940637662550687892539)
      ·
        refine ⟨49168410956493826031838809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32778940637662550687892539 49168410956493826031838809)
        ·
          refine ⟨36876308217370369523879107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49168410956493826031838809 36876308217370369523879107)
          ·
            refine ⟨55314462326055554285818661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36876308217370369523879107 55314462326055554285818661)
            ·
              refine ⟨10371461686135416428590999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55314462326055554285818661 10371461686135416428590999)
              ·
                refine ⟨15557192529203124642886499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10371461686135416428590999 15557192529203124642886499)
                ·
                  refine ⟨23335788793804686964329749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15557192529203124642886499 23335788793804686964329749)
                  ·
                    refine ⟨1093865099709594701452957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23335788793804686964329749 1093865099709594701452957)
                    ·
                      rfl

theorem cell22_3195442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_3195442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195442 prefixEnd_3195442 := by exact prefixLift 3195442
  have htrace : WordTrace (prefixWord ++ tailWord_3195442) baseStart_3195442 baseEnd_3195442 := by
    simpa [prefixWord, tailWord_3195442, baseEnd_3195442] using wordTrace_append hprefix tailTrace_3195442
  have hstable : (prefixWord ++ tailWord_3195442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195442).length < 2 ^ (prefixWord ++ tailWord_3195442).sum := by decide
  have hdescent : baseEnd_3195442 < baseStart_3195442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195457 : List Nat := [1, 2, 5, 1, 1, 2, 10]
def baseStart_3195457 : Nat := 118140960795 + 3195457 * 2 ^ 59
def prefixEnd_3195457 : Nat := 4983230072969 + 3 ^ 40 * 3195457 * 2
def baseEnd_3195457 : Nat := 40513712389486654160293

theorem tailTrace_3195457 : CollatzResearch.WordTrace tailWord_3195457 prefixEnd_3195457 40513712389486654160293 := by
  unfold tailWord_3195457
  simp only [CollatzResearch.WordTrace]
  refine ⟨116547891584412504452080625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77698594389608336301387083 116547891584412504452080625)
  ·
    refine ⟨87410918688309378339060469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116547891584412504452080625 87410918688309378339060469)
    ·
      refine ⟨8194773627029004219286919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87410918688309378339060469 8194773627029004219286919)
      ·
        refine ⟨12292160440543506328930379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8194773627029004219286919 12292160440543506328930379)
        ·
          refine ⟨18438240660815259493395569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12292160440543506328930379 18438240660815259493395569)
          ·
            refine ⟨13828680495611444620046677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18438240660815259493395569 13828680495611444620046677)
            ·
              refine ⟨40513712389486654160293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13828680495611444620046677 40513712389486654160293)
              ·
                rfl

theorem cell22_3195457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 10].length) (baseStart_3195457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195457 prefixEnd_3195457 := by exact prefixLift 3195457
  have htrace : WordTrace (prefixWord ++ tailWord_3195457) baseStart_3195457 baseEnd_3195457 := by
    simpa [prefixWord, tailWord_3195457, baseEnd_3195457] using wordTrace_append hprefix tailTrace_3195457
  have hstable : (prefixWord ++ tailWord_3195457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195457).length < 2 ^ (prefixWord ++ tailWord_3195457).sum := by decide
  have hdescent : baseEnd_3195457 < baseStart_3195457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195523 : List Nat := [1, 1, 1, 3, 3, 1, 6, 2, 1, 3]
def baseStart_3195523 : Nat := 118140960795 + 3195523 * 2 ^ 59
def prefixEnd_3195523 : Nat := 4983230072969 + 3 ^ 40 * 3195523 * 2
def baseEnd_3195523 : Nat := 1093892827664937490177709

theorem tailTrace_3195523 : CollatzResearch.WordTrace tailWord_3195523 prefixEnd_3195523 1093892827664937490177709 := by
  unfold tailWord_3195523
  simp only [CollatzResearch.WordTrace]
  refine ⟨116550298802173397723983223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77700199201448931815988815 116550298802173397723983223)
  ·
    refine ⟨174825448203260096585974835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116550298802173397723983223 174825448203260096585974835)
    ·
      refine ⟨262238172304890144878962253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174825448203260096585974835 262238172304890144878962253)
      ·
        refine ⟨98339314614333804329610845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 262238172304890144878962253 98339314614333804329610845)
        ·
          refine ⟨36877242980375176623604067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98339314614333804329610845 36877242980375176623604067)
          ·
            refine ⟨55315864470562764935406101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36877242980375176623604067 55315864470562764935406101)
            ·
              refine ⟨2592931147057629606347161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55315864470562764935406101 2592931147057629606347161)
              ·
                refine ⟨1944698360293222204760371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2592931147057629606347161 1944698360293222204760371)
                ·
                  refine ⟨2917047540439833307140557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944698360293222204760371 2917047540439833307140557)
                  ·
                    refine ⟨1093892827664937490177709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917047540439833307140557 1093892827664937490177709)
                    ·
                      rfl

theorem cell22_3195523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 1, 3].length) (baseStart_3195523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195523 prefixEnd_3195523 := by exact prefixLift 3195523
  have htrace : WordTrace (prefixWord ++ tailWord_3195523) baseStart_3195523 baseEnd_3195523 := by
    simpa [prefixWord, tailWord_3195523, baseEnd_3195523] using wordTrace_append hprefix tailTrace_3195523
  have hstable : (prefixWord ++ tailWord_3195523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195523).length < 2 ^ (prefixWord ++ tailWord_3195523).sum := by decide
  have hdescent : baseEnd_3195523 < baseStart_3195523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195534 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_3195534 : Nat := 118140960795 + 3195534 * 2 ^ 59
def prefixEnd_3195534 : Nat := 4983230072969 + 3 ^ 40 * 3195534 * 2
def baseEnd_3195534 : Nat := 1093896593189737128152675

theorem tailTrace_3195534 : CollatzResearch.WordTrace tailWord_3195534 prefixEnd_3195534 1093896593189737128152675 := by
  unfold tailWord_3195534
  simp only [CollatzResearch.WordTrace]
  refine ⟨14568837500641693325329207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77700466670089031068422437 14568837500641693325329207)
  ·
    refine ⟨21853256250962539987993811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14568837500641693325329207 21853256250962539987993811)
    ·
      refine ⟨32779884376443809981990717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21853256250962539987993811 32779884376443809981990717)
      ·
        refine ⟨12292456641166428743246519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32779884376443809981990717 12292456641166428743246519)
        ·
          refine ⟨18438684961749643114869779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12292456641166428743246519 18438684961749643114869779)
          ·
            refine ⟨27658027442624464672304669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18438684961749643114869779 27658027442624464672304669)
            ·
              refine ⟨10371760290984174252114251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27658027442624464672304669 10371760290984174252114251)
              ·
                refine ⟨15557640436476261378171377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10371760290984174252114251 15557640436476261378171377)
                ·
                  refine ⟨11668230327357196033628533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15557640436476261378171377 11668230327357196033628533)
                  ·
                    refine ⟨1093896593189737128152675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11668230327357196033628533 1093896593189737128152675)
                    ·
                      rfl

theorem cell22_3195534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_3195534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195534 prefixEnd_3195534 := by exact prefixLift 3195534
  have htrace : WordTrace (prefixWord ++ tailWord_3195534) baseStart_3195534 baseEnd_3195534 := by
    simpa [prefixWord, tailWord_3195534, baseEnd_3195534] using wordTrace_append hprefix tailTrace_3195534
  have hstable : (prefixWord ++ tailWord_3195534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195534).length < 2 ^ (prefixWord ++ tailWord_3195534).sum := by decide
  have hdescent : baseEnd_3195534 < baseStart_3195534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195549 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_3195549 : Nat := 118140960795 + 3195549 * 2 ^ 59
def prefixEnd_3195549 : Nat := 4983230072969 + 3 ^ 40 * 3195549 * 2
def baseEnd_3195549 : Nat := 1093901727996282089027629

theorem tailTrace_3195549 : CollatzResearch.WordTrace tailWord_3195549 prefixEnd_3195549 1093901727996282089027629 := by
  unfold tailWord_3195549
  simp only [CollatzResearch.WordTrace]
  refine ⟨116551247100079204164429701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77700831400052802776286467 116551247100079204164429701)
  ·
    refine ⟨21853358831264850780830569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116551247100079204164429701 21853358831264850780830569)
    ·
      refine ⟨16390019123448638085622927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21853358831264850780830569 16390019123448638085622927)
      ·
        refine ⟨24585028685172957128434391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16390019123448638085622927 24585028685172957128434391)
        ·
          refine ⟨36877543027759435692651587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24585028685172957128434391 36877543027759435692651587)
          ·
            refine ⟨55316314541639153538977381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36877543027759435692651587 55316314541639153538977381)
            ·
              refine ⟨10371808976557341288558259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55316314541639153538977381 10371808976557341288558259)
              ·
                refine ⟨15557713464836011932837389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10371808976557341288558259 15557713464836011932837389)
                ·
                  refine ⟨5834142549313504474814021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15557713464836011932837389 5834142549313504474814021)
                  ·
                    refine ⟨1093901727996282089027629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5834142549313504474814021 1093901727996282089027629)
                    ·
                      rfl

theorem cell22_3195549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_3195549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195549 prefixEnd_3195549 := by exact prefixLift 3195549
  have htrace : WordTrace (prefixWord ++ tailWord_3195549) baseStart_3195549 baseEnd_3195549 := by
    simpa [prefixWord, tailWord_3195549, baseEnd_3195549] using wordTrace_append hprefix tailTrace_3195549
  have hstable : (prefixWord ++ tailWord_3195549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195549).length < 2 ^ (prefixWord ++ tailWord_3195549).sum := by decide
  have hdescent : baseEnd_3195549 < baseStart_3195549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195581 : List Nat := [1, 4, 1, 2, 1, 3, 2, 4, 4]
def baseStart_3195581 : Nat := 118140960795 + 3195581 * 2 ^ 59
def prefixEnd_3195581 : Nat := 4983230072969 + 3 ^ 40 * 3195581 * 2
def baseEnd_3195581 : Nat := 364637560750081557409177

theorem tailTrace_3195581 : CollatzResearch.WordTrace tailWord_3195581 prefixEnd_3195581 364637560750081557409177 := by
  unfold tailWord_3195581
  simp only [CollatzResearch.WordTrace]
  refine ⟨116552414235963273629594597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77701609490642182419729731 116552414235963273629594597)
  ·
    refine ⟨21853577669243113805548987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116552414235963273629594597 21853577669243113805548987)
    ·
      refine ⟨32780366503864670708323481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21853577669243113805548987 32780366503864670708323481)
      ·
        refine ⟨24585274877898503031242611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32780366503864670708323481 24585274877898503031242611)
        ·
          refine ⟨36877912316847754546863917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24585274877898503031242611 36877912316847754546863917)
          ·
            refine ⟨13829217118817907955073969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36877912316847754546863917 13829217118817907955073969)
            ·
              refine ⟨10371912839113430966305477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13829217118817907955073969 10371912839113430966305477)
              ·
                refine ⟨1944733657333768306182277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10371912839113430966305477 1944733657333768306182277)
                ·
                  refine ⟨364637560750081557409177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1944733657333768306182277 364637560750081557409177)
                  ·
                    rfl

theorem cell22_3195581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_3195581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195581 prefixEnd_3195581 := by exact prefixLift 3195581
  have htrace : WordTrace (prefixWord ++ tailWord_3195581) baseStart_3195581 baseEnd_3195581 := by
    simpa [prefixWord, tailWord_3195581, baseEnd_3195581] using wordTrace_append hprefix tailTrace_3195581
  have hstable : (prefixWord ++ tailWord_3195581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195581).length < 2 ^ (prefixWord ++ tailWord_3195581).sum := by decide
  have hdescent : baseEnd_3195581 < baseStart_3195581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195594 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_3195594 : Nat := 118140960795 + 3195594 * 2 ^ 59
def prefixEnd_3195594 : Nat := 4983230072969 + 3 ^ 40 * 3195594 * 2
def baseEnd_3195594 : Nat := 1093917132415916971652491

theorem tailTrace_3195594 : CollatzResearch.WordTrace tailWord_3195594 prefixEnd_3195594 1093917132415916971652491 := by
  unfold tailWord_3195594
  simp only [CollatzResearch.WordTrace]
  refine ⟨29138222096229044212454459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77701925589944117899878557 29138222096229044212454459)
  ·
    refine ⟨43707333144343566318681689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29138222096229044212454459 43707333144343566318681689)
    ·
      refine ⟨32780499858257674739011267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43707333144343566318681689 32780499858257674739011267)
      ·
        refine ⟨49170749787386512108516901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32780499858257674739011267 49170749787386512108516901)
        ·
          refine ⟨9219515585134971020346919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49170749787386512108516901 9219515585134971020346919)
          ·
            refine ⟨13829273377702456530520379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9219515585134971020346919 13829273377702456530520379)
            ·
              refine ⟨20743910066553684795780569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13829273377702456530520379 20743910066553684795780569)
              ·
                refine ⟨15557932549915263596835427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20743910066553684795780569 15557932549915263596835427)
                ·
                  refine ⟨23336898824872895395253141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15557932549915263596835427 23336898824872895395253141)
                  ·
                    refine ⟨1093917132415916971652491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23336898824872895395253141 1093917132415916971652491)
                    ·
                      rfl

theorem cell22_3195594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_3195594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195594 prefixEnd_3195594 := by exact prefixLift 3195594
  have htrace : WordTrace (prefixWord ++ tailWord_3195594) baseStart_3195594 baseEnd_3195594 := by
    simpa [prefixWord, tailWord_3195594, baseEnd_3195594] using wordTrace_append hprefix tailTrace_3195594
  have hstable : (prefixWord ++ tailWord_3195594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195594).length < 2 ^ (prefixWord ++ tailWord_3195594).sum := by decide
  have hdescent : baseEnd_3195594 < baseStart_3195594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195596 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_3195596 : Nat := 118140960795 + 3195596 * 2 ^ 59
def prefixEnd_3195596 : Nat := 4983230072969 + 3 ^ 40 * 3195596 * 2
def baseEnd_3195596 : Nat := 1093917817056789633102485

theorem tailTrace_3195596 : CollatzResearch.WordTrace tailWord_3195596 prefixEnd_3195596 1093917817056789633102485 := by
  unfold tailWord_3195596
  simp only [CollatzResearch.WordTrace]
  refine ⟨58276480665454465595695321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77701974220605954127593761 58276480665454465595695321)
  ·
    refine ⟨43707360499090849196771491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58276480665454465595695321 43707360499090849196771491)
    ·
      refine ⟨65561040748636273795157237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43707360499090849196771491 65561040748636273795157237)
      ·
        refine ⟨6146347570184650668295991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65561040748636273795157237 6146347570184650668295991)
        ·
          refine ⟨9219521355276976002443987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6146347570184650668295991 9219521355276976002443987)
          ·
            refine ⟨13829282032915464003665981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9219521355276976002443987 13829282032915464003665981)
            ·
              refine ⟨5185980762343299001374743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13829282032915464003665981 5185980762343299001374743)
              ·
                refine ⟨7778971143514948502062115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5185980762343299001374743 7778971143514948502062115)
                ·
                  refine ⟨11668456715272422753093173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7778971143514948502062115 11668456715272422753093173)
                  ·
                    refine ⟨1093917817056789633102485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11668456715272422753093173 1093917817056789633102485)
                    ·
                      rfl

theorem cell22_3195596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_3195596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195596 prefixEnd_3195596 := by exact prefixLift 3195596
  have htrace : WordTrace (prefixWord ++ tailWord_3195596) baseStart_3195596 baseEnd_3195596 := by
    simpa [prefixWord, tailWord_3195596, baseEnd_3195596] using wordTrace_append hprefix tailTrace_3195596
  have hstable : (prefixWord ++ tailWord_3195596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195596).length < 2 ^ (prefixWord ++ tailWord_3195596).sum := by decide
  have hdescent : baseEnd_3195596 < baseStart_3195596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195701 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_3195701 : Nat := 118140960795 + 3195701 * 2 ^ 59
def prefixEnd_3195701 : Nat := 4983230072969 + 3 ^ 40 * 3195701 * 2
def baseEnd_3195701 : Nat := 1093953760702604359227163

theorem tailTrace_3195701 : CollatzResearch.WordTrace tailWord_3195701 prefixEnd_3195701 1093953760702604359227163 := by
  unfold tailWord_3195701
  simp only [CollatzResearch.WordTrace]
  refine ⟨116556790995528534123962957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77704527330352356082641971 116556790995528534123962957)
  ·
    refine ⟨43708796623323200296486109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116556790995528534123962957 43708796623323200296486109)
    ·
      refine ⟨16390798733746200111182291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43708796623323200296486109 16390798733746200111182291)
      ·
        refine ⟨24586198100619300166773437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16390798733746200111182291 24586198100619300166773437)
        ·
          refine ⟨9219824287732237562540039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24586198100619300166773437 9219824287732237562540039)
          ·
            refine ⟨13829736431598356343810059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9219824287732237562540039 13829736431598356343810059)
            ·
              refine ⟨20744604647397534515715089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13829736431598356343810059 20744604647397534515715089)
              ·
                refine ⟨15558453485548150886786317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20744604647397534515715089 15558453485548150886786317)
                ·
                  refine ⟨5834420057080556582544869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15558453485548150886786317 5834420057080556582544869)
                  ·
                    refine ⟨1093953760702604359227163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5834420057080556582544869 1093953760702604359227163)
                    ·
                      rfl

theorem cell22_3195701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_3195701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195701 prefixEnd_3195701 := by exact prefixLift 3195701
  have htrace : WordTrace (prefixWord ++ tailWord_3195701) baseStart_3195701 baseEnd_3195701 := by
    simpa [prefixWord, tailWord_3195701, baseEnd_3195701] using wordTrace_append hprefix tailTrace_3195701
  have hstable : (prefixWord ++ tailWord_3195701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195701).length < 2 ^ (prefixWord ++ tailWord_3195701).sum := by decide
  have hdescent : baseEnd_3195701 < baseStart_3195701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195733 : List Nat := [1, 3, 2, 2, 2, 1, 4, 3, 4]
def baseStart_3195733 : Nat := 118140960795 + 3195733 * 2 ^ 59
def prefixEnd_3195733 : Nat := 4983230072969 + 3 ^ 40 * 3195733 * 2
def baseEnd_3195733 : Nat := 364654904985522314142355

theorem tailTrace_3195733 : CollatzResearch.WordTrace tailWord_3195733 prefixEnd_3195733 364654904985522314142355 := by
  unfold tailWord_3195733
  simp only [CollatzResearch.WordTrace]
  refine ⟨116557958131412603589127853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77705305420941735726085235 116557958131412603589127853)
  ·
    refine ⟨43709234299279726345922945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116557958131412603589127853 43709234299279726345922945)
    ·
      refine ⟨32781925724459794759442209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43709234299279726345922945 32781925724459794759442209)
      ·
        refine ⟨24586444293344846069581657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32781925724459794759442209 24586444293344846069581657)
        ·
          refine ⟨18439833220008634552186243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24586444293344846069581657 18439833220008634552186243)
          ·
            refine ⟨27659749830012951828279365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18439833220008634552186243 27659749830012951828279365)
            ·
              refine ⟨5186203093127428467802381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27659749830012951828279365 5186203093127428467802381)
              ·
                refine ⟨1944826159922785675425893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5186203093127428467802381 1944826159922785675425893)
                ·
                  refine ⟨364654904985522314142355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1944826159922785675425893 364654904985522314142355)
                  ·
                    rfl

theorem cell22_3195733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_3195733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195733 prefixEnd_3195733 := by exact prefixLift 3195733
  have htrace : WordTrace (prefixWord ++ tailWord_3195733) baseStart_3195733 baseEnd_3195733 := by
    simpa [prefixWord, tailWord_3195733, baseEnd_3195733] using wordTrace_append hprefix tailTrace_3195733
  have hstable : (prefixWord ++ tailWord_3195733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195733).length < 2 ^ (prefixWord ++ tailWord_3195733).sum := by decide
  have hdescent : baseEnd_3195733 < baseStart_3195733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195735 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 1, 4]
def baseStart_3195735 : Nat := 118140960795 + 3195735 * 2 ^ 59
def prefixEnd_3195735 : Nat := 4983230072969 + 3 ^ 40 * 3195735 * 2
def baseEnd_3195735 : Nat := 1093965399597439603877059

theorem tailTrace_3195735 : CollatzResearch.WordTrace tailWord_3195735 prefixEnd_3195735 1093965399597439603877059 := by
  unfold tailWord_3195735
  simp only [CollatzResearch.WordTrace]
  refine ⟨116558031077405357930700659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77705354051603571953800439 116558031077405357930700659)
  ·
    refine ⟨174837046616108036896050989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116558031077405357930700659 174837046616108036896050989)
    ·
      refine ⟨65563892481040513836019121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174837046616108036896050989 65563892481040513836019121)
      ·
        refine ⟨49172919360780385377014341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65563892481040513836019121 49172919360780385377014341)
        ·
          refine ⟨9219922380146322258190189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49172919360780385377014341 9219922380146322258190189)
          ·
            refine ⟨3457470892554870846821321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9219922380146322258190189 3457470892554870846821321)
            ·
              refine ⟨2593103169416153135115991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3457470892554870846821321 2593103169416153135115991)
              ·
                refine ⟨3889654754124229702673987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593103169416153135115991 3889654754124229702673987)
                ·
                  refine ⟨5834482131186344554010981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889654754124229702673987 5834482131186344554010981)
                  ·
                    refine ⟨1093965399597439603877059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5834482131186344554010981 1093965399597439603877059)
                    ·
                      rfl

theorem cell22_3195735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_3195735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195735 prefixEnd_3195735 := by exact prefixLift 3195735
  have htrace : WordTrace (prefixWord ++ tailWord_3195735) baseStart_3195735 baseEnd_3195735 := by
    simpa [prefixWord, tailWord_3195735, baseEnd_3195735] using wordTrace_append hprefix tailTrace_3195735
  have hstable : (prefixWord ++ tailWord_3195735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195735).length < 2 ^ (prefixWord ++ tailWord_3195735).sum := by decide
  have hdescent : baseEnd_3195735 < baseStart_3195735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195744 : List Nat := [2, 1, 1, 3, 3, 1, 11]
def baseStart_3195744 : Nat := 118140960795 + 3195744 * 2 ^ 59
def prefixEnd_3195744 : Nat := 4983230072969 + 3 ^ 40 * 3195744 * 2
def baseEnd_3195744 : Nat := 40517351128939502977853

theorem tailTrace_3195744 : CollatzResearch.WordTrace tailWord_3195744 prefixEnd_3195744 40517351128939502977853 := by
  unfold tailWord_3195744
  simp only [CollatzResearch.WordTrace]
  refine ⟨58279179667186376233889143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77705572889581834978518857 58279179667186376233889143)
  ·
    refine ⟨87418769500779564350833715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58279179667186376233889143 87418769500779564350833715)
    ·
      refine ⟨131128154251169346526250573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87418769500779564350833715 131128154251169346526250573)
      ·
        refine ⟨49173057844188504947343965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131128154251169346526250573 49173057844188504947343965)
        ·
          refine ⟨18439896691570689355253987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49173057844188504947343965 18439896691570689355253987)
          ·
            refine ⟨27659845037356034032880981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18439896691570689355253987 27659845037356034032880981)
            ·
              refine ⟨40517351128939502977853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27659845037356034032880981 40517351128939502977853)
              ·
                rfl

theorem cell22_3195744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 11].length) (baseStart_3195744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195744 prefixEnd_3195744 := by exact prefixLift 3195744
  have htrace : WordTrace (prefixWord ++ tailWord_3195744) baseStart_3195744 baseEnd_3195744 := by
    simpa [prefixWord, tailWord_3195744, baseEnd_3195744] using wordTrace_append hprefix tailTrace_3195744
  have hstable : (prefixWord ++ tailWord_3195744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195744).length < 2 ^ (prefixWord ++ tailWord_3195744).sum := by decide
  have hdescent : baseEnd_3195744 < baseStart_3195744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195748 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_3195748 : Nat := 118140960795 + 3195748 * 2 ^ 59
def prefixEnd_3195748 : Nat := 4983230072969 + 3 ^ 40 * 3195748 * 2
def baseEnd_3195748 : Nat := 1093969849763111903302019

theorem tailTrace_3195748 : CollatzResearch.WordTrace tailWord_3195748 prefixEnd_3195748 1093969849763111903302019 := by
  unfold tailWord_3195748
  simp only [CollatzResearch.WordTrace]
  refine ⟨58279252613179130575461949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77705670150905507433949265 58279252613179130575461949)
  ·
    refine ⟨21854719729942173965798231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58279252613179130575461949 21854719729942173965798231)
    ·
      refine ⟨32782079594913260948697347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21854719729942173965798231 32782079594913260948697347)
      ·
        refine ⟨49173119392369891423046021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32782079594913260948697347 49173119392369891423046021)
        ·
          refine ⟨9219959886069354641821129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49173119392369891423046021 9219959886069354641821129)
          ·
            refine ⟨6914969914552015981365847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9219959886069354641821129 6914969914552015981365847)
            ·
              refine ⟨10372454871828023972048771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6914969914552015981365847 10372454871828023972048771)
              ·
                refine ⟨15558682307742035958073157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10372454871828023972048771 15558682307742035958073157)
                ·
                  refine ⟨2917252932701631742138717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15558682307742035958073157 2917252932701631742138717)
                  ·
                    refine ⟨1093969849763111903302019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917252932701631742138717 1093969849763111903302019)
                    ·
                      rfl

theorem cell22_3195748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_3195748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195748 prefixEnd_3195748 := by exact prefixLift 3195748
  have htrace : WordTrace (prefixWord ++ tailWord_3195748) baseStart_3195748 baseEnd_3195748 := by
    simpa [prefixWord, tailWord_3195748, baseEnd_3195748] using wordTrace_append hprefix tailTrace_3195748
  have hstable : (prefixWord ++ tailWord_3195748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195748).length < 2 ^ (prefixWord ++ tailWord_3195748).sum := by decide
  have hdescent : baseEnd_3195748 < baseStart_3195748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195776 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 5, 3]
def baseStart_3195776 : Nat := 118140960795 + 3195776 * 2 ^ 59
def prefixEnd_3195776 : Nat := 4983230072969 + 3 ^ 40 * 3195776 * 2
def baseEnd_3195776 : Nat := 1093979434735329163601933

theorem tailTrace_3195776 : CollatzResearch.WordTrace tailWord_3195776 prefixEnd_3195776 1093979434735329163601933 := by
  unfold tailWord_3195776
  simp only [CollatzResearch.WordTrace]
  refine ⟨58279763235128410966471591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77706350980171214621962121 58279763235128410966471591)
  ·
    refine ⟨87419644852692616449707387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58279763235128410966471591 87419644852692616449707387)
    ·
      refine ⟨131129467279038924674561081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87419644852692616449707387 131129467279038924674561081)
      ·
        refine ⟨98347100459279193505920811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131129467279038924674561081 98347100459279193505920811)
        ·
          refine ⟨147520650688918790258881217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98347100459279193505920811 147520650688918790258881217)
          ·
            refine ⟨110640488016689092694160913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147520650688918790258881217 110640488016689092694160913)
            ·
              refine ⟨82980366012516819520620685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110640488016689092694160913 82980366012516819520620685)
              ·
                refine ⟨31117637254693807320232757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82980366012516819520620685 31117637254693807320232757)
                ·
                  refine ⟨2917278492627544436271821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31117637254693807320232757 2917278492627544436271821)
                  ·
                    refine ⟨1093979434735329163601933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917278492627544436271821 1093979434735329163601933)
                    ·
                      rfl

theorem cell22_3195776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 5, 3].length) (baseStart_3195776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195776 prefixEnd_3195776 := by exact prefixLift 3195776
  have htrace : WordTrace (prefixWord ++ tailWord_3195776) baseStart_3195776 baseEnd_3195776 := by
    simpa [prefixWord, tailWord_3195776, baseEnd_3195776] using wordTrace_append hprefix tailTrace_3195776
  have hstable : (prefixWord ++ tailWord_3195776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195776).length < 2 ^ (prefixWord ++ tailWord_3195776).sum := by decide
  have hdescent : baseEnd_3195776 < baseStart_3195776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195810 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_3195810 : Nat := 118140960795 + 3195810 * 2 ^ 59
def prefixEnd_3195810 : Nat := 4983230072969 + 3 ^ 40 * 3195810 * 2
def baseEnd_3195810 : Nat := 1093991073630164408251829

theorem tailTrace_3195810 : CollatzResearch.WordTrace tailWord_3195810 prefixEnd_3195810 1093991073630164408251829 := by
  unfold tailWord_3195810
  simp only [CollatzResearch.WordTrace]
  refine ⟨29140191638033411434920221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77707177701422430493120589 29140191638033411434920221)
  ·
    refine ⟨10927571864262529288095083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29140191638033411434920221 10927571864262529288095083)
    ·
      refine ⟨16391357796393793932142625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10927571864262529288095083 16391357796393793932142625)
      ·
        refine ⟨12293518347295345449106969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16391357796393793932142625 12293518347295345449106969)
        ·
          refine ⟨9220138760471509086830227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12293518347295345449106969 9220138760471509086830227)
          ·
            refine ⟨13830208140707263630245341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220138760471509086830227 13830208140707263630245341)
            ·
              refine ⟨5186328052765223861342003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13830208140707263630245341 5186328052765223861342003)
              ·
                refine ⟨7779492079147835792013005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5186328052765223861342003 7779492079147835792013005)
                ·
                  refine ⟨2917309529680438422004877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7779492079147835792013005 2917309529680438422004877)
                  ·
                    refine ⟨1093991073630164408251829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917309529680438422004877 1093991073630164408251829)
                    ·
                      rfl

theorem cell22_3195810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_3195810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195810 prefixEnd_3195810 := by exact prefixLift 3195810
  have htrace : WordTrace (prefixWord ++ tailWord_3195810) baseStart_3195810 baseEnd_3195810 := by
    simpa [prefixWord, tailWord_3195810, baseEnd_3195810] using wordTrace_append hprefix tailTrace_3195810
  have hstable : (prefixWord ++ tailWord_3195810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195810).length < 2 ^ (prefixWord ++ tailWord_3195810).sum := by decide
  have hdescent : baseEnd_3195810 < baseStart_3195810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195861 : List Nat := [1, 3, 2, 3, 4, 1, 2, 2, 1, 3]
def baseStart_3195861 : Nat := 118140960795 + 3195861 * 2 ^ 59
def prefixEnd_3195861 : Nat := 4983230072969 + 3 ^ 40 * 3195861 * 2
def baseEnd_3195861 : Nat := 1094008531972417275226673

theorem tailTrace_3195861 : CollatzResearch.WordTrace tailWord_3195861 prefixEnd_3195861 1094008531972417275226673 := by
  unfold tailWord_3195861
  simp only [CollatzResearch.WordTrace]
  refine ⟨116562626674948881449787437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77708417783299254299858291 116562626674948881449787437)
  ·
    refine ⟨43710985003105830543670289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116562626674948881449787437 43710985003105830543670289)
    ·
      refine ⟨32783238752329372907752717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43710985003105830543670289 32783238752329372907752717)
      ·
        refine ⟨12293714532123514840407269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32783238752329372907752717 12293714532123514840407269)
        ·
          refine ⟨2305071474773159032576363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12293714532123514840407269 2305071474773159032576363)
          ·
            refine ⟨3457607212159738548864545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305071474773159032576363 3457607212159738548864545)
            ·
              refine ⟨2593205409119803911648409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3457607212159738548864545 2593205409119803911648409)
              ·
                refine ⟨1944904056839852933736307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2593205409119803911648409 1944904056839852933736307)
                ·
                  refine ⟨2917356085259779400604461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944904056839852933736307 2917356085259779400604461)
                  ·
                    refine ⟨1094008531972417275226673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917356085259779400604461 1094008531972417275226673)
                    ·
                      rfl

theorem cell22_3195861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_3195861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195861 prefixEnd_3195861 := by exact prefixLift 3195861
  have htrace : WordTrace (prefixWord ++ tailWord_3195861) baseStart_3195861 baseEnd_3195861 := by
    simpa [prefixWord, tailWord_3195861, baseEnd_3195861] using wordTrace_append hprefix tailTrace_3195861
  have hstable : (prefixWord ++ tailWord_3195861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195861).length < 2 ^ (prefixWord ++ tailWord_3195861).sum := by decide
  have hdescent : baseEnd_3195861 < baseStart_3195861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3195962 : List Nat := [3, 1, 1, 1, 3, 1, 5, 3, 1, 3]
def baseStart_3195962 : Nat := 118140960795 + 3195962 * 2 ^ 59
def prefixEnd_3195962 : Nat := 4983230072969 + 3 ^ 40 * 3195962 * 2
def baseEnd_3195962 : Nat := 1094043106336486678451363

theorem tailTrace_3195962 : CollatzResearch.WordTrace tailWord_3195962 prefixEnd_3195962 1094043106336486678451363 := by
  unfold tailWord_3195962
  simp only [CollatzResearch.WordTrace]
  refine ⟨29141577611895743924803535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77710873631721983799476093 29141577611895743924803535)
  ·
    refine ⟨43712366417843615887205303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29141577611895743924803535 43712366417843615887205303)
    ·
      refine ⟨65568549626765423830807955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43712366417843615887205303 65568549626765423830807955)
      ·
        refine ⟨98352824440148135746211933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65568549626765423830807955 98352824440148135746211933)
        ·
          refine ⟨36882309165055550904829475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98352824440148135746211933 36882309165055550904829475)
          ·
            refine ⟨55323463747583326357244213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36882309165055550904829475 55323463747583326357244213)
            ·
              refine ⟨5186574726335936845991645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55323463747583326357244213 5186574726335936845991645)
              ·
                refine ⟨1944965522375976317246867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5186574726335936845991645 1944965522375976317246867)
                ·
                  refine ⟨2917448283563964475870301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1944965522375976317246867 2917448283563964475870301)
                  ·
                    refine ⟨1094043106336486678451363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917448283563964475870301 1094043106336486678451363)
                    ·
                      rfl

theorem cell22_3195962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_3195962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3195962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3195962 prefixEnd_3195962 := by exact prefixLift 3195962
  have htrace : WordTrace (prefixWord ++ tailWord_3195962) baseStart_3195962 baseEnd_3195962 := by
    simpa [prefixWord, tailWord_3195962, baseEnd_3195962] using wordTrace_append hprefix tailTrace_3195962
  have hstable : (prefixWord ++ tailWord_3195962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3195962).length < 2 ^ (prefixWord ++ tailWord_3195962).sum := by decide
  have hdescent : baseEnd_3195962 < baseStart_3195962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3195962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196037 : List Nat := [1, 3, 1, 1, 6, 1, 1, 4, 4]
def baseStart_3196037 : Nat := 118140960795 + 3196037 * 2 ^ 59
def prefixEnd_3196037 : Nat := 4983230072969 + 3 ^ 40 * 3196037 * 2
def baseEnd_3196037 : Nat := 364689593456403827608711

theorem tailTrace_3196037 : CollatzResearch.WordTrace tailWord_3196037 prefixEnd_3196037 364689593456403827608711 := by
  unfold tailWord_3196037
  simp only [CollatzResearch.WordTrace]
  refine ⟨116569045922311263508194365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77712697281540842338796243 116569045922311263508194365)
  ·
    refine ⟨43713392220866723815572887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116569045922311263508194365 43713392220866723815572887)
    ·
      refine ⟨65570088331300085723359331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43713392220866723815572887 65570088331300085723359331)
      ·
        refine ⟨98355132496950128585038997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65570088331300085723359331 98355132496950128585038997)
        ·
          refine ⟨4610396835794537277423703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98355132496950128585038997 4610396835794537277423703)
          ·
            refine ⟨6915595253691805916135555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610396835794537277423703 6915595253691805916135555)
            ·
              refine ⟨10373392880537708874203333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6915595253691805916135555 10373392880537708874203333)
              ·
                refine ⟨1945011165100820413913125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10373392880537708874203333 1945011165100820413913125)
                ·
                  refine ⟨364689593456403827608711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1945011165100820413913125 364689593456403827608711)
                  ·
                    rfl

theorem cell22_3196037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_3196037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196037 prefixEnd_3196037 := by exact prefixLift 3196037
  have htrace : WordTrace (prefixWord ++ tailWord_3196037) baseStart_3196037 baseEnd_3196037 := by
    simpa [prefixWord, tailWord_3196037, baseEnd_3196037] using wordTrace_append hprefix tailTrace_3196037
  have hstable : (prefixWord ++ tailWord_3196037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196037).length < 2 ^ (prefixWord ++ tailWord_3196037).sum := by decide
  have hdescent : baseEnd_3196037 < baseStart_3196037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196065 : List Nat := [1, 2, 3, 3, 1, 1, 5, 6]
def baseStart_3196065 : Nat := 118140960795 + 3196065 * 2 ^ 59
def prefixEnd_3196065 : Nat := 4983230072969 + 3 ^ 40 * 3196065 * 2
def baseEnd_3196065 : Nat := 121564262815714304791783

theorem tailTrace_3196065 : CollatzResearch.WordTrace tailWord_3196065 prefixEnd_3196065 121564262815714304791783 := by
  unfold tailWord_3196065
  simp only [CollatzResearch.WordTrace]
  refine ⟨116570067166209824290213649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77713378110806549526809099 116570067166209824290213649)
  ·
    refine ⟨87427550374657368217660237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116570067166209824290213649 87427550374657368217660237)
    ·
      refine ⟨32785331390496513081622589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87427550374657368217660237 32785331390496513081622589)
      ·
        refine ⟨12294499271436192405608471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32785331390496513081622589 12294499271436192405608471)
        ·
          refine ⟨18441748907154288608412707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12294499271436192405608471 18441748907154288608412707)
          ·
            refine ⟨27662623360731432912619061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18441748907154288608412707 27662623360731432912619061)
            ·
              refine ⟨2593370940068571835558037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27662623360731432912619061 2593370940068571835558037)
              ·
                refine ⟨121564262815714304791783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2593370940068571835558037 121564262815714304791783)
                ·
                  rfl

theorem cell22_3196065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 6].length) (baseStart_3196065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196065 prefixEnd_3196065 := by exact prefixLift 3196065
  have htrace : WordTrace (prefixWord ++ tailWord_3196065) baseStart_3196065 baseEnd_3196065 := by
    simpa [prefixWord, tailWord_3196065, baseEnd_3196065] using wordTrace_append hprefix tailTrace_3196065
  have hstable : (prefixWord ++ tailWord_3196065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196065).length < 2 ^ (prefixWord ++ tailWord_3196065).sum := by decide
  have hdescent : baseEnd_3196065 < baseStart_3196065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196086 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3196086 : Nat := 118140960795 + 3196086 * 2 ^ 59
def prefixEnd_3196086 : Nat := 4983230072969 + 3 ^ 40 * 3196086 * 2
def baseEnd_3196086 : Nat := 1094085554070591688350983

theorem tailTrace_3196086 : CollatzResearch.WordTrace tailWord_3196086 prefixEnd_3196086 1094085554070591688350983 := by
  unfold tailWord_3196086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7285677068695859054795507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77713888732755829917818741 7285677068695859054795507)
  ·
    refine ⟨10928515603043788582193261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7285677068695859054795507 10928515603043788582193261)
    ·
      refine ⟨4098193351141420718322473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10928515603043788582193261 4098193351141420718322473)
      ·
        refine ⟨3073645013356065538741855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4098193351141420718322473 3073645013356065538741855)
        ·
          refine ⟨4610467520034098308112783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3073645013356065538741855 4610467520034098308112783)
          ·
            refine ⟨6915701280051147462169175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610467520034098308112783 6915701280051147462169175)
            ·
              refine ⟨10373551920076721193253763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6915701280051147462169175 10373551920076721193253763)
              ·
                refine ⟨15560327880115081789880645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10373551920076721193253763 15560327880115081789880645)
                ·
                  refine ⟨2917561477521577835602621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15560327880115081789880645 2917561477521577835602621)
                  ·
                    refine ⟨1094085554070591688350983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917561477521577835602621 1094085554070591688350983)
                    ·
                      rfl

theorem cell22_3196086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3196086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196086 prefixEnd_3196086 := by exact prefixLift 3196086
  have htrace : WordTrace (prefixWord ++ tailWord_3196086) baseStart_3196086 baseEnd_3196086 := by
    simpa [prefixWord, tailWord_3196086, baseEnd_3196086] using wordTrace_append hprefix tailTrace_3196086
  have hstable : (prefixWord ++ tailWord_3196086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196086).length < 2 ^ (prefixWord ++ tailWord_3196086).sum := by decide
  have hdescent : baseEnd_3196086 < baseStart_3196086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196116 : List Nat := [2, 4, 1, 4, 2, 1, 2, 6]
def baseStart_3196116 : Nat := 118140960795 + 3196116 * 2 ^ 59
def prefixEnd_3196116 : Nat := 4983230072969 + 3 ^ 40 * 3196116 * 2
def baseEnd_3196116 : Nat := 121566202631520178900099

theorem tailTrace_3196116 : CollatzResearch.WordTrace tailWord_3196116 prefixEnd_3196116 121566202631520178900099 := by
  unfold tailWord_3196116
  simp only [CollatzResearch.WordTrace]
  refine ⟨58285963644512530000160101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77714618192683373333546801 58285963644512530000160101)
  ·
    refine ⟨10928618183346099375030019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58285963644512530000160101 10928618183346099375030019)
    ·
      refine ⟨16392927275019149062545029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10928618183346099375030019 16392927275019149062545029)
      ·
        refine ⟨3073673864066090449227193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16392927275019149062545029 3073673864066090449227193)
        ·
          refine ⟨2305255398049567836920395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3073673864066090449227193 2305255398049567836920395)
          ·
            refine ⟨3457883097074351755380593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305255398049567836920395 3457883097074351755380593)
            ·
              refine ⟨2593412322805763816535445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3457883097074351755380593 2593412322805763816535445)
              ·
                refine ⟨121566202631520178900099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2593412322805763816535445 121566202631520178900099)
                ·
                  rfl

theorem cell22_3196116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 6].length) (baseStart_3196116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196116 prefixEnd_3196116 := by exact prefixLift 3196116
  have htrace : WordTrace (prefixWord ++ tailWord_3196116) baseStart_3196116 baseEnd_3196116 := by
    simpa [prefixWord, tailWord_3196116, baseEnd_3196116] using wordTrace_append hprefix tailTrace_3196116
  have hstable : (prefixWord ++ tailWord_3196116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196116).length < 2 ^ (prefixWord ++ tailWord_3196116).sum := by decide
  have hdescent : baseEnd_3196116 < baseStart_3196116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196170 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_3196170 : Nat := 118140960795 + 3196170 * 2 ^ 59
def prefixEnd_3196170 : Nat := 4983230072969 + 3 ^ 40 * 3196170 * 2
def baseEnd_3196170 : Nat := 1094114308987243469250725

theorem tailTrace_3196170 : CollatzResearch.WordTrace tailWord_3196170 prefixEnd_3196170 1094114308987243469250725 := by
  unfold tailWord_3196170
  simp only [CollatzResearch.WordTrace]
  refine ⟨29143474207707356805696491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77715931220552951481857309 29143474207707356805696491)
  ·
    refine ⟨43715211311561035208544737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29143474207707356805696491 43715211311561035208544737)
    ·
      refine ⟨32786408483670776406408553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43715211311561035208544737 32786408483670776406408553)
      ·
        refine ⟨24589806362753082304806415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32786408483670776406408553 24589806362753082304806415)
        ·
          refine ⟨36884709544129623457209623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24589806362753082304806415 36884709544129623457209623)
          ·
            refine ⟨55327064316194435185814435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36884709544129623457209623 55327064316194435185814435)
            ·
              refine ⟨82990596474291652778721653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55327064316194435185814435 82990596474291652778721653)
              ·
                refine ⟨7780368419464842448005155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82990596474291652778721653 7780368419464842448005155)
                ·
                  refine ⟨11670552629197263672007733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7780368419464842448005155 11670552629197263672007733)
                  ·
                    refine ⟨1094114308987243469250725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11670552629197263672007733 1094114308987243469250725)
                    ·
                      rfl

theorem cell22_3196170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_3196170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196170 prefixEnd_3196170 := by exact prefixLift 3196170
  have htrace : WordTrace (prefixWord ++ tailWord_3196170) baseStart_3196170 baseEnd_3196170 := by
    simpa [prefixWord, tailWord_3196170, baseEnd_3196170] using wordTrace_append hprefix tailTrace_3196170
  have hstable : (prefixWord ++ tailWord_3196170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196170).length < 2 ^ (prefixWord ++ tailWord_3196170).sum := by decide
  have hdescent : baseEnd_3196170 < baseStart_3196170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196174 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_3196174 : Nat := 118140960795 + 3196174 * 2 ^ 59
def prefixEnd_3196174 : Nat := 4983230072969 + 3 ^ 40 * 3196174 * 2
def baseEnd_3196174 : Nat := 1094115678268988792150713

theorem tailTrace_3196174 : CollatzResearch.WordTrace tailWord_3196174 prefixEnd_3196174 1094115678268988792150713 := by
  unfold tailWord_3196174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14571755340351866988241447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77716028481876623937287717 14571755340351866988241447)
  ·
    refine ⟨21857633010527800482362171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14571755340351866988241447 21857633010527800482362171)
    ·
      refine ⟨32786449515791700723543257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21857633010527800482362171 32786449515791700723543257)
      ·
        refine ⟨24589837136843775542657443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32786449515791700723543257 24589837136843775542657443)
        ·
          refine ⟨36884755705265663313986165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24589837136843775542657443 36884755705265663313986165)
          ·
            refine ⟨3457945847368655935686203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36884755705265663313986165 3457945847368655935686203)
            ·
              refine ⟨5186918771052983903529305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3457945847368655935686203 5186918771052983903529305)
              ·
                refine ⟨3890189078289737927646979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5186918771052983903529305 3890189078289737927646979)
                ·
                  refine ⟨5835283617434606891470469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3890189078289737927646979 5835283617434606891470469)
                  ·
                    refine ⟨1094115678268988792150713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5835283617434606891470469 1094115678268988792150713)
                    ·
                      rfl

theorem cell22_3196174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_3196174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196174 prefixEnd_3196174 := by exact prefixLift 3196174
  have htrace : WordTrace (prefixWord ++ tailWord_3196174) baseStart_3196174 baseEnd_3196174 := by
    simpa [prefixWord, tailWord_3196174, baseEnd_3196174] using wordTrace_append hprefix tailTrace_3196174
  have hstable : (prefixWord ++ tailWord_3196174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196174).length < 2 ^ (prefixWord ++ tailWord_3196174).sum := by decide
  have hdescent : baseEnd_3196174 < baseStart_3196174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196200 : List Nat := [2, 1, 5, 1, 2, 11]
def baseStart_3196200 : Nat := 118140960795 + 3196200 * 2 ^ 59
def prefixEnd_3196200 : Nat := 4983230072969 + 3 ^ 40 * 3196200 * 2
def baseEnd_3196200 : Nat := 13507710846917696185193

theorem tailTrace_3196200 : CollatzResearch.WordTrace tailWord_3196200 prefixEnd_3196200 13507710846917696185193 := by
  unfold tailWord_3196200
  simp only [CollatzResearch.WordTrace]
  refine ⟨58287495510360371173189027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77716660680480494897585369 58287495510360371173189027)
  ·
    refine ⟨87431243265540556759783541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58287495510360371173189027 87431243265540556759783541)
    ·
      refine ⟨8196679056144427196229707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87431243265540556759783541 8196679056144427196229707)
      ·
        refine ⟨12295018584216640794344561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8196679056144427196229707 12295018584216640794344561)
        ·
          refine ⟨9221263938162480595758421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12295018584216640794344561 9221263938162480595758421)
          ·
            refine ⟨13507710846917696185193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9221263938162480595758421 13507710846917696185193)
            ·
              rfl

theorem cell22_3196200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 11].length) (baseStart_3196200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196200 prefixEnd_3196200 := by exact prefixLift 3196200
  have htrace : WordTrace (prefixWord ++ tailWord_3196200) baseStart_3196200 baseEnd_3196200 := by
    simpa [prefixWord, tailWord_3196200, baseEnd_3196200] using wordTrace_append hprefix tailTrace_3196200
  have hstable : (prefixWord ++ tailWord_3196200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196200).length < 2 ^ (prefixWord ++ tailWord_3196200).sum := by decide
  have hdescent : baseEnd_3196200 < baseStart_3196200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196249 : List Nat := [1, 2, 1, 2, 2, 2, 3, 5, 1, 3]
def baseStart_3196249 : Nat := 118140960795 + 3196249 * 2 ^ 59
def prefixEnd_3196249 : Nat := 4983230072969 + 3 ^ 40 * 3196249 * 2
def baseEnd_3196249 : Nat := 1094141352301713596525483

theorem tailTrace_3196249 : CollatzResearch.WordTrace tailWord_3196249 prefixEnd_3196249 1094141352301713596525483 := by
  unfold tailWord_3196249
  simp only [CollatzResearch.WordTrace]
  refine ⟨116576778197543223714911801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77717852131695482476607867 116576778197543223714911801)
  ·
    refine ⟨87432583648157417786183851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116576778197543223714911801 87432583648157417786183851)
    ·
      refine ⟨131148875472236126679275777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87432583648157417786183851 131148875472236126679275777)
      ·
        refine ⟨98361656604177095009456833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131148875472236126679275777 98361656604177095009456833)
        ·
          refine ⟨73771242453132821257092625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98361656604177095009456833 73771242453132821257092625)
          ·
            refine ⟨55328431839849615942819469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73771242453132821257092625 55328431839849615942819469)
            ·
              refine ⟨20748161939943605978557301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55328431839849615942819469 20748161939943605978557301)
              ·
                refine ⟨1945140181869713060489747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20748161939943605978557301 1945140181869713060489747)
                ·
                  refine ⟨2917710272804569590734621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945140181869713060489747 2917710272804569590734621)
                  ·
                    refine ⟨1094141352301713596525483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917710272804569590734621 1094141352301713596525483)
                    ·
                      rfl

theorem cell22_3196249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 1, 3].length) (baseStart_3196249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196249 prefixEnd_3196249 := by exact prefixLift 3196249
  have htrace : WordTrace (prefixWord ++ tailWord_3196249) baseStart_3196249 baseEnd_3196249 := by
    simpa [prefixWord, tailWord_3196249, baseEnd_3196249] using wordTrace_append hprefix tailTrace_3196249
  have hstable : (prefixWord ++ tailWord_3196249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196249).length < 2 ^ (prefixWord ++ tailWord_3196249).sum := by decide
  have hdescent : baseEnd_3196249 < baseStart_3196249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196266 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 3, 3]
def baseStart_3196266 : Nat := 118140960795 + 3196266 * 2 ^ 59
def prefixEnd_3196266 : Nat := 4983230072969 + 3 ^ 40 * 3196266 * 2
def baseEnd_3196266 : Nat := 1094147171749131218850431

theorem tailTrace_3196266 : CollatzResearch.WordTrace tailWord_3196266 prefixEnd_3196266 1094147171749131218850431 := by
  unfold tailWord_3196266
  simp only [CollatzResearch.WordTrace]
  refine ⟨29144349559620408904570163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77718265492321090412187101 29144349559620408904570163)
  ·
    refine ⟨43716524339430613356855245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29144349559620408904570163 43716524339430613356855245)
    ·
      refine ⟨16393696627286480008820717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43716524339430613356855245 16393696627286480008820717)
      ·
        refine ⟨6147636235232430003307769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16393696627286480008820717 6147636235232430003307769)
        ·
          refine ⟨4610727176424322502480827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6147636235232430003307769 4610727176424322502480827)
          ·
            refine ⟨6916090764636483753721241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610727176424322502480827 6916090764636483753721241)
            ·
              refine ⟨5187068073477362815290931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6916090764636483753721241 5187068073477362815290931)
              ·
                refine ⟨7780602110216044222936397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5187068073477362815290931 7780602110216044222936397)
                ·
                  refine ⟨2917725791331016583601149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7780602110216044222936397 2917725791331016583601149)
                  ·
                    refine ⟨1094147171749131218850431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917725791331016583601149 1094147171749131218850431)
                    ·
                      rfl

theorem cell22_3196266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_3196266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196266 prefixEnd_3196266 := by exact prefixLift 3196266
  have htrace : WordTrace (prefixWord ++ tailWord_3196266) baseStart_3196266 baseEnd_3196266 := by
    simpa [prefixWord, tailWord_3196266, baseEnd_3196266] using wordTrace_append hprefix tailTrace_3196266
  have hstable : (prefixWord ++ tailWord_3196266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196266).length < 2 ^ (prefixWord ++ tailWord_3196266).sum := by decide
  have hdescent : baseEnd_3196266 < baseStart_3196266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196337 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 4, 4]
def baseStart_3196337 : Nat := 118140960795 + 3196337 * 2 ^ 59
def prefixEnd_3196337 : Nat := 4983230072969 + 3 ^ 40 * 3196337 * 2
def baseEnd_3196337 : Nat := 1094171476500110700325213

theorem tailTrace_3196337 : CollatzResearch.WordTrace tailWord_3196337 prefixEnd_3196337 1094171476500110700325213 := by
  unfold tailWord_3196337
  simp only [CollatzResearch.WordTrace]
  refine ⟨116579987821224414744115265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77719991880816276496076843 116579987821224414744115265)
  ·
    refine ⟨87434990865918311058086449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116579987821224414744115265 87434990865918311058086449)
    ·
      refine ⟨65576243149438733293564837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87434990865918311058086449 65576243149438733293564837)
      ·
        refine ⟨12295545590519762492543407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65576243149438733293564837 12295545590519762492543407)
        ·
          refine ⟨18443318385779643738815111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12295545590519762492543407 18443318385779643738815111)
          ·
            refine ⟨27664977578669465608222667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18443318385779643738815111 27664977578669465608222667)
            ·
              refine ⟨41497466368004198412334001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27664977578669465608222667 41497466368004198412334001)
              ·
                refine ⟨31123099776003148809250501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41497466368004198412334001 31123099776003148809250501)
                ·
                  refine ⟨5835581208000590401734469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31123099776003148809250501 5835581208000590401734469)
                  ·
                    refine ⟨1094171476500110700325213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5835581208000590401734469 1094171476500110700325213)
                    ·
                      rfl

theorem cell22_3196337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_3196337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196337 prefixEnd_3196337 := by exact prefixLift 3196337
  have htrace : WordTrace (prefixWord ++ tailWord_3196337) baseStart_3196337 baseEnd_3196337 := by
    simpa [prefixWord, tailWord_3196337, baseEnd_3196337] using wordTrace_append hprefix tailTrace_3196337
  have hstable : (prefixWord ++ tailWord_3196337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196337).length < 2 ^ (prefixWord ++ tailWord_3196337).sum := by decide
  have hdescent : baseEnd_3196337 < baseStart_3196337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196474 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 6, 3]
def baseStart_3196474 : Nat := 118140960795 + 3196474 * 2 ^ 59
def prefixEnd_3196474 : Nat := 4983230072969 + 3 ^ 40 * 3196474 * 2
def baseEnd_3196474 : Nat := 1094218374399888009649793

theorem tailTrace_3196474 : CollatzResearch.WordTrace tailWord_3196474 prefixEnd_3196474 1094218374399888009649793 := by
  unfold tailWord_3196474
  simp only [CollatzResearch.WordTrace]
  refine ⟨29146246155432021785463119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77723323081152058094568317 29146246155432021785463119)
  ·
    refine ⟨43719369233148032678194679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29146246155432021785463119 43719369233148032678194679)
    ·
      refine ⟨65579053849722049017292019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43719369233148032678194679 65579053849722049017292019)
      ·
        refine ⟨98368580774583073525938029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65579053849722049017292019 98368580774583073525938029)
        ·
          refine ⟨36888217790468652572226761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98368580774583073525938029 36888217790468652572226761)
          ·
            refine ⟨27666163342851489429170071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36888217790468652572226761 27666163342851489429170071)
            ·
              refine ⟨41499245014277234143755107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27666163342851489429170071 41499245014277234143755107)
              ·
                refine ⟨62248867521415851215632661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41499245014277234143755107 62248867521415851215632661)
                ·
                  refine ⟨2917915665066368025732781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62248867521415851215632661 2917915665066368025732781)
                  ·
                    refine ⟨1094218374399888009649793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917915665066368025732781 1094218374399888009649793)
                    ·
                      rfl

theorem cell22_3196474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_3196474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196474 prefixEnd_3196474 := by exact prefixLift 3196474
  have htrace : WordTrace (prefixWord ++ tailWord_3196474) baseStart_3196474 baseEnd_3196474 := by
    simpa [prefixWord, tailWord_3196474, baseEnd_3196474] using wordTrace_append hprefix tailTrace_3196474
  have hstable : (prefixWord ++ tailWord_3196474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196474).length < 2 ^ (prefixWord ++ tailWord_3196474).sum := by decide
  have hdescent : baseEnd_3196474 < baseStart_3196474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196493 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 6]
def baseStart_3196493 : Nat := 118140960795 + 3196493 * 2 ^ 59
def prefixEnd_3196493 : Nat := 4983230072969 + 3 ^ 40 * 3196493 * 2
def baseEnd_3196493 : Nat := 364741626162726097808245

theorem tailTrace_3196493 : CollatzResearch.WordTrace tailWord_3196493 prefixEnd_3196493 364741626162726097808245 := by
  unfold tailWord_3196493
  simp only [CollatzResearch.WordTrace]
  refine ⟨116585677608659253386794133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77723785072439502257862755 116585677608659253386794133)
  ·
    refine ⟨5464953637905902502505975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116585677608659253386794133 5464953637905902502505975)
    ·
      refine ⟨8197430456858853753758963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5464953637905902502505975 8197430456858853753758963)
      ·
        refine ⟨12296145685288280630638445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8197430456858853753758963 12296145685288280630638445)
        ·
          refine ⟨4611054631983105236489417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12296145685288280630638445 4611054631983105236489417)
          ·
            refine ⟨3458290973987328927367063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4611054631983105236489417 3458290973987328927367063)
            ·
              refine ⟨5187436460980993391050595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458290973987328927367063 5187436460980993391050595)
              ·
                refine ⟨7781154691471490086575893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5187436460980993391050595 7781154691471490086575893)
                ·
                  refine ⟨364741626162726097808245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7781154691471490086575893 364741626162726097808245)
                  ·
                    rfl

theorem cell22_3196493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_3196493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196493 prefixEnd_3196493 := by exact prefixLift 3196493
  have htrace : WordTrace (prefixWord ++ tailWord_3196493) baseStart_3196493 baseEnd_3196493 := by
    simpa [prefixWord, tailWord_3196493, baseEnd_3196493] using wordTrace_append hprefix tailTrace_3196493
  have hstable : (prefixWord ++ tailWord_3196493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196493).length < 2 ^ (prefixWord ++ tailWord_3196493).sum := by decide
  have hdescent : baseEnd_3196493 < baseStart_3196493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196508 : List Nat := [2, 2, 4, 1, 2, 2, 1, 3, 2, 3]
def baseStart_3196508 : Nat := 118140960795 + 3196508 * 2 ^ 59
def prefixEnd_3196508 : Nat := 4983230072969 + 3 ^ 40 * 3196508 * 2
def baseEnd_3196508 : Nat := 1094230013294723254299689

theorem tailTrace_3196508 : CollatzResearch.WordTrace tailWord_3196508 prefixEnd_3196508 1094230013294723254299689 := by
  unfold tailWord_3196508
  simp only [CollatzResearch.WordTrace]
  refine ⟨58293112351802455474295089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77724149802403273965726785 58293112351802455474295089)
  ·
    refine ⟨43719834263851841605721317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58293112351802455474295089 43719834263851841605721317)
    ·
      refine ⟨8197468924472220301072747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43719834263851841605721317 8197468924472220301072747)
      ·
        refine ⟨12296203386708330451609121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8197468924472220301072747 12296203386708330451609121)
        ·
          refine ⟨9222152540031247838706841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12296203386708330451609121 9222152540031247838706841)
          ·
            refine ⟨6916614405023435879030131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9222152540031247838706841 6916614405023435879030131)
            ·
              refine ⟨10374921607535153818545197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6916614405023435879030131 10374921607535153818545197)
              ·
                refine ⟨3890595602825682681954449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10374921607535153818545197 3890595602825682681954449)
                ·
                  refine ⟨2917946702119262011465837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3890595602825682681954449 2917946702119262011465837)
                  ·
                    refine ⟨1094230013294723254299689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2917946702119262011465837 1094230013294723254299689)
                    ·
                      rfl

theorem cell22_3196508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_3196508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196508 prefixEnd_3196508 := by exact prefixLift 3196508
  have htrace : WordTrace (prefixWord ++ tailWord_3196508) baseStart_3196508 baseEnd_3196508 := by
    simpa [prefixWord, tailWord_3196508, baseEnd_3196508] using wordTrace_append hprefix tailTrace_3196508
  have hstable : (prefixWord ++ tailWord_3196508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196508).length < 2 ^ (prefixWord ++ tailWord_3196508).sum := by decide
  have hdescent : baseEnd_3196508 < baseStart_3196508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196579 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 3, 4]
def baseStart_3196579 : Nat := 118140960795 + 3196579 * 2 ^ 59
def prefixEnd_3196579 : Nat := 4983230072969 + 3 ^ 40 * 3196579 * 2
def baseEnd_3196579 : Nat := 1094254318045702735774471

theorem tailTrace_3196579 : CollatzResearch.WordTrace tailWord_3196579 prefixEnd_3196579 1094254318045702735774471 := by
  unfold tailWord_3196579
  simp only [CollatzResearch.WordTrace]
  refine ⟨116588814286347690074424791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77725876190898460049616527 116588814286347690074424791)
  ·
    refine ⟨174883221429521535111637187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116588814286347690074424791 174883221429521535111637187)
    ·
      refine ⟨262324832144282302667455781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174883221429521535111637187 262324832144282302667455781)
      ·
        refine ⟨49185906027052931750147959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 262324832144282302667455781 49185906027052931750147959)
        ·
          refine ⟨73778859040579397625221939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49185906027052931750147959 73778859040579397625221939)
          ·
            refine ⟨110668288560869096437832909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73778859040579397625221939 110668288560869096437832909)
            ·
              refine ⟨41500608210325911164187341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110668288560869096437832909 41500608210325911164187341)
              ·
                refine ⟨15562728078872216686570253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41500608210325911164187341 15562728078872216686570253)
                ·
                  refine ⟨5836023029577081257463845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15562728078872216686570253 5836023029577081257463845)
                  ·
                    refine ⟨1094254318045702735774471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5836023029577081257463845 1094254318045702735774471)
                    ·
                      rfl

theorem cell22_3196579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 4].length) (baseStart_3196579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196579 prefixEnd_3196579 := by exact prefixLift 3196579
  have htrace : WordTrace (prefixWord ++ tailWord_3196579) baseStart_3196579 baseEnd_3196579 := by
    simpa [prefixWord, tailWord_3196579, baseEnd_3196579] using wordTrace_append hprefix tailTrace_3196579
  have hstable : (prefixWord ++ tailWord_3196579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196579).length < 2 ^ (prefixWord ++ tailWord_3196579).sum := by decide
  have hdescent : baseEnd_3196579 < baseStart_3196579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196598 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3196598 : Nat := 118140960795 + 3196598 * 2 ^ 59
def prefixEnd_3196598 : Nat := 4983230072969 + 3 ^ 40 * 3196598 * 2
def baseEnd_3196598 : Nat := 1094260822133993019549413

theorem tailTrace_3196598 : CollatzResearch.WordTrace tailWord_3196598 prefixEnd_3196598 1094260822133993019549413 := by
  unfold tailWord_3196598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286844204579928519960403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77726338182185904212910965 7286844204579928519960403)
  ·
    refine ⟨10930266306869892779940605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7286844204579928519960403 10930266306869892779940605)
    ·
      refine ⟨4098849865076209792477727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10930266306869892779940605 4098849865076209792477727)
      ·
        refine ⟨6148274797614314688716591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4098849865076209792477727 6148274797614314688716591)
        ·
          refine ⟨9222412196421472033074887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6148274797614314688716591 9222412196421472033074887)
          ·
            refine ⟨13833618294632208049612331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9222412196421472033074887 13833618294632208049612331)
            ·
              refine ⟨20750427441948312074418497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13833618294632208049612331 20750427441948312074418497)
              ·
                refine ⟨15562820581461234055813873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20750427441948312074418497 15562820581461234055813873)
                ·
                  refine ⟨11672115436095925541860405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15562820581461234055813873 11672115436095925541860405)
                  ·
                    refine ⟨1094260822133993019549413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11672115436095925541860405 1094260822133993019549413)
                    ·
                      rfl

theorem cell22_3196598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3196598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196598 prefixEnd_3196598 := by exact prefixLift 3196598
  have htrace : WordTrace (prefixWord ++ tailWord_3196598) baseStart_3196598 baseEnd_3196598 := by
    simpa [prefixWord, tailWord_3196598, baseEnd_3196598] using wordTrace_append hprefix tailTrace_3196598
  have hstable : (prefixWord ++ tailWord_3196598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196598).length < 2 ^ (prefixWord ++ tailWord_3196598).sum := by decide
  have hdescent : baseEnd_3196598 < baseStart_3196598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196624 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 6, 4]
def baseStart_3196624 : Nat := 118140960795 + 3196624 * 2 ^ 59
def prefixEnd_3196624 : Nat := 4983230072969 + 3 ^ 40 * 3196624 * 2
def baseEnd_3196624 : Nat := 1094269722465337618399333

theorem tailTrace_3196624 : CollatzResearch.WordTrace tailWord_3196624 prefixEnd_3196624 1094269722465337618399333 := by
  unfold tailWord_3196624
  simp only [CollatzResearch.WordTrace]
  refine ⟨58295227785592331379906463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77726970380789775173208617 58295227785592331379906463)
  ·
    refine ⟨87442841678388497069859695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58295227785592331379906463 87442841678388497069859695)
    ·
      refine ⟨131164262517582745604789543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87442841678388497069859695 131164262517582745604789543)
      ·
        refine ⟨196746393776374118407184315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131164262517582745604789543 196746393776374118407184315)
        ·
          refine ⟨295119590664561177610776473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196746393776374118407184315 295119590664561177610776473)
          ·
            refine ⟨221339692998420883208082355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295119590664561177610776473 221339692998420883208082355)
            ·
              refine ⟨332009539497631324812123533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221339692998420883208082355 332009539497631324812123533)
              ·
                refine ⟨124503577311611746804546325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332009539497631324812123533 124503577311611746804546325)
                ·
                  refine ⟨5836105186481800631463109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124503577311611746804546325 5836105186481800631463109)
                  ·
                    refine ⟨1094269722465337618399333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5836105186481800631463109 1094269722465337618399333)
                    ·
                      rfl

theorem cell22_3196624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_3196624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196624 prefixEnd_3196624 := by exact prefixLift 3196624
  have htrace : WordTrace (prefixWord ++ tailWord_3196624) baseStart_3196624 baseEnd_3196624 := by
    simpa [prefixWord, tailWord_3196624, baseEnd_3196624] using wordTrace_append hprefix tailTrace_3196624
  have hstable : (prefixWord ++ tailWord_3196624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196624).length < 2 ^ (prefixWord ++ tailWord_3196624).sum := by decide
  have hdescent : baseEnd_3196624 < baseStart_3196624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196639 : List Nat := [1, 1, 2, 3, 2, 2, 3, 8]
def baseStart_3196639 : Nat := 118140960795 + 3196639 * 2 ^ 59
def prefixEnd_3196639 : Nat := 4983230072969 + 3 ^ 40 * 3196639 * 2
def baseEnd_3196639 : Nat := 121586095252431397697143

theorem tailTrace_3196639 : CollatzResearch.WordTrace tailWord_3196639 prefixEnd_3196639 121586095252431397697143 := by
  unfold tailWord_3196639
  simp only [CollatzResearch.WordTrace]
  refine ⟨116591002666130320321608971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77727335110753546881072647 116591002666130320321608971)
  ·
    refine ⟨174886503999195480482413457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116591002666130320321608971 174886503999195480482413457)
    ·
      refine ⟨131164877999396610361810093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174886503999195480482413457 131164877999396610361810093)
      ·
        refine ⟨49186829249773728885678785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131164877999396610361810093 49186829249773728885678785)
        ·
          refine ⟨36890121937330296664259089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49186829249773728885678785 36890121937330296664259089)
          ·
            refine ⟨27667591452997722498194317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36890121937330296664259089 27667591452997722498194317)
            ·
              refine ⟨10375346794874145936822869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27667591452997722498194317 10375346794874145936822869)
              ·
                refine ⟨121586095252431397697143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10375346794874145936822869 121586095252431397697143)
                ·
                  rfl

theorem cell22_3196639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 8].length) (baseStart_3196639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196639 prefixEnd_3196639 := by exact prefixLift 3196639
  have htrace : WordTrace (prefixWord ++ tailWord_3196639) baseStart_3196639 baseEnd_3196639 := by
    simpa [prefixWord, tailWord_3196639, baseEnd_3196639] using wordTrace_append hprefix tailTrace_3196639
  have hstable : (prefixWord ++ tailWord_3196639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196639).length < 2 ^ (prefixWord ++ tailWord_3196639).sum := by decide
  have hdescent : baseEnd_3196639 < baseStart_3196639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196699 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 1, 7]
def baseStart_3196699 : Nat := 118140960795 + 3196699 * 2 ^ 59
def prefixEnd_3196699 : Nat := 4983230072969 + 3 ^ 40 * 3196699 * 2
def baseEnd_3196699 : Nat := 1094295396498062422774103

theorem tailTrace_3196699 : CollatzResearch.WordTrace tailWord_3196699 prefixEnd_3196699 1094295396498062422774103 := by
  unfold tailWord_3196699
  simp only [CollatzResearch.WordTrace]
  refine ⟨116593191045912950568793151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77728794030608633712528767 116593191045912950568793151)
  ·
    refine ⟨174889786568869425853189727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116593191045912950568793151 174889786568869425853189727)
    ·
      refine ⟨262334679853304138779784591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174889786568869425853189727 262334679853304138779784591)
      ·
        refine ⟨393502019779956208169676887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262334679853304138779784591 393502019779956208169676887)
        ·
          refine ⟨590253029669934312254515331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393502019779956208169676887 590253029669934312254515331)
          ·
            refine ⟨885379544504901468381772997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590253029669934312254515331 885379544504901468381772997)
            ·
              refine ⟨166008664594669025321582437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 885379544504901468381772997 166008664594669025321582437)
              ·
                refine ⟨31126624611500442247796707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166008664594669025321582437 31126624611500442247796707)
                ·
                  refine ⟨46689936917250663371695061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31126624611500442247796707 46689936917250663371695061)
                  ·
                    refine ⟨1094295396498062422774103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46689936917250663371695061 1094295396498062422774103)
                    ·
                      rfl

theorem cell22_3196699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_3196699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196699 prefixEnd_3196699 := by exact prefixLift 3196699
  have htrace : WordTrace (prefixWord ++ tailWord_3196699) baseStart_3196699 baseEnd_3196699 := by
    simpa [prefixWord, tailWord_3196699, baseEnd_3196699] using wordTrace_append hprefix tailTrace_3196699
  have hstable : (prefixWord ++ tailWord_3196699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196699).length < 2 ^ (prefixWord ++ tailWord_3196699).sum := by decide
  have hdescent : baseEnd_3196699 < baseStart_3196699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196722 : List Nat := [3, 2, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_3196722 : Nat := 118140960795 + 3196722 * 2 ^ 59
def prefixEnd_3196722 : Nat := 4983230072969 + 3 ^ 40 * 3196722 * 2
def baseEnd_3196722 : Nat := 1094303269868098029449033

theorem tailTrace_3196722 : CollatzResearch.WordTrace tailWord_3196722 prefixEnd_3196722 1094303269868098029449033 := by
  unfold tailWord_3196722
  simp only [CollatzResearch.WordTrace]
  refine ⟨29148507481207406374220105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77729353283219750331253613 29148507481207406374220105)
  ·
    refine ⟨21861380610905554780665079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29148507481207406374220105 21861380610905554780665079)
    ·
      refine ⟨32792070916358332170997619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21861380610905554780665079 32792070916358332170997619)
      ·
        refine ⟨49188106374537498256496429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32792070916358332170997619 49188106374537498256496429)
        ·
          refine ⟨18445539890451561846186161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49188106374537498256496429 18445539890451561846186161)
          ·
            refine ⟨13834154917838671384639621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18445539890451561846186161 13834154917838671384639621)
            ·
              refine ⟨2593904047094750884619929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13834154917838671384639621 2593904047094750884619929)
              ·
                refine ⟨1945428035321063163464947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2593904047094750884619929 1945428035321063163464947)
                ·
                  refine ⟨2918142052981594745197421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945428035321063163464947 2918142052981594745197421)
                  ·
                    refine ⟨1094303269868098029449033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2918142052981594745197421 1094303269868098029449033)
                    ·
                      rfl

theorem cell22_3196722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_3196722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196722 prefixEnd_3196722 := by exact prefixLift 3196722
  have htrace : WordTrace (prefixWord ++ tailWord_3196722) baseStart_3196722 baseEnd_3196722 := by
    simpa [prefixWord, tailWord_3196722, baseEnd_3196722] using wordTrace_append hprefix tailTrace_3196722
  have hstable : (prefixWord ++ tailWord_3196722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196722).length < 2 ^ (prefixWord ++ tailWord_3196722).sum := by decide
  have hdescent : baseEnd_3196722 < baseStart_3196722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196733 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_3196733 : Nat := 118140960795 + 3196733 * 2 ^ 59
def prefixEnd_3196733 : Nat := 4983230072969 + 3 ^ 40 * 3196733 * 2
def baseEnd_3196733 : Nat := 1094307035392897667423999

theorem tailTrace_3196733 : CollatzResearch.WordTrace tailWord_3196733 prefixEnd_3196733 1094307035392897667423999 := by
  unfold tailWord_3196733
  simp only [CollatzResearch.WordTrace]
  refine ⟨116594431127789774375530853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77729620751859849583687235 116594431127789774375530853)
  ·
    refine ⟨21861455836460582695412035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116594431127789774375530853 21861455836460582695412035)
    ·
      refine ⟨32792183754690874043118053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21861455836460582695412035 32792183754690874043118053)
      ·
        refine ⟨6148534454004538883084635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32792183754690874043118053 6148534454004538883084635)
        ·
          refine ⟨9222801681006808324626953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6148534454004538883084635 9222801681006808324626953)
          ·
            refine ⟨6917101260755106243470215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9222801681006808324626953 6917101260755106243470215)
            ·
              refine ⟨10375651891132659365205323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6917101260755106243470215 10375651891132659365205323)
              ·
                refine ⟨15563477836698989047807985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10375651891132659365205323 15563477836698989047807985)
                ·
                  refine ⟨11672608377524241785855989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15563477836698989047807985 11672608377524241785855989)
                  ·
                    refine ⟨1094307035392897667423999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11672608377524241785855989 1094307035392897667423999)
                    ·
                      rfl

theorem cell22_3196733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_3196733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196733 prefixEnd_3196733 := by exact prefixLift 3196733
  have htrace : WordTrace (prefixWord ++ tailWord_3196733) baseStart_3196733 baseEnd_3196733 := by
    simpa [prefixWord, tailWord_3196733, baseEnd_3196733] using wordTrace_append hprefix tailTrace_3196733
  have hstable : (prefixWord ++ tailWord_3196733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196733).length < 2 ^ (prefixWord ++ tailWord_3196733).sum := by decide
  have hdescent : baseEnd_3196733 < baseStart_3196733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196746 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 6]
def baseStart_3196746 : Nat := 118140960795 + 3196746 * 2 ^ 59
def prefixEnd_3196746 : Nat := 4983230072969 + 3 ^ 40 * 3196746 * 2
def baseEnd_3196746 : Nat := 364770495186189988949653

theorem tailTrace_3196746 : CollatzResearch.WordTrace tailWord_3196746 prefixEnd_3196746 364770495186189988949653 := by
  unfold tailWord_3196746
  simp only [CollatzResearch.WordTrace]
  refine ⟨29148726319185669398938523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77729936851161785063836061 29148726319185669398938523)
  ·
    refine ⟨43723089478778504098407785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29148726319185669398938523 43723089478778504098407785)
    ·
      refine ⟨32792317109083878073805839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43723089478778504098407785 32792317109083878073805839)
      ·
        refine ⟨49188475663625817110708759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32792317109083878073805839 49188475663625817110708759)
        ·
          refine ⟨73782713495438725666063139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49188475663625817110708759 73782713495438725666063139)
          ·
            refine ⟨110674070243158088499094709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73782713495438725666063139 110674070243158088499094709)
            ·
              refine ⟨10375694085296070796790129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110674070243158088499094709 10375694085296070796790129)
              ·
                refine ⟨7781770563972053097592597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10375694085296070796790129 7781770563972053097592597)
                ·
                  refine ⟨364770495186189988949653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7781770563972053097592597 364770495186189988949653)
                  ·
                    rfl

theorem cell22_3196746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_3196746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196746 prefixEnd_3196746 := by exact prefixLift 3196746
  have htrace : WordTrace (prefixWord ++ tailWord_3196746) baseStart_3196746 baseEnd_3196746 := by
    simpa [prefixWord, tailWord_3196746, baseEnd_3196746] using wordTrace_append hprefix tailTrace_3196746
  have hstable : (prefixWord ++ tailWord_3196746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196746).length < 2 ^ (prefixWord ++ tailWord_3196746).sum := by decide
  have hdescent : baseEnd_3196746 < baseStart_3196746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196761 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 1, 5]
def baseStart_3196761 : Nat := 118140960795 + 3196761 * 2 ^ 59
def prefixEnd_3196761 : Nat := 4983230072969 + 3 ^ 40 * 3196761 * 2
def baseEnd_3196761 : Nat := 1094316620365114927723913

theorem tailTrace_3196761 : CollatzResearch.WordTrace tailWord_3196761 prefixEnd_3196761 1094316620365114927723913 := by
  unfold tailWord_3196761
  simp only [CollatzResearch.WordTrace]
  refine ⟨116595452371688335157550137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77730301581125556771700091 116595452371688335157550137)
  ·
    refine ⟨87446589278766251368162603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116595452371688335157550137 87446589278766251368162603)
    ·
      refine ⟨131169883918149377052243905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87446589278766251368162603 131169883918149377052243905)
      ·
        refine ⟨98377412938612032789182929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131169883918149377052243905 98377412938612032789182929)
        ·
          refine ⟨73783059703959024591887197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98377412938612032789182929 73783059703959024591887197)
          ·
            refine ⟨27668647388984634221957699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73783059703959024591887197 27668647388984634221957699)
            ·
              refine ⟨41502971083476951332936549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27668647388984634221957699 41502971083476951332936549)
              ·
                refine ⟨7781807078151928374925603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41502971083476951332936549 7781807078151928374925603)
                ·
                  refine ⟨11672710617227892562388405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7781807078151928374925603 11672710617227892562388405)
                  ·
                    refine ⟨1094316620365114927723913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11672710617227892562388405 1094316620365114927723913)
                    ·
                      rfl

theorem cell22_3196761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_3196761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196761 prefixEnd_3196761 := by exact prefixLift 3196761
  have htrace : WordTrace (prefixWord ++ tailWord_3196761) baseStart_3196761 baseEnd_3196761 := by
    simpa [prefixWord, tailWord_3196761, baseEnd_3196761] using wordTrace_append hprefix tailTrace_3196761
  have hstable : (prefixWord ++ tailWord_3196761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196761).length < 2 ^ (prefixWord ++ tailWord_3196761).sum := by decide
  have hdescent : baseEnd_3196761 < baseStart_3196761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196808 : List Nat := [2, 1, 3, 3, 3, 1, 1, 8]
def baseStart_3196808 : Nat := 118140960795 + 3196808 * 2 ^ 59
def prefixEnd_3196808 : Nat := 4983230072969 + 3 ^ 40 * 3196808 * 2
def baseEnd_3196808 : Nat := 121592523269513607977641

theorem tailTrace_3196808 : CollatzResearch.WordTrace tailWord_3196808 prefixEnd_3196808 121592523269513607977641 := by
  unfold tailWord_3196808
  simp only [CollatzResearch.WordTrace]
  refine ⟨58298583301259031092255539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77731444401678708123007385 58298583301259031092255539)
  ·
    refine ⟨87447874951888546638383309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58298583301259031092255539 87447874951888546638383309)
    ·
      refine ⟨32792953106958204989393741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87447874951888546638383309 32792953106958204989393741)
      ·
        refine ⟨12297357415109326871022653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32792953106958204989393741 12297357415109326871022653)
        ·
          refine ⟨4611509030665997576633495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12297357415109326871022653 4611509030665997576633495)
          ·
            refine ⟨6917263545998996364950243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611509030665997576633495 6917263545998996364950243)
            ·
              refine ⟨10375895318998494547425365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6917263545998996364950243 10375895318998494547425365)
              ·
                refine ⟨121592523269513607977641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10375895318998494547425365 121592523269513607977641)
                ·
                  rfl

theorem cell22_3196808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 8].length) (baseStart_3196808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196808 prefixEnd_3196808 := by exact prefixLift 3196808
  have htrace : WordTrace (prefixWord ++ tailWord_3196808) baseStart_3196808 baseEnd_3196808 := by
    simpa [prefixWord, tailWord_3196808, baseEnd_3196808] using wordTrace_append hprefix tailTrace_3196808
  have hstable : (prefixWord ++ tailWord_3196808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196808).length < 2 ^ (prefixWord ++ tailWord_3196808).sum := by decide
  have hdescent : baseEnd_3196808 < baseStart_3196808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196814 : List Nat := [4, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_3196814 : Nat := 118140960795 + 3196814 * 2 ^ 59
def prefixEnd_3196814 : Nat := 4983230072969 + 3 ^ 40 * 3196814 * 2
def baseEnd_3196814 : Nat := 364778254449413485382917

theorem tailTrace_3196814 : CollatzResearch.WordTrace tailWord_3196814 prefixEnd_3196814 364778254449413485382917 := by
  unfold tailWord_3196814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14574673180062040651153687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77731590293664216806152997 14574673180062040651153687)
  ·
    refine ⟨21862009770093060976730531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14574673180062040651153687 21862009770093060976730531)
    ·
      refine ⟨32793014655139591465095797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21862009770093060976730531 32793014655139591465095797)
      ·
        refine ⟨3074345123919336699852731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32793014655139591465095797 3074345123919336699852731)
        ·
          refine ⟨4611517685879005049779097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3074345123919336699852731 4611517685879005049779097)
          ·
            refine ⟨3458638264409253787334323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4611517685879005049779097 3458638264409253787334323)
            ·
              refine ⟨5187957396613880681001485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458638264409253787334323 5187957396613880681001485)
              ·
                refine ⟨1945484023730205255375557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5187957396613880681001485 1945484023730205255375557)
                ·
                  refine ⟨364778254449413485382917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1945484023730205255375557 364778254449413485382917)
                  ·
                    rfl

theorem cell22_3196814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_3196814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196814 prefixEnd_3196814 := by exact prefixLift 3196814
  have htrace : WordTrace (prefixWord ++ tailWord_3196814) baseStart_3196814 baseEnd_3196814 := by
    simpa [prefixWord, tailWord_3196814, baseEnd_3196814] using wordTrace_append hprefix tailTrace_3196814
  have hstable : (prefixWord ++ tailWord_3196814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196814).length < 2 ^ (prefixWord ++ tailWord_3196814).sum := by decide
  have hdescent : baseEnd_3196814 < baseStart_3196814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196846 : List Nat := [4, 1, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3196846 : Nat := 118140960795 + 3196846 * 2 ^ 59
def prefixEnd_3196846 : Nat := 4983230072969 + 3 ^ 40 * 3196846 * 2
def baseEnd_3196846 : Nat := 1094345717602203039348653

theorem tailTrace_3196846 : CollatzResearch.WordTrace tailWord_3196846 prefixEnd_3196846 1094345717602203039348653 := by
  unfold tailWord_3196846
  simp only [CollatzResearch.WordTrace]
  refine ⟨14574819072047549334299299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77732368384253596449596261 14574819072047549334299299)
  ·
    refine ⟨21862228608071324001448949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14574819072047549334299299 21862228608071324001448949)
    ·
      refine ⟨2049583932006686625135839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21862228608071324001448949 2049583932006686625135839)
      ·
        refine ⟨3074375898010029937703759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049583932006686625135839 3074375898010029937703759)
        ·
          refine ⟨4611563847015044906555639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3074375898010029937703759 4611563847015044906555639)
          ·
            refine ⟨6917345770522567359833459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611563847015044906555639 6917345770522567359833459)
            ·
              refine ⟨10376018655783851039750189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6917345770522567359833459 10376018655783851039750189)
              ·
                refine ⟨3891006995918944139906321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10376018655783851039750189 3891006995918944139906321)
                ·
                  refine ⟨2918255246939208104929741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3891006995918944139906321 2918255246939208104929741)
                  ·
                    refine ⟨1094345717602203039348653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2918255246939208104929741 1094345717602203039348653)
                    ·
                      rfl

theorem cell22_3196846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3196846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196846 prefixEnd_3196846 := by exact prefixLift 3196846
  have htrace : WordTrace (prefixWord ++ tailWord_3196846) baseStart_3196846 baseEnd_3196846 := by
    simpa [prefixWord, tailWord_3196846, baseEnd_3196846] using wordTrace_append hprefix tailTrace_3196846
  have hstable : (prefixWord ++ tailWord_3196846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196846).length < 2 ^ (prefixWord ++ tailWord_3196846).sum := by decide
  have hdescent : baseEnd_3196846 < baseStart_3196846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196851 : List Nat := [1, 1, 1, 2, 3, 1, 4, 1, 1, 7]
def baseStart_3196851 : Nat := 118140960795 + 3196851 * 2 ^ 59
def prefixEnd_3196851 : Nat := 4983230072969 + 3 ^ 40 * 3196851 * 2
def baseEnd_3196851 : Nat := 1094347429204384692973637

theorem tailTrace_3196851 : CollatzResearch.WordTrace tailWord_3196851 prefixEnd_3196851 1094347429204384692973637 := by
  unfold tailWord_3196851
  simp only [CollatzResearch.WordTrace]
  refine ⟨116598734941362280528326407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77732489960908187018884271 116598734941362280528326407)
  ·
    refine ⟨174898102412043420792489611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116598734941362280528326407 174898102412043420792489611)
    ·
      refine ⟨262347153618065131188734417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174898102412043420792489611 262347153618065131188734417)
      ·
        refine ⟨196760365213548848391550813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262347153618065131188734417 196760365213548848391550813)
        ·
          refine ⟨73785136955080818146831555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196760365213548848391550813 73785136955080818146831555)
          ·
            refine ⟨110677705432621227220247333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73785136955080818146831555 110677705432621227220247333)
            ·
              refine ⟨20752069768616480103796375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110677705432621227220247333 20752069768616480103796375)
              ·
                refine ⟨31128104652924720155694563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20752069768616480103796375 31128104652924720155694563)
                ·
                  refine ⟨46692156979387080233541845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31128104652924720155694563 46692156979387080233541845)
                  ·
                    refine ⟨1094347429204384692973637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46692156979387080233541845 1094347429204384692973637)
                    ·
                      rfl

theorem cell22_3196851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_3196851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196851 prefixEnd_3196851 := by exact prefixLift 3196851
  have htrace : WordTrace (prefixWord ++ tailWord_3196851) baseStart_3196851 baseEnd_3196851 := by
    simpa [prefixWord, tailWord_3196851, baseEnd_3196851] using wordTrace_append hprefix tailTrace_3196851
  have hstable : (prefixWord ++ tailWord_3196851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196851).length < 2 ^ (prefixWord ++ tailWord_3196851).sum := by decide
  have hdescent : baseEnd_3196851 < baseStart_3196851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196881 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 10]
def baseStart_3196881 : Nat := 118140960795 + 3196881 * 2 ^ 59
def prefixEnd_3196881 : Nat := 4983230072969 + 3 ^ 40 * 3196881 * 2
def baseEnd_3196881 : Nat := 364785899605824871574515

theorem tailTrace_3196881 : CollatzResearch.WordTrace tailWord_3196881 prefixEnd_3196881 364785899605824871574515 := by
  unfold tailWord_3196881
  simp only [CollatzResearch.WordTrace]
  refine ⟨116599829131253595651918497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77733219420835730434612331 116599829131253595651918497)
  ·
    refine ⟨87449871848440196738938873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116599829131253595651918497 87449871848440196738938873)
    ·
      refine ⟨65587403886330147554204155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87449871848440196738938873 65587403886330147554204155)
      ·
        refine ⟨98381105829495221331306233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65587403886330147554204155 98381105829495221331306233)
        ·
          refine ⟨73785829372121415998479675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98381105829495221331306233 73785829372121415998479675)
          ·
            refine ⟨110678744058182123997719513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73785829372121415998479675 110678744058182123997719513)
            ·
              refine ⟨83009058043636592998289635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110678744058182123997719513 83009058043636592998289635)
              ·
                refine ⟨124513587065454889497434453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83009058043636592998289635 124513587065454889497434453)
                ·
                  refine ⟨364785899605824871574515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 124513587065454889497434453 364785899605824871574515)
                  ·
                    rfl

theorem cell22_3196881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_3196881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196881 prefixEnd_3196881 := by exact prefixLift 3196881
  have htrace : WordTrace (prefixWord ++ tailWord_3196881) baseStart_3196881 baseEnd_3196881 := by
    simpa [prefixWord, tailWord_3196881, baseEnd_3196881] using wordTrace_append hprefix tailTrace_3196881
  have hstable : (prefixWord ++ tailWord_3196881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196881).length < 2 ^ (prefixWord ++ tailWord_3196881).sum := by decide
  have hdescent : baseEnd_3196881 < baseStart_3196881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196928 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 2, 4]
def baseStart_3196928 : Nat := 118140960795 + 3196928 * 2 ^ 59
def prefixEnd_3196928 : Nat := 4983230072969 + 3 ^ 40 * 3196928 * 2
def baseEnd_3196928 : Nat := 1094373787877982158798401

theorem tailTrace_3196928 : CollatzResearch.WordTrace tailWord_3196928 prefixEnd_3196928 1094373787877982158798401 := by
  unfold tailWord_3196928
  simp only [CollatzResearch.WordTrace]
  refine ⟨58300771681041661339439719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77734362241388881785919625 58300771681041661339439719)
  ·
    refine ⟨87451157521562492009159579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58300771681041661339439719 87451157521562492009159579)
    ·
      refine ⟨131176736282343738013739369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87451157521562492009159579 131176736282343738013739369)
      ·
        refine ⟨98382552211757803510304527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131176736282343738013739369 98382552211757803510304527)
        ·
          refine ⟨147573828317636705265456791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98382552211757803510304527 147573828317636705265456791)
          ·
            refine ⟨221360742476455057898185187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147573828317636705265456791 221360742476455057898185187)
            ·
              refine ⟨332041113714682586847277781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221360742476455057898185187 332041113714682586847277781)
              ·
                refine ⟨7782213602687873129233073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 332041113714682586847277781 7782213602687873129233073)
                ·
                  refine ⟨5836660202015904846924805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7782213602687873129233073 5836660202015904846924805)
                  ·
                    refine ⟨1094373787877982158798401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5836660202015904846924805 1094373787877982158798401)
                    ·
                      rfl

theorem cell22_3196928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_3196928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196928 prefixEnd_3196928 := by exact prefixLift 3196928
  have htrace : WordTrace (prefixWord ++ tailWord_3196928) baseStart_3196928 baseEnd_3196928 := by
    simpa [prefixWord, tailWord_3196928, baseEnd_3196928] using wordTrace_append hprefix tailTrace_3196928
  have hstable : (prefixWord ++ tailWord_3196928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196928).length < 2 ^ (prefixWord ++ tailWord_3196928).sum := by decide
  have hdescent : baseEnd_3196928 < baseStart_3196928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196964 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_3196964 : Nat := 118140960795 + 3196964 * 2 ^ 59
def prefixEnd_3196964 : Nat := 4983230072969 + 3 ^ 40 * 3196964 * 2
def baseEnd_3196964 : Nat := 1094386111413690064898291

theorem tailTrace_3196964 : CollatzResearch.WordTrace tailWord_3196964 prefixEnd_3196964 1094386111413690064898291 := by
  unfold tailWord_3196964
  simp only [CollatzResearch.WordTrace]
  refine ⟨58301428194976450413594973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77735237593301933884793297 58301428194976450413594973)
  ·
    refine ⟨21863035573116168905098115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58301428194976450413594973 21863035573116168905098115)
    ·
      refine ⟨32794553359674253357647173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21863035573116168905098115 32794553359674253357647173)
      ·
        refine ⟨6148978754938922504558845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32794553359674253357647173 6148978754938922504558845)
        ·
          refine ⟨2305867033102095939209567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6148978754938922504558845 2305867033102095939209567)
          ·
            refine ⟨3458800549653143908814351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305867033102095939209567 3458800549653143908814351)
            ·
              refine ⟨5188200824479715863221527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458800549653143908814351 5188200824479715863221527)
              ·
                refine ⟨7782301236719573794832291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5188200824479715863221527 7782301236719573794832291)
                ·
                  refine ⟨11673451855079360692248437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7782301236719573794832291 11673451855079360692248437)
                  ·
                    refine ⟨1094386111413690064898291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11673451855079360692248437 1094386111413690064898291)
                    ·
                      rfl

theorem cell22_3196964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_3196964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196964 prefixEnd_3196964 := by exact prefixLift 3196964
  have htrace : WordTrace (prefixWord ++ tailWord_3196964) baseStart_3196964 baseEnd_3196964 := by
    simpa [prefixWord, tailWord_3196964, baseEnd_3196964] using wordTrace_append hprefix tailTrace_3196964
  have hstable : (prefixWord ++ tailWord_3196964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196964).length < 2 ^ (prefixWord ++ tailWord_3196964).sum := by decide
  have hdescent : baseEnd_3196964 < baseStart_3196964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3196988 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 9]
def baseStart_3196988 : Nat := 118140960795 + 3196988 * 2 ^ 59
def prefixEnd_3196988 : Nat := 4983230072969 + 3 ^ 40 * 3196988 * 2
def baseEnd_3196988 : Nat := 364798109034720667432739

theorem tailTrace_3196988 : CollatzResearch.WordTrace tailWord_3196988 prefixEnd_3196988 364798109034720667432739 := by
  unfold tailWord_3196988
  simp only [CollatzResearch.WordTrace]
  refine ⟨58301865870932976463031809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77735821161243968617375745 58301865870932976463031809)
  ·
    refine ⟨43726399403199732347273857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58301865870932976463031809 43726399403199732347273857)
    ·
      refine ⟨32794799552399799260455393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43726399403199732347273857 32794799552399799260455393)
      ·
        refine ⟨24596099664299849445341545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32794799552399799260455393 24596099664299849445341545)
        ·
          refine ⟨18447074748224887084006159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24596099664299849445341545 18447074748224887084006159)
          ·
            refine ⟨27670612122337330626009239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18447074748224887084006159 27670612122337330626009239)
            ·
              refine ⟨41505918183505995939013859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27670612122337330626009239 41505918183505995939013859)
              ·
                refine ⟨62258877275258993908520789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41505918183505995939013859 62258877275258993908520789)
                ·
                  refine ⟨364798109034720667432739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62258877275258993908520789 364798109034720667432739)
                  ·
                    rfl

theorem cell22_3196988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_3196988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3196988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3196988 prefixEnd_3196988 := by exact prefixLift 3196988
  have htrace : WordTrace (prefixWord ++ tailWord_3196988) baseStart_3196988 baseEnd_3196988 := by
    simpa [prefixWord, tailWord_3196988, baseEnd_3196988] using wordTrace_append hprefix tailTrace_3196988
  have hstable : (prefixWord ++ tailWord_3196988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3196988).length < 2 ^ (prefixWord ++ tailWord_3196988).sum := by decide
  have hdescent : baseEnd_3196988 < baseStart_3196988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3196988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197005 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 7]
def baseStart_3197005 : Nat := 118140960795 + 3197005 * 2 ^ 59
def prefixEnd_3197005 : Nat := 4983230072969 + 3 ^ 40 * 3197005 * 2
def baseEnd_3197005 : Nat := 364800048850526541541055

theorem tailTrace_3197005 : CollatzResearch.WordTrace tailWord_3197005 prefixEnd_3197005 364800048850526541541055 := by
  unfold tailWord_3197005
  simp only [CollatzResearch.WordTrace]
  refine ⟨116604351782804364829432469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77736234521869576552954979 116604351782804364829432469)
  ·
    refine ⟨5465828989818954601379647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116604351782804364829432469 5465828989818954601379647)
    ·
      refine ⟨8198743484728431902069471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5465828989818954601379647 8198743484728431902069471)
      ·
        refine ⟨12298115227092647853104207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8198743484728431902069471 12298115227092647853104207)
        ·
          refine ⟨18447172840638971779656311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12298115227092647853104207 18447172840638971779656311)
          ·
            refine ⟨27670759260958457669484467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18447172840638971779656311 27670759260958457669484467)
            ·
              refine ⟨41506138891437686504226701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27670759260958457669484467 41506138891437686504226701)
              ·
                refine ⟨15564802084289132439085013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41506138891437686504226701 15564802084289132439085013)
                ·
                  refine ⟨364800048850526541541055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15564802084289132439085013 364800048850526541541055)
                  ·
                    rfl

theorem cell22_3197005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_3197005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197005 prefixEnd_3197005 := by exact prefixLift 3197005
  have htrace : WordTrace (prefixWord ++ tailWord_3197005) baseStart_3197005 baseEnd_3197005 := by
    simpa [prefixWord, tailWord_3197005, baseEnd_3197005] using wordTrace_append hprefix tailTrace_3197005
  have hstable : (prefixWord ++ tailWord_3197005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197005).length < 2 ^ (prefixWord ++ tailWord_3197005).sum := by decide
  have hdescent : baseEnd_3197005 < baseStart_3197005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197033 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 8]
def baseStart_3197033 : Nat := 118140960795 + 3197033 * 2 ^ 59
def prefixEnd_3197033 : Nat := 4983230072969 + 3 ^ 40 * 3197033 * 2
def baseEnd_3197033 : Nat := 364803243841265628307693

theorem tailTrace_3197033 : CollatzResearch.WordTrace tailWord_3197033 prefixEnd_3197033 364803243841265628307693 := by
  unfold tailWord_3197033
  simp only [CollatzResearch.WordTrace]
  refine ⟨116605373026702925611451753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77736915351135283740967835 116605373026702925611451753)
  ·
    refine ⟨87454029770027194208588815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116605373026702925611451753 87454029770027194208588815)
    ·
      refine ⟨131181044655040791312883223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87454029770027194208588815 131181044655040791312883223)
      ·
        refine ⟨196771566982561186969324835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131181044655040791312883223 196771566982561186969324835)
        ·
          refine ⟨295157350473841780453987253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196771566982561186969324835 295157350473841780453987253)
          ·
            refine ⟨27671001606922666917561305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295157350473841780453987253 27671001606922666917561305)
            ·
              refine ⟨20753251205192000188170979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27671001606922666917561305 20753251205192000188170979)
              ·
                refine ⟨31129876807788000282256469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20753251205192000188170979 31129876807788000282256469)
                ·
                  refine ⟨364803243841265628307693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31129876807788000282256469 364803243841265628307693)
                  ·
                    rfl

theorem cell22_3197033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_3197033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197033 prefixEnd_3197033 := by exact prefixLift 3197033
  have htrace : WordTrace (prefixWord ++ tailWord_3197033) baseStart_3197033 baseEnd_3197033 := by
    simpa [prefixWord, tailWord_3197033, baseEnd_3197033] using wordTrace_append hprefix tailTrace_3197033
  have hstable : (prefixWord ++ tailWord_3197033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197033).length < 2 ^ (prefixWord ++ tailWord_3197033).sum := by decide
  have hdescent : baseEnd_3197033 < baseStart_3197033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197116 : List Nat := [2, 2, 2, 3, 3, 2, 1, 2, 2, 3]
def baseStart_3197116 : Nat := 118140960795 + 3197116 * 2 ^ 59
def prefixEnd_3197116 : Nat := 4983230072969 + 3 ^ 40 * 3197116 * 2
def baseEnd_3197116 : Nat := 1094438144120012335097825

theorem tailTrace_3197116 : CollatzResearch.WordTrace tailWord_3197116 prefixEnd_3197116 1094438144120012335097825 := by
  unfold tailWord_3197116
  simp only [CollatzResearch.WordTrace]
  refine ⟨58304200142701115393361601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77738933523601487191148801 58304200142701115393361601)
  ·
    refine ⟨43728150107025836545021201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58304200142701115393361601 43728150107025836545021201)
    ·
      refine ⟨32796112580269377408765901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43728150107025836545021201 32796112580269377408765901)
      ·
        refine ⟨12298542217601016528287213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32796112580269377408765901 12298542217601016528287213)
        ·
          refine ⟨4611953331600381198107705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12298542217601016528287213 4611953331600381198107705)
          ·
            refine ⟨3458964998700285898580779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4611953331600381198107705 3458964998700285898580779)
            ·
              refine ⟨5188447498050428847871169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458964998700285898580779 5188447498050428847871169)
              ·
                refine ⟨3891335623537821635903377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5188447498050428847871169 3891335623537821635903377)
                ·
                  refine ⟨2918501717653366226927533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3891335623537821635903377 2918501717653366226927533)
                  ·
                    refine ⟨1094438144120012335097825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2918501717653366226927533 1094438144120012335097825)
                    ·
                      rfl

theorem cell22_3197116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_3197116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197116 prefixEnd_3197116 := by exact prefixLift 3197116
  have htrace : WordTrace (prefixWord ++ tailWord_3197116) baseStart_3197116 baseEnd_3197116 := by
    simpa [prefixWord, tailWord_3197116, baseEnd_3197116] using wordTrace_append hprefix tailTrace_3197116
  have hstable : (prefixWord ++ tailWord_3197116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197116).length < 2 ^ (prefixWord ++ tailWord_3197116).sum := by decide
  have hdescent : baseEnd_3197116 < baseStart_3197116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197217 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 6, 3]
def baseStart_3197217 : Nat := 118140960795 + 3197217 * 2 ^ 59
def prefixEnd_3197217 : Nat := 4983230072969 + 3 ^ 40 * 3197217 * 2
def baseEnd_3197217 : Nat := 1094472718484081738322515

theorem tailTrace_3197217 : CollatzResearch.WordTrace tailWord_3197217 prefixEnd_3197217 1094472718484081738322515 := by
  unfold tailWord_3197217
  simp only [CollatzResearch.WordTrace]
  refine ⟨116612084058036325036149905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77741389372024216690766603 116612084058036325036149905)
  ·
    refine ⟨87459063043527243777112429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116612084058036325036149905 87459063043527243777112429)
    ·
      refine ⟨32797148641322716416417161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87459063043527243777112429 32797148641322716416417161)
      ·
        refine ⟨24597861480992037312312871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32797148641322716416417161 24597861480992037312312871)
        ·
          refine ⟨36896792221488055968469307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24597861480992037312312871 36896792221488055968469307)
          ·
            refine ⟨55345188332232083952703961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36896792221488055968469307 55345188332232083952703961)
            ·
              refine ⟨41508891249174062964527971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55345188332232083952703961 41508891249174062964527971)
              ·
                refine ⟨62263336873761094446791957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41508891249174062964527971 62263336873761094446791957)
                ·
                  refine ⟨2918593915957551302193373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62263336873761094446791957 2918593915957551302193373)
                  ·
                    refine ⟨1094472718484081738322515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2918593915957551302193373 1094472718484081738322515)
                    ·
                      rfl

theorem cell22_3197217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_3197217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197217 prefixEnd_3197217 := by exact prefixLift 3197217
  have htrace : WordTrace (prefixWord ++ tailWord_3197217) baseStart_3197217 baseEnd_3197217 := by
    simpa [prefixWord, tailWord_3197217, baseEnd_3197217] using wordTrace_append hprefix tailTrace_3197217
  have hstable : (prefixWord ++ tailWord_3197217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197217).length < 2 ^ (prefixWord ++ tailWord_3197217).sum := by decide
  have hdescent : baseEnd_3197217 < baseStart_3197217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197221 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 1, 4]
def baseStart_3197221 : Nat := 118140960795 + 3197221 * 2 ^ 59
def prefixEnd_3197221 : Nat := 4983230072969 + 3 ^ 40 * 3197221 * 2
def baseEnd_3197221 : Nat := 1094474087765827061222503

theorem tailTrace_3197221 : CollatzResearch.WordTrace tailWord_3197221 prefixEnd_3197221 1094474087765827061222503 := by
  unfold tailWord_3197221
  simp only [CollatzResearch.WordTrace]
  refine ⟨116612229950021833719295517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77741486633347889146197011 116612229950021833719295517)
  ·
    refine ⟨43729586231258187644735819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116612229950021833719295517 43729586231258187644735819)
    ·
      refine ⟨65594379346887281467103729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43729586231258187644735819 65594379346887281467103729)
      ·
        refine ⟨49195784510165461100327797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65594379346887281467103729 49195784510165461100327797)
        ·
          refine ⟨4612104797828011978155731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49195784510165461100327797 4612104797828011978155731)
          ·
            refine ⟨6918157196742017967233597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612104797828011978155731 6918157196742017967233597)
            ·
              refine ⟨2594308948778256737712599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6918157196742017967233597 2594308948778256737712599)
              ·
                refine ⟨3891463423167385106568899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594308948778256737712599 3891463423167385106568899)
                ·
                  refine ⟨5837195134751077659853349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891463423167385106568899 5837195134751077659853349)
                  ·
                    refine ⟨1094474087765827061222503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5837195134751077659853349 1094474087765827061222503)
                    ·
                      rfl

theorem cell22_3197221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 1, 4].length) (baseStart_3197221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197221 prefixEnd_3197221 := by exact prefixLift 3197221
  have htrace : WordTrace (prefixWord ++ tailWord_3197221) baseStart_3197221 baseEnd_3197221 := by
    simpa [prefixWord, tailWord_3197221, baseEnd_3197221] using wordTrace_append hprefix tailTrace_3197221
  have hstable : (prefixWord ++ tailWord_3197221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197221).length < 2 ^ (prefixWord ++ tailWord_3197221).sum := by decide
  have hdescent : baseEnd_3197221 < baseStart_3197221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197236 : List Nat := [2, 5, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3197236 : Nat := 118140960795 + 3197236 * 2 ^ 59
def prefixEnd_3197236 : Nat := 4983230072969 + 3 ^ 40 * 3197236 * 2
def baseEnd_3197236 : Nat := 364826407524124007365819

theorem tailTrace_3197236 : CollatzResearch.WordTrace tailWord_3197236 prefixEnd_3197236 364826407524124007365819 := by
  unfold tailWord_3197236
  simp only [CollatzResearch.WordTrace]
  refine ⟨58306388522483745640545781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77741851363311660854061041 58306388522483745640545781)
  ·
    refine ⟨5466223923982851153801167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58306388522483745640545781 5466223923982851153801167)
    ·
      refine ⟨8199335885974276730701751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5466223923982851153801167 8199335885974276730701751)
      ·
        refine ⟨12299003828961415096052627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8199335885974276730701751 12299003828961415096052627)
        ·
          refine ⟨18448505743442122644078941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12299003828961415096052627 18448505743442122644078941)
          ·
            refine ⟨6918189653790795991529603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18448505743442122644078941 6918189653790795991529603)
            ·
              refine ⟨10377284480686193987294405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6918189653790795991529603 10377284480686193987294405)
              ·
                refine ⟨1945740840128661372617701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10377284480686193987294405 1945740840128661372617701)
                ·
                  refine ⟨364826407524124007365819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1945740840128661372617701 364826407524124007365819)
                  ·
                    rfl

theorem cell22_3197236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3197236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197236 prefixEnd_3197236 := by exact prefixLift 3197236
  have htrace : WordTrace (prefixWord ++ tailWord_3197236) baseStart_3197236 baseEnd_3197236 := by
    simpa [prefixWord, tailWord_3197236, baseEnd_3197236] using wordTrace_append hprefix tailTrace_3197236
  have hstable : (prefixWord ++ tailWord_3197236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197236).length < 2 ^ (prefixWord ++ tailWord_3197236).sum := by decide
  have hdescent : baseEnd_3197236 < baseStart_3197236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197296 : List Nat := [2, 1, 1, 1, 4, 3, 2, 4, 1, 3]
def baseStart_3197296 : Nat := 118140960795 + 3197296 * 2 ^ 59
def prefixEnd_3197296 : Nat := 4983230072969 + 3 ^ 40 * 3197296 * 2
def baseEnd_3197296 : Nat := 1094499761798551865597273

theorem tailTrace_3197296 : CollatzResearch.WordTrace tailWord_3197296 prefixEnd_3197296 1094499761798551865597273 := by
  unfold tailWord_3197296
  simp only [CollatzResearch.WordTrace]
  refine ⟨58307482712375060764137871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77743310283166747685517161 58307482712375060764137871)
  ·
    refine ⟨87461224068562591146206807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58307482712375060764137871 87461224068562591146206807)
    ·
      refine ⟨131191836102843886719310211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87461224068562591146206807 131191836102843886719310211)
      ·
        refine ⟨196787754154265830078965317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131191836102843886719310211 196787754154265830078965317)
        ·
          refine ⟨36897703903924843139805997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196787754154265830078965317 36897703903924843139805997)
          ·
            refine ⟨13836638963971816177427249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36897703903924843139805997 13836638963971816177427249)
            ·
              refine ⟨10377479222978862133070437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13836638963971816177427249 10377479222978862133070437)
              ·
                refine ⟨1945777354308536649950707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10377479222978862133070437 1945777354308536649950707)
                ·
                  refine ⟨2918666031462804974926061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945777354308536649950707 2918666031462804974926061)
                  ·
                    refine ⟨1094499761798551865597273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2918666031462804974926061 1094499761798551865597273)
                    ·
                      rfl

theorem cell22_3197296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 1, 3].length) (baseStart_3197296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197296 prefixEnd_3197296 := by exact prefixLift 3197296
  have htrace : WordTrace (prefixWord ++ tailWord_3197296) baseStart_3197296 baseEnd_3197296 := by
    simpa [prefixWord, tailWord_3197296, baseEnd_3197296] using wordTrace_append hprefix tailTrace_3197296
  have hstable : (prefixWord ++ tailWord_3197296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197296).length < 2 ^ (prefixWord ++ tailWord_3197296).sum := by decide
  have hdescent : baseEnd_3197296 < baseStart_3197296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197307 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 2, 5]
def baseStart_3197307 : Nat := 118140960795 + 3197307 * 2 ^ 59
def prefixEnd_3197307 : Nat := 4983230072969 + 3 ^ 40 * 3197307 * 2
def baseEnd_3197307 : Nat := 1094503527323351503572239

theorem tailTrace_3197307 : CollatzResearch.WordTrace tailWord_3197307 prefixEnd_3197307 1094503527323351503572239 := by
  unfold tailWord_3197307
  simp only [CollatzResearch.WordTrace]
  refine ⟨116615366627710270406926175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77743577751806846937950783 116615366627710270406926175)
  ·
    refine ⟨174923049941565405610389263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116615366627710270406926175 174923049941565405610389263)
    ·
      refine ⟨262384574912348108415583895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174923049941565405610389263 262384574912348108415583895)
      ·
        refine ⟨393576862368522162623375843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262384574912348108415583895 393576862368522162623375843)
        ·
          refine ⟨590365293552783243935063765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393576862368522162623375843 590365293552783243935063765)
          ·
            refine ⟨13836686567643357279728057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 590365293552783243935063765 13836686567643357279728057)
            ·
              refine ⟨10377514925732517959796043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13836686567643357279728057 10377514925732517959796043)
              ·
                refine ⟨15566272388598776939694065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10377514925732517959796043 15566272388598776939694065)
                ·
                  refine ⟨11674704291449082704770549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15566272388598776939694065 11674704291449082704770549)
                  ·
                    refine ⟨1094503527323351503572239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11674704291449082704770549 1094503527323351503572239)
                    ·
                      rfl

theorem cell22_3197307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 5].length) (baseStart_3197307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197307 prefixEnd_3197307 := by exact prefixLift 3197307
  have htrace : WordTrace (prefixWord ++ tailWord_3197307) baseStart_3197307 baseEnd_3197307 := by
    simpa [prefixWord, tailWord_3197307, baseEnd_3197307] using wordTrace_append hprefix tailTrace_3197307
  have hstable : (prefixWord ++ tailWord_3197307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197307).length < 2 ^ (prefixWord ++ tailWord_3197307).sum := by decide
  have hdescent : baseEnd_3197307 < baseStart_3197307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197384 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 2, 4]
def baseStart_3197384 : Nat := 118140960795 + 3197384 * 2 ^ 59
def prefixEnd_3197384 : Nat := 4983230072969 + 3 ^ 40 * 3197384 * 2
def baseEnd_3197384 : Nat := 1094529885996948969397003

theorem tailTrace_3197384 : CollatzResearch.WordTrace tailWord_3197384 prefixEnd_3197384 1094529885996948969397003 := by
  unfold tailWord_3197384
  simp only [CollatzResearch.WordTrace]
  refine ⟨58309087524215656278739603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77745450032287541704986137 58309087524215656278739603)
  ·
    refine ⟨87463631286323484418109405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58309087524215656278739603 87463631286323484418109405)
    ·
      refine ⟨32798861732371306656791027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87463631286323484418109405 32798861732371306656791027)
      ·
        refine ⟨49198292598556959985186541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32798861732371306656791027 49198292598556959985186541)
        ·
          refine ⟨18449359724458859994444953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49198292598556959985186541 18449359724458859994444953)
          ·
            refine ⟨13837019793344144995833715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18449359724458859994444953 13837019793344144995833715)
            ·
              refine ⟨20755529690016217493750573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13837019793344144995833715 20755529690016217493750573)
              ·
                refine ⟨7783323633756081560156465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20755529690016217493750573 7783323633756081560156465)
                ·
                  refine ⟨5837492725317061170117349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7783323633756081560156465 5837492725317061170117349)
                  ·
                    refine ⟨1094529885996948969397003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5837492725317061170117349 1094529885996948969397003)
                    ·
                      rfl

theorem cell22_3197384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_3197384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197384 prefixEnd_3197384 := by exact prefixLift 3197384
  have htrace : WordTrace (prefixWord ++ tailWord_3197384) baseStart_3197384 baseEnd_3197384 := by
    simpa [prefixWord, tailWord_3197384, baseEnd_3197384] using wordTrace_append hprefix tailTrace_3197384
  have hstable : (prefixWord ++ tailWord_3197384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197384).length < 2 ^ (prefixWord ++ tailWord_3197384).sum := by decide
  have hdescent : baseEnd_3197384 < baseStart_3197384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197489 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 6]
def baseStart_3197489 : Nat := 118140960795 + 3197489 * 2 ^ 59
def prefixEnd_3197489 : Nat := 4983230072969 + 3 ^ 40 * 3197489 * 2
def baseEnd_3197489 : Nat := 364855276547587898507227

theorem tailTrace_3197489 : CollatzResearch.WordTrace tailWord_3197489 prefixEnd_3197489 364855276547587898507227 := by
  unfold tailWord_3197489
  simp only [CollatzResearch.WordTrace]
  refine ⟨116622004713050915490051521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77748003142033943660034347 116622004713050915490051521)
  ·
    refine ⟨87466503534788186617538641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116622004713050915490051521 87466503534788186617538641)
    ·
      refine ⟨65599877651091139963153981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87466503534788186617538641 65599877651091139963153981)
      ·
        refine ⟨24599954119159177486182743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65599877651091139963153981 24599954119159177486182743)
        ·
          refine ⟨36899931178738766229274115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24599954119159177486182743 36899931178738766229274115)
          ·
            refine ⟨55349896768108149343911173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36899931178738766229274115 55349896768108149343911173)
            ·
              refine ⟨10378105644020278001983345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55349896768108149343911173 10378105644020278001983345)
              ·
                refine ⟨7783579233015208501487509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10378105644020278001983345 7783579233015208501487509)
                ·
                  refine ⟨364855276547587898507227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7783579233015208501487509 364855276547587898507227)
                  ·
                    rfl

theorem cell22_3197489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_3197489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197489 prefixEnd_3197489 := by exact prefixLift 3197489
  have htrace : WordTrace (prefixWord ++ tailWord_3197489) baseStart_3197489 baseEnd_3197489 := by
    simpa [prefixWord, tailWord_3197489, baseEnd_3197489] using wordTrace_append hprefix tailTrace_3197489
  have hstable : (prefixWord ++ tailWord_3197489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197489).length < 2 ^ (prefixWord ++ tailWord_3197489).sum := by decide
  have hdescent : baseEnd_3197489 < baseStart_3197489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197491 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 1, 4]
def baseStart_3197491 : Nat := 118140960795 + 3197491 * 2 ^ 59
def prefixEnd_3197491 : Nat := 4983230072969 + 3 ^ 40 * 3197491 * 2
def baseEnd_3197491 : Nat := 1094566514283636356971675

theorem tailTrace_3197491 : CollatzResearch.WordTrace tailWord_3197491 prefixEnd_3197491 1094566514283636356971675 := by
  unfold tailWord_3197491
  simp only [CollatzResearch.WordTrace]
  refine ⟨116622077659043669831624327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77748051772695779887749551 116622077659043669831624327)
  ·
    refine ⟨174933116488565504747436491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116622077659043669831624327 174933116488565504747436491)
    ·
      refine ⟨262399674732848257121154737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174933116488565504747436491 262399674732848257121154737)
      ·
        refine ⟨196799756049636192840866053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262399674732848257121154737 196799756049636192840866053)
        ·
          refine ⟨36899954259306786157662385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196799756049636192840866053 36899954259306786157662385)
          ·
            refine ⟨27674965694480089618246789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36899954259306786157662385 27674965694480089618246789)
            ·
              refine ⟨5189056067715016803421273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27674965694480089618246789 5189056067715016803421273)
              ·
                refine ⟨3891792050786262602565955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5189056067715016803421273 3891792050786262602565955)
                ·
                  refine ⟨5837688076179393903848933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891792050786262602565955 5837688076179393903848933)
                  ·
                    refine ⟨1094566514283636356971675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5837688076179393903848933 1094566514283636356971675)
                    ·
                      rfl

theorem cell22_3197491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 4].length) (baseStart_3197491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197491 prefixEnd_3197491 := by exact prefixLift 3197491
  have htrace : WordTrace (prefixWord ++ tailWord_3197491) baseStart_3197491 baseEnd_3197491 := by
    simpa [prefixWord, tailWord_3197491, baseEnd_3197491] using wordTrace_append hprefix tailTrace_3197491
  have hstable : (prefixWord ++ tailWord_3197491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197491).length < 2 ^ (prefixWord ++ tailWord_3197491).sum := by decide
  have hdescent : baseEnd_3197491 < baseStart_3197491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197504 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 1, 5]
def baseStart_3197504 : Nat := 118140960795 + 3197504 * 2 ^ 59
def prefixEnd_3197504 : Nat := 4983230072969 + 3 ^ 40 * 3197504 * 2
def baseEnd_3197504 : Nat := 1094570964449308656396635

theorem tailTrace_3197504 : CollatzResearch.WordTrace tailWord_3197504 prefixEnd_3197504 1094570964449308656396635 := by
  unfold tailWord_3197504
  simp only [CollatzResearch.WordTrace]
  refine ⟨58311275903998286525923783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77748367871997715367898377 58311275903998286525923783)
  ·
    refine ⟨87466913855997429788885675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58311275903998286525923783 87466913855997429788885675)
    ·
      refine ⟨131200370783996144683328513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87466913855997429788885675 131200370783996144683328513)
      ·
        refine ⟨98400278087997108512496385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131200370783996144683328513 98400278087997108512496385)
        ·
          refine ⟨73800208565997831384372289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98400278087997108512496385 73800208565997831384372289)
          ·
            refine ⟨55350156424498373538279217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73800208565997831384372289 55350156424498373538279217)
            ·
              refine ⟨41512617318373780153709413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55350156424498373538279217 41512617318373780153709413)
              ·
                refine ⟨7783615747195083778820515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41512617318373780153709413 7783615747195083778820515)
                ·
                  refine ⟨11675423620792625668230773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7783615747195083778820515 11675423620792625668230773)
                  ·
                    refine ⟨1094570964449308656396635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11675423620792625668230773 1094570964449308656396635)
                    ·
                      rfl

theorem cell22_3197504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_3197504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197504 prefixEnd_3197504 := by exact prefixLift 3197504
  have htrace : WordTrace (prefixWord ++ tailWord_3197504) baseStart_3197504 baseEnd_3197504 := by
    simpa [prefixWord, tailWord_3197504, baseEnd_3197504] using wordTrace_append hprefix tailTrace_3197504
  have hstable : (prefixWord ++ tailWord_3197504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197504).length < 2 ^ (prefixWord ++ tailWord_3197504).sum := by decide
  have hdescent : baseEnd_3197504 < baseStart_3197504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197519 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 4, 4]
def baseStart_3197519 : Nat := 118140960795 + 3197519 * 2 ^ 59
def prefixEnd_3197519 : Nat := 4983230072969 + 3 ^ 40 * 3197519 * 2
def baseEnd_3197519 : Nat := 1094576099255853617271589

theorem tailTrace_3197519 : CollatzResearch.WordTrace tailWord_3197519 prefixEnd_3197519 1094576099255853617271589 := by
  unfold tailWord_3197519
  simp only [CollatzResearch.WordTrace]
  refine ⟨116623098902942230613643611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77748732601961487075762407 116623098902942230613643611)
  ·
    refine ⟨174934648354413345920465417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116623098902942230613643611 174934648354413345920465417)
    ·
      refine ⟨131200986265810009440349063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174934648354413345920465417 131200986265810009440349063)
      ·
        refine ⟨196801479398715014160523595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131200986265810009440349063 196801479398715014160523595)
        ·
          refine ⟨295202219098072521240785393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196801479398715014160523595 295202219098072521240785393)
          ·
            refine ⟨221401664323554390930589045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295202219098072521240785393 221401664323554390930589045)
            ·
              refine ⟨20756406030333224149742723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221401664323554390930589045 20756406030333224149742723)
              ·
                refine ⟨31134609045499836224614085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20756406030333224149742723 31134609045499836224614085)
                ·
                  refine ⟨5837739196031219292115141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31134609045499836224614085 5837739196031219292115141)
                  ·
                    refine ⟨1094576099255853617271589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5837739196031219292115141 1094576099255853617271589)
                    ·
                      rfl

theorem cell22_3197519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_3197519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197519 prefixEnd_3197519 := by exact prefixLift 3197519
  have htrace : WordTrace (prefixWord ++ tailWord_3197519) baseStart_3197519 baseEnd_3197519 := by
    simpa [prefixWord, tailWord_3197519, baseEnd_3197519] using wordTrace_append hprefix tailTrace_3197519
  have hstable : (prefixWord ++ tailWord_3197519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197519).length < 2 ^ (prefixWord ++ tailWord_3197519).sum := by decide
  have hdescent : baseEnd_3197519 < baseStart_3197519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197521 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 4, 3]
def baseStart_3197521 : Nat := 118140960795 + 3197521 * 2 ^ 59
def prefixEnd_3197521 : Nat := 4983230072969 + 3 ^ 40 * 3197521 * 2
def baseEnd_3197521 : Nat := 1094576783896726278721583

theorem tailTrace_3197521 : CollatzResearch.WordTrace tailWord_3197521 prefixEnd_3197521 1094576783896726278721583 := by
  unfold tailWord_3197521
  simp only [CollatzResearch.WordTrace]
  refine ⟨116623171848934984955216417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77748781232623323303477611 116623171848934984955216417)
  ·
    refine ⟨87467378886701238716412313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116623171848934984955216417 87467378886701238716412313)
    ·
      refine ⟨65600534165025929037309235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87467378886701238716412313 65600534165025929037309235)
      ·
        refine ⟨98400801247538893555963853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65600534165025929037309235 98400801247538893555963853)
        ·
          refine ⟨36900300467827085083486445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98400801247538893555963853 36900300467827085083486445)
          ·
            refine ⟨13837612675435156906307417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36900300467827085083486445 13837612675435156906307417)
            ·
              refine ⟨10378209506576367679730563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13837612675435156906307417 10378209506576367679730563)
              ·
                refine ⟨15567314259864551519595845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10378209506576367679730563 15567314259864551519595845)
                ·
                  refine ⟨2918871423724603409924221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15567314259864551519595845 2918871423724603409924221)
                  ·
                    refine ⟨1094576783896726278721583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2918871423724603409924221 1094576783896726278721583)
                    ·
                      rfl

theorem cell22_3197521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_3197521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197521 prefixEnd_3197521 := by exact prefixLift 3197521
  have htrace : WordTrace (prefixWord ++ tailWord_3197521) baseStart_3197521 baseEnd_3197521 := by
    simpa [prefixWord, tailWord_3197521, baseEnd_3197521] using wordTrace_append hprefix tailTrace_3197521
  have hstable : (prefixWord ++ tailWord_3197521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197521).length < 2 ^ (prefixWord ++ tailWord_3197521).sum := by decide
  have hdescent : baseEnd_3197521 < baseStart_3197521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197583 : List Nat := [1, 1, 2, 1, 1, 1, 1, 10, 1, 3]
def baseStart_3197583 : Nat := 118140960795 + 3197583 * 2 ^ 59
def prefixEnd_3197583 : Nat := 4983230072969 + 3 ^ 40 * 3197583 * 2
def baseEnd_3197583 : Nat := 1094598007763778783671393

theorem tailTrace_3197583 : CollatzResearch.WordTrace tailWord_3197583 prefixEnd_3197583 1094598007763778783671393 := by
  unfold tailWord_3197583
  simp only [CollatzResearch.WordTrace]
  refine ⟨116625433174710369543973403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77750288783140246362648935 116625433174710369543973403)
  ·
    refine ⟨174938149762065554315960105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116625433174710369543973403 174938149762065554315960105)
    ·
      refine ⟨131203612321549165736970079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174938149762065554315960105 131203612321549165736970079)
      ·
        refine ⟨196805418482323748605455119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131203612321549165736970079 196805418482323748605455119)
        ·
          refine ⟨295208127723485622908182679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196805418482323748605455119 295208127723485622908182679)
          ·
            refine ⟨442812191585228434362274019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295208127723485622908182679 442812191585228434362274019)
            ·
              refine ⟨664218287377842651543411029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442812191585228434362274019 664218287377842651543411029)
              ·
                refine ⟨1945952013802273393193587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 664218287377842651543411029 1945952013802273393193587)
                ·
                  refine ⟨2918928020703410089790381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945952013802273393193587 2918928020703410089790381)
                  ·
                    refine ⟨1094598007763778783671393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2918928020703410089790381 1094598007763778783671393)
                    ·
                      rfl

theorem cell22_3197583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 1, 3].length) (baseStart_3197583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197583 prefixEnd_3197583 := by exact prefixLift 3197583
  have htrace : WordTrace (prefixWord ++ tailWord_3197583) baseStart_3197583 baseEnd_3197583 := by
    simpa [prefixWord, tailWord_3197583, baseEnd_3197583] using wordTrace_append hprefix tailTrace_3197583
  have hstable : (prefixWord ++ tailWord_3197583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197583).length < 2 ^ (prefixWord ++ tailWord_3197583).sum := by decide
  have hdescent : baseEnd_3197583 < baseStart_3197583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197660 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3197660 : Nat := 118140960795 + 3197660 * 2 ^ 59
def prefixEnd_3197660 : Nat := 4983230072969 + 3 ^ 40 * 3197660 * 2
def baseEnd_3197660 : Nat := 1094624366437376249496157

theorem tailTrace_3197660 : CollatzResearch.WordTrace tailWord_3197660 prefixEnd_3197660 1094624366437376249496157 := by
  unfold tailWord_3197660
  simp only [CollatzResearch.WordTrace]
  refine ⟨58314120797715705847263217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77752161063620941129684289 58314120797715705847263217)
  ·
    refine ⟨43735590598286779385447413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58314120797715705847263217 43735590598286779385447413)
    ·
      refine ⟨4100211618589385567385695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43735590598286779385447413 4100211618589385567385695)
      ·
        refine ⟨6150317427884078351078543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100211618589385567385695 6150317427884078351078543)
        ·
          refine ⟨9225476141826117526617815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6150317427884078351078543 9225476141826117526617815)
          ·
            refine ⟨13838214212739176289926723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9225476141826117526617815 13838214212739176289926723)
            ·
              refine ⟨20757321319108764434890085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13838214212739176289926723 20757321319108764434890085)
              ·
                refine ⟨3891997747332893331541891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20757321319108764434890085 3891997747332893331541891)
                ·
                  refine ⟨5837996620999339997312837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891997747332893331541891 5837996620999339997312837)
                  ·
                    refine ⟨1094624366437376249496157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5837996620999339997312837 1094624366437376249496157)
                    ·
                      rfl

theorem cell22_3197660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3197660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197660 prefixEnd_3197660 := by exact prefixLift 3197660
  have htrace : WordTrace (prefixWord ++ tailWord_3197660) baseStart_3197660 baseEnd_3197660 := by
    simpa [prefixWord, tailWord_3197660, baseEnd_3197660] using wordTrace_append hprefix tailTrace_3197660
  have hstable : (prefixWord ++ tailWord_3197660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197660).length < 2 ^ (prefixWord ++ tailWord_3197660).sum := by decide
  have hdescent : baseEnd_3197660 < baseStart_3197660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197703 : List Nat := [1, 1, 4, 4, 1, 2, 2, 7]
def baseStart_3197703 : Nat := 118140960795 + 3197703 * 2 ^ 59
def prefixEnd_3197703 : Nat := 4983230072969 + 3 ^ 40 * 3197703 * 2
def baseEnd_3197703 : Nat := 121626565135126496741225

theorem tailTrace_3197703 : CollatzResearch.WordTrace tailWord_3197703 prefixEnd_3197703 121626565135126496741225 := by
  unfold tailWord_3197703
  simp only [CollatzResearch.WordTrace]
  refine ⟨116629809934275630038341763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77753206622850420025561175 116629809934275630038341763)
  ·
    refine ⟨174944714901413445057512645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116629809934275630038341763 174944714901413445057512645)
    ·
      refine ⟨32802134044015020948283621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174944714901413445057512645 32802134044015020948283621)
      ·
        refine ⟨6150400133252816427803179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32802134044015020948283621 6150400133252816427803179)
        ·
          refine ⟨9225600199879224641704769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6150400133252816427803179 9225600199879224641704769)
          ·
            refine ⟨6919200149909418481278577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9225600199879224641704769 6919200149909418481278577)
            ·
              refine ⟨5189400112432063860958933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6919200149909418481278577 5189400112432063860958933)
              ·
                refine ⟨121626565135126496741225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5189400112432063860958933 121626565135126496741225)
                ·
                  rfl

theorem cell22_3197703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 7].length) (baseStart_3197703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197703 prefixEnd_3197703 := by exact prefixLift 3197703
  have htrace : WordTrace (prefixWord ++ tailWord_3197703) baseStart_3197703 baseEnd_3197703 := by
    simpa [prefixWord, tailWord_3197703, baseEnd_3197703] using wordTrace_append hprefix tailTrace_3197703
  have hstable : (prefixWord ++ tailWord_3197703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197703).length < 2 ^ (prefixWord ++ tailWord_3197703).sum := by decide
  have hdescent : baseEnd_3197703 < baseStart_3197703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197776 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 8]
def baseStart_3197776 : Nat := 118140960795 + 3197776 * 2 ^ 59
def prefixEnd_3197776 : Nat := 4983230072969 + 3 ^ 40 * 3197776 * 2
def baseEnd_3197776 : Nat := 364888025202663537865267

theorem tailTrace_3197776 : CollatzResearch.WordTrace tailWord_3197776 prefixEnd_3197776 364888025202663537865267 := by
  unfold tailWord_3197776
  simp only [CollatzResearch.WordTrace]
  refine ⟨58316236231505581752874591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77754981642007442337166121 58316236231505581752874591)
  ·
    refine ⟨87474354347258372629311887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58316236231505581752874591 87474354347258372629311887)
    ·
      refine ⟨131211531520887558943967831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87474354347258372629311887 131211531520887558943967831)
      ·
        refine ⟨196817297281331338415951747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131211531520887558943967831 196817297281331338415951747)
        ·
          refine ⟨295225945921997007623927621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196817297281331338415951747 295225945921997007623927621)
          ·
            refine ⟨55354864860374438929486429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295225945921997007623927621 55354864860374438929486429)
            ·
              refine ⟨20758074322640414598557411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55354864860374438929486429 20758074322640414598557411)
              ·
                refine ⟨31137111483960621897836117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20758074322640414598557411 31137111483960621897836117)
                ·
                  refine ⟨364888025202663537865267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31137111483960621897836117 364888025202663537865267)
                  ·
                    rfl

theorem cell22_3197776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_3197776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197776 prefixEnd_3197776 := by exact prefixLift 3197776
  have htrace : WordTrace (prefixWord ++ tailWord_3197776) baseStart_3197776 baseEnd_3197776 := by
    simpa [prefixWord, tailWord_3197776, baseEnd_3197776] using wordTrace_append hprefix tailTrace_3197776
  have hstable : (prefixWord ++ tailWord_3197776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197776).length < 2 ^ (prefixWord ++ tailWord_3197776).sum := by decide
  have hdescent : baseEnd_3197776 < baseStart_3197776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197778 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_3197778 : Nat := 118140960795 + 3197778 * 2 ^ 59
def prefixEnd_3197778 : Nat := 4983230072969 + 3 ^ 40 * 3197778 * 2
def baseEnd_3197778 : Nat := 1094664760248863275045795

theorem tailTrace_3197778 : CollatzResearch.WordTrace tailWord_3197778 prefixEnd_3197778 1094664760248863275045795 := by
  unfold tailWord_3197778
  simp only [CollatzResearch.WordTrace]
  refine ⟨29158136352250979461830497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77755030272669278564881325 29158136352250979461830497)
  ·
    refine ⟨21868602264188234596372873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29158136352250979461830497 21868602264188234596372873)
    ·
      refine ⟨16401451698141175947279655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21868602264188234596372873 16401451698141175947279655)
      ·
        refine ⟨24602177547211763920919483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16401451698141175947279655 24602177547211763920919483)
        ·
          refine ⟨36903266320817645881379225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24602177547211763920919483 36903266320817645881379225)
          ·
            refine ⟨27677449740613234411034419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36903266320817645881379225 27677449740613234411034419)
            ·
              refine ⟨41516174610919851616551629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27677449740613234411034419 41516174610919851616551629)
              ·
                refine ⟨15568565479094944356206861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41516174610919851616551629 15568565479094944356206861)
                ·
                  refine ⟨5838212054660604133577573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15568565479094944356206861 5838212054660604133577573)
                  ·
                    refine ⟨1094664760248863275045795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5838212054660604133577573 1094664760248863275045795)
                    ·
                      rfl

theorem cell22_3197778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_3197778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197778 prefixEnd_3197778 := by exact prefixLift 3197778
  have htrace : WordTrace (prefixWord ++ tailWord_3197778) baseStart_3197778 baseEnd_3197778 := by
    simpa [prefixWord, tailWord_3197778, baseEnd_3197778] using wordTrace_append hprefix tailTrace_3197778
  have hstable : (prefixWord ++ tailWord_3197778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197778).length < 2 ^ (prefixWord ++ tailWord_3197778).sum := by decide
  have hdescent : baseEnd_3197778 < baseStart_3197778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197795 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 1, 4]
def baseStart_3197795 : Nat := 118140960795 + 3197795 * 2 ^ 59
def prefixEnd_3197795 : Nat := 4983230072969 + 3 ^ 40 * 3197795 * 2
def baseEnd_3197795 : Nat := 1094670579696280897370743

theorem tailTrace_3197795 : CollatzResearch.WordTrace tailWord_3197795 prefixEnd_3197795 1094670579696280897370743 := by
  unfold tailWord_3197795
  simp only [CollatzResearch.WordTrace]
  refine ⟨116633165449942329750690839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77755443633294886500460559 116633165449942329750690839)
  ·
    refine ⟨174949748174913494626036259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116633165449942329750690839 174949748174913494626036259)
    ·
      refine ⟨262424622262370241939054389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174949748174913494626036259 262424622262370241939054389)
      ·
        refine ⟨24602308337097210181786349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 262424622262370241939054389 24602308337097210181786349)
        ·
          refine ⟨9225865626411453818169881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24602308337097210181786349 9225865626411453818169881)
          ·
            refine ⟨6919399219808590363627411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9225865626411453818169881 6919399219808590363627411)
            ·
              refine ⟨10379098829712885545441117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6919399219808590363627411 10379098829712885545441117)
              ·
                refine ⟨3892162061142332079540419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10379098829712885545441117 3892162061142332079540419)
                ·
                  refine ⟨5838243091713498119310629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892162061142332079540419 5838243091713498119310629)
                  ·
                    refine ⟨1094670579696280897370743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5838243091713498119310629 1094670579696280897370743)
                    ·
                      rfl

theorem cell22_3197795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 4].length) (baseStart_3197795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197795 prefixEnd_3197795 := by exact prefixLift 3197795
  have htrace : WordTrace (prefixWord ++ tailWord_3197795) baseStart_3197795 baseEnd_3197795 := by
    simpa [prefixWord, tailWord_3197795, baseEnd_3197795] using wordTrace_append hprefix tailTrace_3197795
  have hstable : (prefixWord ++ tailWord_3197795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197795).length < 2 ^ (prefixWord ++ tailWord_3197795).sum := by decide
  have hdescent : baseEnd_3197795 < baseStart_3197795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197810 : List Nat := [3, 2, 1, 2, 1, 1, 4, 4, 4]
def baseStart_3197810 : Nat := 118140960795 + 3197810 * 2 ^ 59
def prefixEnd_3197810 : Nat := 4983230072969 + 3 ^ 40 * 3197810 * 2
def baseEnd_3197810 : Nat := 364891904834275286081899

theorem tailTrace_3197810 : CollatzResearch.WordTrace tailWord_3197810 prefixEnd_3197810 364891904834275286081899 := by
  unfold tailWord_3197810
  simp only [CollatzResearch.WordTrace]
  refine ⟨29158428136221996828121721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77755808363258658208324589 29158428136221996828121721)
  ·
    refine ⟨21868821102166497621091291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29158428136221996828121721 21868821102166497621091291)
    ·
      refine ⟨32803231653249746431636937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21868821102166497621091291 32803231653249746431636937)
      ·
        refine ⟨24602423739937309823727703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32803231653249746431636937 24602423739937309823727703)
        ·
          refine ⟨36903635609905964735591555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24602423739937309823727703 36903635609905964735591555)
          ·
            refine ⟨55355453414858947103387333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36903635609905964735591555 55355453414858947103387333)
            ·
              refine ⟨10379147515286052581885125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55355453414858947103387333 10379147515286052581885125)
              ·
                refine ⟨1946090159116134859103461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10379147515286052581885125 1946090159116134859103461)
                ·
                  refine ⟨364891904834275286081899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1946090159116134859103461 364891904834275286081899)
                  ·
                    rfl

theorem cell22_3197810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_3197810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197810 prefixEnd_3197810 := by exact prefixLift 3197810
  have htrace : WordTrace (prefixWord ++ tailWord_3197810) baseStart_3197810 baseEnd_3197810 := by
    simpa [prefixWord, tailWord_3197810, baseEnd_3197810] using wordTrace_append hprefix tailTrace_3197810
  have hstable : (prefixWord ++ tailWord_3197810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197810).length < 2 ^ (prefixWord ++ tailWord_3197810).sum := by decide
  have hdescent : baseEnd_3197810 < baseStart_3197810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197876 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3197876 : Nat := 118140960795 + 3197876 * 2 ^ 59
def prefixEnd_3197876 : Nat := 4983230072969 + 3 ^ 40 * 3197876 * 2
def baseEnd_3197876 : Nat := 1094698307651623686095495

theorem tailTrace_3197876 : CollatzResearch.WordTrace tailWord_3197876 prefixEnd_3197876 1094698307651623686095495 := by
  unfold tailWord_3197876
  simp only [CollatzResearch.WordTrace]
  refine ⟨58318059881324440292194741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77757413175099253722926321 58318059881324440292194741)
  ·
    refine ⟨5467318113874166277393257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58318059881324440292194741 5467318113874166277393257)
    ·
      refine ⟨4100488585405624708044943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5467318113874166277393257 4100488585405624708044943)
      ·
        refine ⟨6150732878108437062067415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100488585405624708044943 6150732878108437062067415)
        ·
          refine ⟨9226099317162655593101123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6150732878108437062067415 9226099317162655593101123)
          ·
            refine ⟨13839148975743983389651685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9226099317162655593101123 13839148975743983389651685)
            ·
              refine ⟨2594840432951996885559691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13839148975743983389651685 2594840432951996885559691)
              ·
                refine ⟨3892260649427995328339537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594840432951996885559691 3892260649427995328339537)
                ·
                  refine ⟨2919195487070996496254653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3892260649427995328339537 2919195487070996496254653)
                  ·
                    refine ⟨1094698307651623686095495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2919195487070996496254653 1094698307651623686095495)
                    ·
                      rfl

theorem cell22_3197876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3197876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197876 prefixEnd_3197876 := by exact prefixLift 3197876
  have htrace : WordTrace (prefixWord ++ tailWord_3197876) baseStart_3197876 baseEnd_3197876 := by
    simpa [prefixWord, tailWord_3197876, baseEnd_3197876] using wordTrace_append hprefix tailTrace_3197876
  have hstable : (prefixWord ++ tailWord_3197876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197876).length < 2 ^ (prefixWord ++ tailWord_3197876).sum := by decide
  have hdescent : baseEnd_3197876 < baseStart_3197876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197898 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_3197898 : Nat := 118140960795 + 3197898 * 2 ^ 59
def prefixEnd_3197898 : Nat := 4983230072969 + 3 ^ 40 * 3197898 * 2
def baseEnd_3197898 : Nat := 1094705838701222962045427

theorem tailTrace_3197898 : CollatzResearch.WordTrace tailWord_3197898 prefixEnd_3197898 1094705838701222962045427 := by
  unfold tailWord_3197898
  simp only [CollatzResearch.WordTrace]
  refine ⟨29159230542142294585422587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77757948112379452227793565 29159230542142294585422587)
  ·
    refine ⟨43738845813213441878133881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29159230542142294585422587 43738845813213441878133881)
    ·
      refine ⟨32804134359910081408600411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43738845813213441878133881 32804134359910081408600411)
      ·
        refine ⟨49206201539865122112900617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32804134359910081408600411 49206201539865122112900617)
        ·
          refine ⟨36904651154898841584675463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49206201539865122112900617 36904651154898841584675463)
          ·
            refine ⟨55356976732348262377013195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36904651154898841584675463 55356976732348262377013195)
            ·
              refine ⟨83035465098522393565519793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55356976732348262377013195 83035465098522393565519793)
              ·
                refine ⟨62276598823891795174139845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83035465098522393565519793 62276598823891795174139845)
                ·
                  refine ⟨11676862279479711595151221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62276598823891795174139845 11676862279479711595151221)
                  ·
                    refine ⟨1094705838701222962045427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11676862279479711595151221 1094705838701222962045427)
                    ·
                      rfl

theorem cell22_3197898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_3197898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197898 prefixEnd_3197898 := by exact prefixLift 3197898
  have htrace : WordTrace (prefixWord ++ tailWord_3197898) baseStart_3197898 baseEnd_3197898 := by
    simpa [prefixWord, tailWord_3197898, baseEnd_3197898] using wordTrace_append hprefix tailTrace_3197898
  have hstable : (prefixWord ++ tailWord_3197898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197898).length < 2 ^ (prefixWord ++ tailWord_3197898).sum := by decide
  have hdescent : baseEnd_3197898 < baseStart_3197898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197917 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 5]
def baseStart_3197917 : Nat := 118140960795 + 3197917 * 2 ^ 59
def prefixEnd_3197917 : Nat := 4983230072969 + 3 ^ 40 * 3197917 * 2
def baseEnd_3197917 : Nat := 364904114263171081940123

theorem tailTrace_3197917 : CollatzResearch.WordTrace tailWord_3197917 prefixEnd_3197917 364904114263171081940123 := by
  unfold tailWord_3197917
  simp only [CollatzResearch.WordTrace]
  refine ⟨116637615155500344586632005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77758410103666896391088003 116637615155500344586632005)
  ·
    refine ⟨21869552841656314609993501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116637615155500344586632005 21869552841656314609993501)
    ·
      refine ⟨8201082315621117978747563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21869552841656314609993501 8201082315621117978747563)
      ·
        refine ⟨12301623473431676968121345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8201082315621117978747563 12301623473431676968121345)
        ·
          refine ⟨9226217605073757726091009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12301623473431676968121345 9226217605073757726091009)
          ·
            refine ⟨6919663203805318294568257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9226217605073757726091009 6919663203805318294568257)
            ·
              refine ⟨5189747402853988720926193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6919663203805318294568257 5189747402853988720926193)
              ·
                refine ⟨3892310552140491540694645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5189747402853988720926193 3892310552140491540694645)
                ·
                  refine ⟨364904114263171081940123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3892310552140491540694645 364904114263171081940123)
                  ·
                    rfl

theorem cell22_3197917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_3197917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197917 prefixEnd_3197917 := by exact prefixLift 3197917
  have htrace : WordTrace (prefixWord ++ tailWord_3197917) baseStart_3197917 baseEnd_3197917 := by
    simpa [prefixWord, tailWord_3197917, baseEnd_3197917] using wordTrace_append hprefix tailTrace_3197917
  have hstable : (prefixWord ++ tailWord_3197917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197917).length < 2 ^ (prefixWord ++ tailWord_3197917).sum := by decide
  have hdescent : baseEnd_3197917 < baseStart_3197917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197930 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_3197930 : Nat := 118140960795 + 3197930 * 2 ^ 59
def prefixEnd_3197930 : Nat := 4983230072969 + 3 ^ 40 * 3197930 * 2
def baseEnd_3197930 : Nat := 1094716792955185545245329

theorem tailTrace_3197930 : CollatzResearch.WordTrace tailWord_3197930 prefixEnd_3197930 1094716792955185545245329 := by
  unfold tailWord_3197930
  simp only [CollatzResearch.WordTrace]
  refine ⟨29159522326113311951713811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77758726202968831871236829 29159522326113311951713811)
  ·
    refine ⟨43739283489169967927570717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29159522326113311951713811 43739283489169967927570717)
    ·
      refine ⟨16402231308438737972839019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43739283489169967927570717 16402231308438737972839019)
      ·
        refine ⟨24603346962658106959258529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16402231308438737972839019 24603346962658106959258529)
        ·
          refine ⟨18452510221993580219443897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24603346962658106959258529 18452510221993580219443897)
          ·
            refine ⟨13839382666495185164582923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18452510221993580219443897 13839382666495185164582923)
            ·
              refine ⟨20759073999742777746874385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13839382666495185164582923 20759073999742777746874385)
              ·
                refine ⟨15569305499807083310155789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20759073999742777746874385 15569305499807083310155789)
                ·
                  refine ⟨5838489562427656241308421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15569305499807083310155789 5838489562427656241308421)
                  ·
                    refine ⟨1094716792955185545245329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5838489562427656241308421 1094716792955185545245329)
                    ·
                      rfl

theorem cell22_3197930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_3197930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197930 prefixEnd_3197930 := by exact prefixLift 3197930
  have htrace : WordTrace (prefixWord ++ tailWord_3197930) baseStart_3197930 baseEnd_3197930 := by
    simpa [prefixWord, tailWord_3197930, baseEnd_3197930] using wordTrace_append hprefix tailTrace_3197930
  have hstable : (prefixWord ++ tailWord_3197930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197930).length < 2 ^ (prefixWord ++ tailWord_3197930).sum := by decide
  have hdescent : baseEnd_3197930 < baseStart_3197930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197960 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 1, 5]
def baseStart_3197960 : Nat := 118140960795 + 3197960 * 2 ^ 59
def prefixEnd_3197960 : Nat := 4983230072969 + 3 ^ 40 * 3197960 * 2
def baseEnd_3197960 : Nat := 1094727062568275466995237

theorem tailTrace_3197960 : CollatzResearch.WordTrace tailWord_3197960 prefixEnd_3197960 1094727062568275466995237 := by
  unfold tailWord_3197960
  simp only [CollatzResearch.WordTrace]
  refine ⟨58319591747172281465223667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77759455662896375286964889 58319591747172281465223667)
  ·
    refine ⟨87479387620758422197835501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58319591747172281465223667 87479387620758422197835501)
    ·
      refine ⟨32804770357784408324188313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87479387620758422197835501 32804770357784408324188313)
      ·
        refine ⟨24603577768338306243141235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32804770357784408324188313 24603577768338306243141235)
        ·
          refine ⟨36905366652507459364711853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24603577768338306243141235 36905366652507459364711853)
          ·
            refine ⟨13839512494690297261766945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36905366652507459364711853 13839512494690297261766945)
            ·
              refine ⟨10379634371017722946325209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13839512494690297261766945 10379634371017722946325209)
              ·
                refine ⟨7784725778263292209743907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10379634371017722946325209 7784725778263292209743907)
                ·
                  refine ⟨11677088667394938314615861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7784725778263292209743907 11677088667394938314615861)
                  ·
                    refine ⟨1094727062568275466995237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11677088667394938314615861 1094727062568275466995237)
                    ·
                      rfl

theorem cell22_3197960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_3197960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197960 prefixEnd_3197960 := by exact prefixLift 3197960
  have htrace : WordTrace (prefixWord ++ tailWord_3197960) baseStart_3197960 baseEnd_3197960 := by
    simpa [prefixWord, tailWord_3197960, baseEnd_3197960] using wordTrace_append hprefix tailTrace_3197960
  have hstable : (prefixWord ++ tailWord_3197960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197960).length < 2 ^ (prefixWord ++ tailWord_3197960).sum := by decide
  have hdescent : baseEnd_3197960 < baseStart_3197960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197962 : List Nat := [3, 1, 2, 2, 3, 1, 1, 5, 4]
def baseStart_3197962 : Nat := 118140960795 + 3197962 * 2 ^ 59
def prefixEnd_3197962 : Nat := 4983230072969 + 3 ^ 40 * 3197962 * 2
def baseEnd_3197962 : Nat := 364909249069716042815077

theorem tailTrace_3197962 : CollatzResearch.WordTrace tailWord_3197962 prefixEnd_3197962 364909249069716042815077 := by
  unfold tailWord_3197962
  simp only [CollatzResearch.WordTrace]
  refine ⟨29159814110084329318005035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77759504293558211514680093 29159814110084329318005035)
  ·
    refine ⟨43739721165126493977007553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29159814110084329318005035 43739721165126493977007553)
    ·
      refine ⟨32804790873844870482755665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43739721165126493977007553 32804790873844870482755665)
      ·
        refine ⟨24603593155383652862066749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32804790873844870482755665 24603593155383652862066749)
        ·
          refine ⟨9226347433268869823275031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24603593155383652862066749 9226347433268869823275031)
          ·
            refine ⟨13839521149903304734912547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9226347433268869823275031 13839521149903304734912547)
            ·
              refine ⟨20759281724854957102368821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13839521149903304734912547 20759281724854957102368821)
              ·
                refine ⟨1946182661705152228347077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20759281724854957102368821 1946182661705152228347077)
                ·
                  refine ⟨364909249069716042815077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1946182661705152228347077 364909249069716042815077)
                  ·
                    rfl

theorem cell22_3197962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_3197962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197962 prefixEnd_3197962 := by exact prefixLift 3197962
  have htrace : WordTrace (prefixWord ++ tailWord_3197962) baseStart_3197962 baseEnd_3197962 := by
    simpa [prefixWord, tailWord_3197962, baseEnd_3197962] using wordTrace_append hprefix tailTrace_3197962
  have hstable : (prefixWord ++ tailWord_3197962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197962).length < 2 ^ (prefixWord ++ tailWord_3197962).sum := by decide
  have hdescent : baseEnd_3197962 < baseStart_3197962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197964 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 1, 4]
def baseStart_3197964 : Nat := 118140960795 + 3197964 * 2 ^ 59
def prefixEnd_3197964 : Nat := 4983230072969 + 3 ^ 40 * 3197964 * 2
def baseEnd_3197964 : Nat := 1094728431850020789895225

theorem tailTrace_3197964 : CollatzResearch.WordTrace tailWord_3197964 prefixEnd_3197964 1094728431850020789895225 := by
  unfold tailWord_3197964
  simp only [CollatzResearch.WordTrace]
  refine ⟨58319664693165035806796473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77759552924220047742395297 58319664693165035806796473)
  ·
    refine ⟨43739748519873776855097355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58319664693165035806796473 43739748519873776855097355)
    ·
      refine ⟨65609622779810665282646033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43739748519873776855097355 65609622779810665282646033)
      ·
        refine ⟨49207217084857998961984525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65609622779810665282646033 49207217084857998961984525)
        ·
          refine ⟨18452706406821749610744197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49207217084857998961984525 18452706406821749610744197)
          ·
            refine ⟨3459882451279078052014537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18452706406821749610744197 3459882451279078052014537)
            ·
              refine ⟨2594911838459308539010903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3459882451279078052014537 2594911838459308539010903)
              ·
                refine ⟨3892367757688962808516355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594911838459308539010903 3892367757688962808516355)
                ·
                  refine ⟨5838551636533444212774533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892367757688962808516355 5838551636533444212774533)
                  ·
                    refine ⟨1094728431850020789895225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5838551636533444212774533 1094728431850020789895225)
                    ·
                      rfl

theorem cell22_3197964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_3197964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197964 prefixEnd_3197964 := by exact prefixLift 3197964
  have htrace : WordTrace (prefixWord ++ tailWord_3197964) baseStart_3197964 baseEnd_3197964 := by
    simpa [prefixWord, tailWord_3197964, baseEnd_3197964] using wordTrace_append hprefix tailTrace_3197964
  have hstable : (prefixWord ++ tailWord_3197964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197964).length < 2 ^ (prefixWord ++ tailWord_3197964).sum := by decide
  have hdescent : baseEnd_3197964 < baseStart_3197964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197977 : List Nat := [1, 2, 1, 2, 1, 1, 7, 2, 2, 3]
def baseStart_3197977 : Nat := 118140960795 + 3197977 * 2 ^ 59
def prefixEnd_3197977 : Nat := 4983230072969 + 3 ^ 40 * 3197977 * 2
def baseEnd_3197977 : Nat := 1094732882015693089320185

theorem tailTrace_3197977 : CollatzResearch.WordTrace tailWord_3197977 prefixEnd_3197977 1094732882015693089320185 := by
  unfold tailWord_3197977
  simp only [CollatzResearch.WordTrace]
  refine ⟨116639803535282974833816185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77759869023521983222544123 116639803535282974833816185)
  ·
    refine ⟨87479852651462231125362139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116639803535282974833816185 87479852651462231125362139)
    ·
      refine ⟨131219778977193346688043209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87479852651462231125362139 131219778977193346688043209)
      ·
        refine ⟨98414834232895010016032407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131219778977193346688043209 98414834232895010016032407)
        ·
          refine ⟨147622251349342515024048611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98414834232895010016032407 147622251349342515024048611)
          ·
            refine ⟨221433377024013772536072917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147622251349342515024048611 221433377024013772536072917)
            ·
              refine ⟨5189844774000322793814209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 221433377024013772536072917 5189844774000322793814209)
              ·
                refine ⟨3892383580500242095360657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5189844774000322793814209 3892383580500242095360657)
                ·
                  refine ⟨2919287685375181571520493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3892383580500242095360657 2919287685375181571520493)
                  ·
                    refine ⟨1094732882015693089320185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2919287685375181571520493 1094732882015693089320185)
                    ·
                      rfl

theorem cell22_3197977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 3].length) (baseStart_3197977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197977 prefixEnd_3197977 := by exact prefixLift 3197977
  have htrace : WordTrace (prefixWord ++ tailWord_3197977) baseStart_3197977 baseEnd_3197977 := by
    simpa [prefixWord, tailWord_3197977, baseEnd_3197977] using wordTrace_append hprefix tailTrace_3197977
  have hstable : (prefixWord ++ tailWord_3197977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197977).length < 2 ^ (prefixWord ++ tailWord_3197977).sum := by decide
  have hdescent : baseEnd_3197977 < baseStart_3197977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3197994 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 1, 5]
def baseStart_3197994 : Nat := 118140960795 + 3197994 * 2 ^ 59
def prefixEnd_3197994 : Nat := 4983230072969 + 3 ^ 40 * 3197994 * 2
def baseEnd_3197994 : Nat := 1094738701463110711645133

theorem tailTrace_3197994 : CollatzResearch.WordTrace tailWord_3197994 prefixEnd_3197994 1094738701463110711645133 := by
  unfold tailWord_3197994
  simp only [CollatzResearch.WordTrace]
  refine ⟨29160105894055346684296259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77760282384147591158123357 29160105894055346684296259)
  ·
    refine ⟨43740158841083020026444389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29160105894055346684296259 43740158841083020026444389)
    ·
      refine ⟨8201279782703066254958323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43740158841083020026444389 8201279782703066254958323)
      ·
        refine ⟨12301919674054599382437485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8201279782703066254958323 12301919674054599382437485)
        ·
          refine ⟨4613219877770474768414057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12301919674054599382437485 4613219877770474768414057)
          ·
            refine ⟨3459914908327856076310543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4613219877770474768414057 3459914908327856076310543)
            ·
              refine ⟨5189872362491784114465815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459914908327856076310543 5189872362491784114465815)
              ·
                refine ⟨7784808543737676171698723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5189872362491784114465815 7784808543737676171698723)
                ·
                  refine ⟨11677212815606514257548085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7784808543737676171698723 11677212815606514257548085)
                  ·
                    refine ⟨1094738701463110711645133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11677212815606514257548085 1094738701463110711645133)
                    ·
                      rfl

theorem cell22_3197994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_3197994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3197994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3197994 prefixEnd_3197994 := by exact prefixLift 3197994
  have htrace : WordTrace (prefixWord ++ tailWord_3197994) baseStart_3197994 baseEnd_3197994 := by
    simpa [prefixWord, tailWord_3197994, baseEnd_3197994] using wordTrace_append hprefix tailTrace_3197994
  have hstable : (prefixWord ++ tailWord_3197994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3197994).length < 2 ^ (prefixWord ++ tailWord_3197994).sum := by decide
  have hdescent : baseEnd_3197994 < baseStart_3197994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3197994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198045 : List Nat := [1, 4, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3198045 : Nat := 118140960795 + 3198045 * 2 ^ 59
def prefixEnd_3198045 : Nat := 4983230072969 + 3 ^ 40 * 3198045 * 2
def baseEnd_3198045 : Nat := 1094756159805363578619977

theorem tailTrace_3198045 : CollatzResearch.WordTrace tailWord_3198045 prefixEnd_3198045 1094756159805363578619977 := by
  unfold tailWord_3198045
  simp only [CollatzResearch.WordTrace]
  refine ⟨116642283699036622447291589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77761522466024414964861059 116642283699036622447291589)
  ·
    refine ⟨21870428193569366708867173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116642283699036622447291589 21870428193569366708867173)
    ·
      refine ⟨4100705286294256257912595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21870428193569366708867173 4100705286294256257912595)
      ·
        refine ⟨6151057929441384386868893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100705286294256257912595 6151057929441384386868893)
        ·
          refine ⟨2306646723540519145075835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6151057929441384386868893 2306646723540519145075835)
          ·
            refine ⟨3459970085310778717613753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306646723540519145075835 3459970085310778717613753)
            ·
              refine ⟨2594977563983084038210315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3459970085310778717613753 2594977563983084038210315)
              ·
                refine ⟨3892466345974626057315473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594977563983084038210315 3892466345974626057315473)
                ·
                  refine ⟨2919349759480969542986605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3892466345974626057315473 2919349759480969542986605)
                  ·
                    refine ⟨1094756159805363578619977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2919349759480969542986605 1094756159805363578619977)
                    ·
                      rfl

theorem cell22_3198045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3198045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198045 prefixEnd_3198045 := by exact prefixLift 3198045
  have htrace : WordTrace (prefixWord ++ tailWord_3198045) baseStart_3198045 baseEnd_3198045 := by
    simpa [prefixWord, tailWord_3198045, baseEnd_3198045] using wordTrace_append hprefix tailTrace_3198045
  have hstable : (prefixWord ++ tailWord_3198045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198045).length < 2 ^ (prefixWord ++ tailWord_3198045).sum := by decide
  have hdescent : baseEnd_3198045 < baseStart_3198045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198112 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 1, 5]
def baseStart_3198112 : Nat := 118140960795 + 3198112 * 2 ^ 59
def prefixEnd_3198112 : Nat := 4983230072969 + 3 ^ 40 * 3198112 * 2
def baseEnd_3198112 : Nat := 1094779095274597737194771

theorem tailTrace_3198112 : CollatzResearch.WordTrace tailWord_3198112 prefixEnd_3198112 1094779095274597737194771 := by
  unfold tailWord_3198112
  simp only [CollatzResearch.WordTrace]
  refine ⟨58322363694896946444990295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77763151593195928593320393 58322363694896946444990295)
  ·
    refine ⟨87483545542345419667485443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58322363694896946444990295 87483545542345419667485443)
    ·
      refine ⟨131225318313518129501228165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87483545542345419667485443 131225318313518129501228165)
      ·
        refine ⟨24604747183784649281480281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131225318313518129501228165 24604747183784649281480281)
        ·
          refine ⟨18453560387838486961110211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24604747183784649281480281 18453560387838486961110211)
          ·
            refine ⟨27680340581757730441665317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18453560387838486961110211 27680340581757730441665317)
            ·
              refine ⟨5190063859079574457812247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27680340581757730441665317 5190063859079574457812247)
              ·
                refine ⟨7785095788619361686718371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5190063859079574457812247 7785095788619361686718371)
                ·
                  refine ⟨11677643682929042530077557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7785095788619361686718371 11677643682929042530077557)
                  ·
                    refine ⟨1094779095274597737194771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11677643682929042530077557 1094779095274597737194771)
                    ·
                      rfl

theorem cell22_3198112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_3198112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198112 prefixEnd_3198112 := by exact prefixLift 3198112
  have htrace : WordTrace (prefixWord ++ tailWord_3198112) baseStart_3198112 baseEnd_3198112 := by
    simpa [prefixWord, tailWord_3198112, baseEnd_3198112] using wordTrace_append hprefix tailTrace_3198112
  have hstable : (prefixWord ++ tailWord_3198112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198112).length < 2 ^ (prefixWord ++ tailWord_3198112).sum := by decide
  have hdescent : baseEnd_3198112 < baseStart_3198112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198114 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 6]
def baseStart_3198114 : Nat := 118140960795 + 3198114 * 2 ^ 59
def prefixEnd_3198114 : Nat := 4983230072969 + 3 ^ 40 * 3198114 * 2
def baseEnd_3198114 : Nat := 364926593305156799548255

theorem tailTrace_3198114 : CollatzResearch.WordTrace tailWord_3198114 prefixEnd_3198114 364926593305156799548255 := by
  unfold tailWord_3198114
  simp only [CollatzResearch.WordTrace]
  refine ⟨29161200083946661807888349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77763200223857764821035597 29161200083946661807888349)
  ·
    refine ⟨10935450031479998177958131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29161200083946661807888349 10935450031479998177958131)
    ·
      refine ⟨16403175047219997266937197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10935450031479998177958131 16403175047219997266937197)
      ·
        refine ⟨6151190642707498975101449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16403175047219997266937197 6151190642707498975101449)
        ·
          refine ⟨4613392982030624231326087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6151190642707498975101449 4613392982030624231326087)
          ·
            refine ⟨6920089473045936346989131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4613392982030624231326087 6920089473045936346989131)
            ·
              refine ⟨10380134209568904520483697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6920089473045936346989131 10380134209568904520483697)
              ·
                refine ⟨7785100657176678390362773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10380134209568904520483697 7785100657176678390362773)
                ·
                  refine ⟨364926593305156799548255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7785100657176678390362773 364926593305156799548255)
                  ·
                    rfl

theorem cell22_3198114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_3198114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198114 prefixEnd_3198114 := by exact prefixLift 3198114
  have htrace : WordTrace (prefixWord ++ tailWord_3198114) baseStart_3198114 baseEnd_3198114 := by
    simpa [prefixWord, tailWord_3198114, baseEnd_3198114] using wordTrace_append hprefix tailTrace_3198114
  have hstable : (prefixWord ++ tailWord_3198114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198114).length < 2 ^ (prefixWord ++ tailWord_3198114).sum := by decide
  have hdescent : baseEnd_3198114 < baseStart_3198114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198127 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 2, 4]
def baseStart_3198127 : Nat := 118140960795 + 3198127 * 2 ^ 59
def prefixEnd_3198127 : Nat := 4983230072969 + 3 ^ 40 * 3198127 * 2
def baseEnd_3198127 : Nat := 1094784230081142698069725

theorem tailTrace_3198127 : CollatzResearch.WordTrace tailWord_3198127 prefixEnd_3198127 1094784230081142698069725 := by
  unfold tailWord_3198127
  simp only [CollatzResearch.WordTrace]
  refine ⟨116645274484739550451776635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77763516323159700301184423 116645274484739550451776635)
  ·
    refine ⟨174967911727109325677664953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116645274484739550451776635 174967911727109325677664953)
    ·
      refine ⟨131225933795331994258248715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174967911727109325677664953 131225933795331994258248715)
      ·
        refine ⟨196838900692997991387373073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131225933795331994258248715 196838900692997991387373073)
        ·
          refine ⟨147629175519748493540529805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196838900692997991387373073 147629175519748493540529805)
          ·
            refine ⟨55360940819905685077698677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147629175519748493540529805 55360940819905685077698677)
            ·
              refine ⟨5190088201866157976034251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55360940819905685077698677 5190088201866157976034251)
              ·
                refine ⟨7785132302799236964051377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5190088201866157976034251 7785132302799236964051377)
                ·
                  refine ⟨5838849227099427723038533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7785132302799236964051377 5838849227099427723038533)
                  ·
                    refine ⟨1094784230081142698069725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5838849227099427723038533 1094784230081142698069725)
                    ·
                      rfl

theorem cell22_3198127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_3198127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198127 prefixEnd_3198127 := by exact prefixLift 3198127
  have htrace : WordTrace (prefixWord ++ tailWord_3198127) baseStart_3198127 baseEnd_3198127 := by
    simpa [prefixWord, tailWord_3198127, baseEnd_3198127] using wordTrace_append hprefix tailTrace_3198127
  have hstable : (prefixWord ++ tailWord_3198127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198127).length < 2 ^ (prefixWord ++ tailWord_3198127).sum := by decide
  have hdescent : baseEnd_3198127 < baseStart_3198127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198142 : List Nat := [4, 2, 1, 1, 3, 2, 9]
def baseStart_3198142 : Nat := 118140960795 + 3198142 * 2 ^ 59
def prefixEnd_3198142 : Nat := 4983230072969 + 3 ^ 40 * 3198142 * 2
def baseEnd_3198142 : Nat := 40547754255099542923877

theorem tailTrace_3198142 : CollatzResearch.WordTrace tailWord_3198142 prefixEnd_3198142 40547754255099542923877 := by
  unfold tailWord_3198142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14580727697460651001696585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77763881053123472009048453 14580727697460651001696585)
  ·
    refine ⟨10935545773095488251272439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14580727697460651001696585 10935545773095488251272439)
    ·
      refine ⟨16403318659643232376908659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10935545773095488251272439 16403318659643232376908659)
      ·
        refine ⟨24604977989464848565362989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16403318659643232376908659 24604977989464848565362989)
        ·
          refine ⟨9226866746049318212011121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24604977989464848565362989 9226866746049318212011121)
          ·
            refine ⟨6920150059536988659008341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9226866746049318212011121 6920150059536988659008341)
            ·
              refine ⟨40547754255099542923877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6920150059536988659008341 40547754255099542923877)
              ·
                rfl

theorem cell22_3198142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 9].length) (baseStart_3198142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198142 prefixEnd_3198142 := by exact prefixLift 3198142
  have htrace : WordTrace (prefixWord ++ tailWord_3198142) baseStart_3198142 baseEnd_3198142 := by
    simpa [prefixWord, tailWord_3198142, baseEnd_3198142] using wordTrace_append hprefix tailTrace_3198142
  have hstable : (prefixWord ++ tailWord_3198142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198142).length < 2 ^ (prefixWord ++ tailWord_3198142).sum := by decide
  have hdescent : baseEnd_3198142 < baseStart_3198142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198155 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 2, 6]
def baseStart_3198155 : Nat := 118140960795 + 3198155 * 2 ^ 59
def prefixEnd_3198155 : Nat := 4983230072969 + 3 ^ 40 * 3198155 * 2
def baseEnd_3198155 : Nat := 1094793815053359958369639

theorem tailTrace_3198155 : CollatzResearch.WordTrace tailWord_3198155 prefixEnd_3198155 1094793815053359958369639 := by
  unfold tailWord_3198155
  simp only [CollatzResearch.WordTrace]
  refine ⟨116646295728638111233795919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77764197152425407489197279 116646295728638111233795919)
  ·
    refine ⟨174969443592957166850693879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116646295728638111233795919 174969443592957166850693879)
    ·
      refine ⟨262454165389435750276040819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174969443592957166850693879 262454165389435750276040819)
      ·
        refine ⟨393681248084153625414061229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262454165389435750276040819 393681248084153625414061229)
        ·
          refine ⟨147630468031557609530272961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393681248084153625414061229 147630468031557609530272961)
          ·
            refine ⟨110722851023668207147704721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147630468031557609530272961 110722851023668207147704721)
            ·
              refine ⟨83042138267751155360778541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110722851023668207147704721 83042138267751155360778541)
              ·
                refine ⟨31140801850406683260291953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83042138267751155360778541 31140801850406683260291953)
                ·
                  refine ⟨23355601387805012445218965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31140801850406683260291953 23355601387805012445218965)
                  ·
                    refine ⟨1094793815053359958369639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23355601387805012445218965 1094793815053359958369639)
                    ·
                      rfl

theorem cell22_3198155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_3198155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198155 prefixEnd_3198155 := by exact prefixLift 3198155
  have htrace : WordTrace (prefixWord ++ tailWord_3198155) baseStart_3198155 baseEnd_3198155 := by
    simpa [prefixWord, tailWord_3198155, baseEnd_3198155] using wordTrace_append hprefix tailTrace_3198155
  have hstable : (prefixWord ++ tailWord_3198155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198155).length < 2 ^ (prefixWord ++ tailWord_3198155).sum := by decide
  have hdescent : baseEnd_3198155 < baseStart_3198155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198217 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 3, 4]
def baseStart_3198217 : Nat := 118140960795 + 3198217 * 2 ^ 59
def prefixEnd_3198217 : Nat := 4983230072969 + 3 ^ 40 * 3198217 * 2
def baseEnd_3198217 : Nat := 1094815038920412463319449

theorem tailTrace_3198217 : CollatzResearch.WordTrace tailWord_3198217 prefixEnd_3198217 1094815038920412463319449 := by
  unfold tailWord_3198217
  simp only [CollatzResearch.WordTrace]
  refine ⟨116648557054413495822552905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77765704702942330548368603 116648557054413495822552905)
  ·
    refine ⟨87486417790810121866914679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116648557054413495822552905 87486417790810121866914679)
    ·
      refine ⟨131229626686215182800372019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87486417790810121866914679 131229626686215182800372019)
      ·
        refine ⟨196844440029322774200558029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131229626686215182800372019 196844440029322774200558029)
        ·
          refine ⟨73816665010996040325209261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196844440029322774200558029 73816665010996040325209261)
          ·
            refine ⟨27681249379123515121953473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73816665010996040325209261 27681249379123515121953473)
            ·
              refine ⟨20760937034342636341465105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27681249379123515121953473 20760937034342636341465105)
              ·
                refine ⟨15570702775756977256098829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20760937034342636341465105 15570702775756977256098829)
                ·
                  refine ⟨5839013540908866471037061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15570702775756977256098829 5839013540908866471037061)
                  ·
                    refine ⟨1094815038920412463319449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5839013540908866471037061 1094815038920412463319449)
                    ·
                      rfl

theorem cell22_3198217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_3198217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198217 prefixEnd_3198217 := by exact prefixLift 3198217
  have htrace : WordTrace (prefixWord ++ tailWord_3198217) baseStart_3198217 baseEnd_3198217 := by
    simpa [prefixWord, tailWord_3198217, baseEnd_3198217] using wordTrace_append hprefix tailTrace_3198217
  have hstable : (prefixWord ++ tailWord_3198217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198217).length < 2 ^ (prefixWord ++ tailWord_3198217).sum := by decide
  have hdescent : baseEnd_3198217 < baseStart_3198217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198234 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_3198234 : Nat := 118140960795 + 3198234 * 2 ^ 59
def prefixEnd_3198234 : Nat := 4983230072969 + 3 ^ 40 * 3198234 * 2
def baseEnd_3198234 : Nat := 1094820858367830085644397

theorem tailTrace_3198234 : CollatzResearch.WordTrace tailWord_3198234 prefixEnd_3198234 1094820858367830085644397 := by
  unfold tailWord_3198234
  simp only [CollatzResearch.WordTrace]
  refine ⟨29162294273837976931480439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77766118063567938483947837 29162294273837976931480439)
  ·
    refine ⟨43743441410756965397220659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29162294273837976931480439 43743441410756965397220659)
    ·
      refine ⟨65615162116135448095830989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43743441410756965397220659 65615162116135448095830989)
      ·
        refine ⟨24605685793550793035936621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65615162116135448095830989 24605685793550793035936621)
        ·
          refine ⟨9227132172581547388476233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24605685793550793035936621 9227132172581547388476233)
          ·
            refine ⟨6920349129436160541357175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9227132172581547388476233 6920349129436160541357175)
            ·
              refine ⟨10380523694154240812035763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6920349129436160541357175 10380523694154240812035763)
              ·
                refine ⟨15570785541231361218053645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10380523694154240812035763 15570785541231361218053645)
                ·
                  refine ⟨5839044577961760456770117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15570785541231361218053645 5839044577961760456770117)
                  ·
                    refine ⟨1094820858367830085644397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5839044577961760456770117 1094820858367830085644397)
                    ·
                      rfl

theorem cell22_3198234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_3198234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198234 prefixEnd_3198234 := by exact prefixLift 3198234
  have htrace : WordTrace (prefixWord ++ tailWord_3198234) baseStart_3198234 baseEnd_3198234 := by
    simpa [prefixWord, tailWord_3198234, baseEnd_3198234] using wordTrace_append hprefix tailTrace_3198234
  have hstable : (prefixWord ++ tailWord_3198234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198234).length < 2 ^ (prefixWord ++ tailWord_3198234).sum := by decide
  have hdescent : baseEnd_3198234 < baseStart_3198234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198309 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 5, 3]
def baseStart_3198309 : Nat := 118140960795 + 3198309 * 2 ^ 59
def prefixEnd_3198309 : Nat := 4983230072969 + 3 ^ 40 * 3198309 * 2
def baseEnd_3198309 : Nat := 1094846532400554890019167

theorem tailTrace_3198309 : CollatzResearch.WordTrace tailWord_3198309 prefixEnd_3198309 1094846532400554890019167 := by
  unfold tailWord_3198309
  simp only [CollatzResearch.WordTrace]
  refine ⟨116651912570080195534901981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77767941713386797023267987 116651912570080195534901981)
  ·
    refine ⟨43744467213780073325588243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116651912570080195534901981 43744467213780073325588243)
    ·
      refine ⟨65616700820670109988382365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43744467213780073325588243 65616700820670109988382365)
      ·
        refine ⟨24606262807751291245643387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65616700820670109988382365 24606262807751291245643387)
        ·
          refine ⟨36909394211626936868465081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24606262807751291245643387 36909394211626936868465081)
          ·
            refine ⟨27682045658720202651348811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36909394211626936868465081 27682045658720202651348811)
            ·
              refine ⟨41523068488080303977023217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27682045658720202651348811 41523068488080303977023217)
              ·
                refine ⟨31142301366060227982767413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41523068488080303977023217 31142301366060227982767413)
                ·
                  refine ⟨2919590753068146373384445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31142301366060227982767413 2919590753068146373384445)
                  ·
                    refine ⟨1094846532400554890019167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2919590753068146373384445 1094846532400554890019167)
                    ·
                      rfl

theorem cell22_3198309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_3198309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198309 prefixEnd_3198309 := by exact prefixLift 3198309
  have htrace : WordTrace (prefixWord ++ tailWord_3198309) baseStart_3198309 baseEnd_3198309 := by
    simpa [prefixWord, tailWord_3198309, baseEnd_3198309] using wordTrace_append hprefix tailTrace_3198309
  have hstable : (prefixWord ++ tailWord_3198309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198309).length < 2 ^ (prefixWord ++ tailWord_3198309).sum := by decide
  have hdescent : baseEnd_3198309 < baseStart_3198309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198414 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_3198414 : Nat := 118140960795 + 3198414 * 2 ^ 59
def prefixEnd_3198414 : Nat := 4983230072969 + 3 ^ 40 * 3198414 * 2
def baseEnd_3198414 : Nat := 1094882476046369616143845

theorem tailTrace_3198414 : CollatzResearch.WordTrace tailWord_3198414 prefixEnd_3198414 1094882476046369616143845 := by
  unfold tailWord_3198414
  simp only [CollatzResearch.WordTrace]
  refine ⟨14581967779337474808434287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77770494823133198978316197 14581967779337474808434287)
  ·
    refine ⟨21872951669006212212651431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14581967779337474808434287 21872951669006212212651431)
    ·
      refine ⟨32809427503509318318977147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21872951669006212212651431 32809427503509318318977147)
      ·
        refine ⟨49214141255263977478465721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32809427503509318318977147 49214141255263977478465721)
        ·
          refine ⟨36910605941447983108849291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49214141255263977478465721 36910605941447983108849291)
          ·
            refine ⟨55365908912171974663273937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36910605941447983108849291 55365908912171974663273937)
            ·
              refine ⟨41524431684128980997455453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55365908912171974663273937 41524431684128980997455453)
              ·
                refine ⟨15571661881548367874045795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41524431684128980997455453 15571661881548367874045795)
                ·
                  refine ⟨23357492822322551811068693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15571661881548367874045795 23357492822322551811068693)
                  ·
                    refine ⟨1094882476046369616143845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23357492822322551811068693 1094882476046369616143845)
                    ·
                      rfl

theorem cell22_3198414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_3198414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198414 prefixEnd_3198414 := by exact prefixLift 3198414
  have htrace : WordTrace (prefixWord ++ tailWord_3198414) baseStart_3198414 baseEnd_3198414 := by
    simpa [prefixWord, tailWord_3198414, baseEnd_3198414] using wordTrace_append hprefix tailTrace_3198414
  have hstable : (prefixWord ++ tailWord_3198414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198414).length < 2 ^ (prefixWord ++ tailWord_3198414).sum := by decide
  have hdescent : baseEnd_3198414 < baseStart_3198414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198420 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_3198420 : Nat := 118140960795 + 3198420 * 2 ^ 59
def prefixEnd_3198420 : Nat := 4983230072969 + 3 ^ 40 * 3198420 * 2
def baseEnd_3198420 : Nat := 1094884529968987600493827

theorem tailTrace_3198420 : CollatzResearch.WordTrace tailWord_3198420 prefixEnd_3198420 1094884529968987600493827 := by
  unfold tailWord_3198420
  simp only [CollatzResearch.WordTrace]
  refine ⟨58327980536339030746096357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77770640715118707661461809 58327980536339030746096357)
  ·
    refine ⟨10936496350563568264893067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58327980536339030746096357 10936496350563568264893067)
    ·
      refine ⟨16404744525845352397339601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10936496350563568264893067 16404744525845352397339601)
      ·
        refine ⟨12303558394384014298004701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16404744525845352397339601 12303558394384014298004701)
        ·
          refine ⟨4613834397894005361751763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12303558394384014298004701 4613834397894005361751763)
          ·
            refine ⟨6920751596841008042627645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4613834397894005361751763 6920751596841008042627645)
            ·
              refine ⟨2595281848815378015985367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6920751596841008042627645 2595281848815378015985367)
              ·
                refine ⟨3892922773223067023978051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595281848815378015985367 3892922773223067023978051)
                ·
                  refine ⟨5839384159834600535967077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892922773223067023978051 5839384159834600535967077)
                  ·
                    refine ⟨1094884529968987600493827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5839384159834600535967077 1094884529968987600493827)
                    ·
                      rfl

theorem cell22_3198420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_3198420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198420 prefixEnd_3198420 := by exact prefixLift 3198420
  have htrace : WordTrace (prefixWord ++ tailWord_3198420) baseStart_3198420 baseEnd_3198420 := by
    simpa [prefixWord, tailWord_3198420, baseEnd_3198420] using wordTrace_append hprefix tailTrace_3198420
  have hstable : (prefixWord ++ tailWord_3198420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198420).length < 2 ^ (prefixWord ++ tailWord_3198420).sum := by decide
  have hdescent : baseEnd_3198420 < baseStart_3198420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198429 : List Nat := [1, 4, 3, 1, 1, 12]
def baseStart_3198429 : Nat := 118140960795 + 3198429 * 2 ^ 59
def prefixEnd_3198429 : Nat := 4983230072969 + 3 ^ 40 * 3198429 * 2
def baseEnd_3198429 : Nat := 13517130998184130580479

theorem tailTrace_3198429 : CollatzResearch.WordTrace tailWord_3198429 prefixEnd_3198429 13517130998184130580479 := by
  unfold tailWord_3198429
  simp only [CollatzResearch.WordTrace]
  refine ⟨116656289329645456029270341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77770859553096970686180227 116656289329645456029270341)
  ·
    refine ⟨21873054249308523005488189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116656289329645456029270341 21873054249308523005488189)
    ·
      refine ⟨8202395343490696127058071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21873054249308523005488189 8202395343490696127058071)
      ·
        refine ⟨12303593015236044190587107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8202395343490696127058071 12303593015236044190587107)
        ·
          refine ⟨18455389522854066285880661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12303593015236044190587107 18455389522854066285880661)
          ·
            refine ⟨13517130998184130580479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18455389522854066285880661 13517130998184130580479)
            ·
              rfl

theorem cell22_3198429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 12].length) (baseStart_3198429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198429 prefixEnd_3198429 := by exact prefixLift 3198429
  have htrace : WordTrace (prefixWord ++ tailWord_3198429) baseStart_3198429 baseEnd_3198429 := by
    simpa [prefixWord, tailWord_3198429, baseEnd_3198429] using wordTrace_append hprefix tailTrace_3198429
  have hstable : (prefixWord ++ tailWord_3198429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198429).length < 2 ^ (prefixWord ++ tailWord_3198429).sum := by decide
  have hdescent : baseEnd_3198429 < baseStart_3198429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198433 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 2, 3]
def baseStart_3198433 : Nat := 118140960795 + 3198433 * 2 ^ 59
def prefixEnd_3198433 : Nat := 4983230072969 + 3 ^ 40 * 3198433 * 2
def baseEnd_3198433 : Nat := 1094888980134659899918787

theorem tailTrace_3198433 : CollatzResearch.WordTrace tailWord_3198433 prefixEnd_3198433 1094888980134659899918787 := by
  unfold tailWord_3198433
  simp only [CollatzResearch.WordTrace]
  refine ⟨116656435221630964712415953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77770956814420643141610635 116656435221630964712415953)
  ·
    refine ⟨87492326416223223534311965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116656435221630964712415953 87492326416223223534311965)
    ·
      refine ⟨32809622406083708825366987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87492326416223223534311965 32809622406083708825366987)
      ·
        refine ⟨49214433609125563238050481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32809622406083708825366987 49214433609125563238050481)
        ·
          refine ⟨36910825206844172428537861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49214433609125563238050481 36910825206844172428537861)
          ·
            refine ⟨6920779726283282330350849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36910825206844172428537861 6920779726283282330350849)
            ·
              refine ⟨5190584794712461747763137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6920779726283282330350849 5190584794712461747763137)
              ·
                refine ⟨3892938596034346310822353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5190584794712461747763137 3892938596034346310822353)
                ·
                  refine ⟨2919703947025759733116765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3892938596034346310822353 2919703947025759733116765)
                  ·
                    refine ⟨1094888980134659899918787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2919703947025759733116765 1094888980134659899918787)
                    ·
                      rfl

theorem cell22_3198433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_3198433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198433 prefixEnd_3198433 := by exact prefixLift 3198433
  have htrace : WordTrace (prefixWord ++ tailWord_3198433) baseStart_3198433 baseEnd_3198433 := by
    simpa [prefixWord, tailWord_3198433, baseEnd_3198433] using wordTrace_append hprefix tailTrace_3198433
  have hstable : (prefixWord ++ tailWord_3198433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198433).length < 2 ^ (prefixWord ++ tailWord_3198433).sum := by decide
  have hdescent : baseEnd_3198433 < baseStart_3198433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198435 : List Nat := [1, 1, 1, 6, 2, 3, 2, 2, 4]
def baseStart_3198435 : Nat := 118140960795 + 3198435 * 2 ^ 59
def prefixEnd_3198435 : Nat := 4983230072969 + 3 ^ 40 * 3198435 * 2
def baseEnd_3198435 : Nat := 364963221591844187122927

theorem tailTrace_3198435 : CollatzResearch.WordTrace tailWord_3198435 prefixEnd_3198435 364963221591844187122927 := by
  unfold tailWord_3198435
  simp only [CollatzResearch.WordTrace]
  refine ⟨116656508167623719053988759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77771005445082479369325839 116656508167623719053988759)
  ·
    refine ⟨174984762251435578580983139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116656508167623719053988759 174984762251435578580983139)
    ·
      refine ⟨262477143377153367871474709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174984762251435578580983139 262477143377153367871474709)
      ·
        refine ⟨12303616095804064118975377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 262477143377153367871474709 12303616095804064118975377)
        ·
          refine ⟨9227712071853048089231533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12303616095804064118975377 9227712071853048089231533)
          ·
            refine ⟨3460392026944893033461825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9227712071853048089231533 3460392026944893033461825)
            ·
              refine ⟨2595294020208669775096369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3460392026944893033461825 2595294020208669775096369)
              ·
                refine ⟨1946470515156502331322277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595294020208669775096369 1946470515156502331322277)
                ·
                  refine ⟨364963221591844187122927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1946470515156502331322277 364963221591844187122927)
                  ·
                    rfl

theorem cell22_3198435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 4].length) (baseStart_3198435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198435 prefixEnd_3198435 := by exact prefixLift 3198435
  have htrace : WordTrace (prefixWord ++ tailWord_3198435) baseStart_3198435 baseEnd_3198435 := by
    simpa [prefixWord, tailWord_3198435, baseEnd_3198435] using wordTrace_append hprefix tailTrace_3198435
  have hstable : (prefixWord ++ tailWord_3198435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198435).length < 2 ^ (prefixWord ++ tailWord_3198435).sum := by decide
  have hdescent : baseEnd_3198435 < baseStart_3198435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198461 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_3198461 : Nat := 118140960795 + 3198461 * 2 ^ 59
def prefixEnd_3198461 : Nat := 4983230072969 + 3 ^ 40 * 3198461 * 2
def baseEnd_3198461 : Nat := 1094898565106877160218701

theorem tailTrace_3198461 : CollatzResearch.WordTrace tailWord_3198461 prefixEnd_3198461 1094898565106877160218701 := by
  unfold tailWord_3198461
  simp only [CollatzResearch.WordTrace]
  refine ⟨116657456465529525494435237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77771637643686350329623491 116657456465529525494435237)
  ·
    refine ⟨21873273087286786030206607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116657456465529525494435237 21873273087286786030206607)
    ·
      refine ⟨32809909630930179045309911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21873273087286786030206607 32809909630930179045309911)
      ·
        refine ⟨49214864446395268567964867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32809909630930179045309911 49214864446395268567964867)
        ·
          refine ⟨73822296669592902851947301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49214864446395268567964867 73822296669592902851947301)
          ·
            refine ⟨13841680625548669284740119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73822296669592902851947301 13841680625548669284740119)
            ·
              refine ⟨20762520938323003927110179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13841680625548669284740119 20762520938323003927110179)
              ·
                refine ⟨31143781407484505890665269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20762520938323003927110179 31143781407484505890665269)
                ·
                  refine ⟨2919729506951672427249869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31143781407484505890665269 2919729506951672427249869)
                  ·
                    refine ⟨1094898565106877160218701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2919729506951672427249869 1094898565106877160218701)
                    ·
                      rfl

theorem cell22_3198461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_3198461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198461 prefixEnd_3198461 := by exact prefixLift 3198461
  have htrace : WordTrace (prefixWord ++ tailWord_3198461) baseStart_3198461 baseEnd_3198461 := by
    simpa [prefixWord, tailWord_3198461, baseEnd_3198461] using wordTrace_append hprefix tailTrace_3198461
  have hstable : (prefixWord ++ tailWord_3198461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198461).length < 2 ^ (prefixWord ++ tailWord_3198461).sum := by decide
  have hdescent : baseEnd_3198461 < baseStart_3198461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198465 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3198465 : Nat := 118140960795 + 3198465 * 2 ^ 59
def prefixEnd_3198465 : Nat := 4983230072969 + 3 ^ 40 * 3198465 * 2
def baseEnd_3198465 : Nat := 1094899934388622483118689

theorem tailTrace_3198465 : CollatzResearch.WordTrace tailWord_3198465 prefixEnd_3198465 1094899934388622483118689 := by
  unfold tailWord_3198465
  simp only [CollatzResearch.WordTrace]
  refine ⟨116657602357515034177580849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77771734905010022785053899 116657602357515034177580849)
  ·
    refine ⟨87493201768136275633185637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116657602357515034177580849 87493201768136275633185637)
    ·
      refine ⟨16404975331525551681222307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87493201768136275633185637 16404975331525551681222307)
      ·
        refine ⟨24607462997288327521833461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16404975331525551681222307 24607462997288327521833461)
        ·
          refine ⟨2306949655995780705171887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24607462997288327521833461 2306949655995780705171887)
          ·
            refine ⟨3460424483993671057757831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306949655995780705171887 3460424483993671057757831)
            ·
              refine ⟨5190636725990506586636747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460424483993671057757831 5190636725990506586636747)
              ·
                refine ⟨7785955088985759879955121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5190636725990506586636747 7785955088985759879955121)
                ·
                  refine ⟨5839466316739319909966341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7785955088985759879955121 5839466316739319909966341)
                  ·
                    refine ⟨1094899934388622483118689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5839466316739319909966341 1094899934388622483118689)
                    ·
                      rfl

theorem cell22_3198465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3198465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198465 prefixEnd_3198465 := by exact prefixLift 3198465
  have htrace : WordTrace (prefixWord ++ tailWord_3198465) baseStart_3198465 baseEnd_3198465 := by
    simpa [prefixWord, tailWord_3198465, baseEnd_3198465] using wordTrace_append hprefix tailTrace_3198465
  have hstable : (prefixWord ++ tailWord_3198465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198465).length < 2 ^ (prefixWord ++ tailWord_3198465).sum := by decide
  have hdescent : baseEnd_3198465 < baseStart_3198465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198484 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3198484 : Nat := 118140960795 + 3198484 * 2 ^ 59
def prefixEnd_3198484 : Nat := 4983230072969 + 3 ^ 40 * 3198484 * 2
def baseEnd_3198484 : Nat := 1094906438476912766893631

theorem tailTrace_3198484 : CollatzResearch.WordTrace tailWord_3198484 prefixEnd_3198484 1094906438476912766893631 := by
  unfold tailWord_3198484
  simp only [CollatzResearch.WordTrace]
  refine ⟨58329147672223100211261253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77772196896297466948348337 58329147672223100211261253)
  ·
    refine ⟨10936715188541831289611485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58329147672223100211261253 10936715188541831289611485)
    ·
      refine ⟨4101268195703186733604307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10936715188541831289611485 4101268195703186733604307)
      ·
        refine ⟨6151902293554780100406461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4101268195703186733604307 6151902293554780100406461)
        ·
          refine ⟨2306963360083042537652423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6151902293554780100406461 2306963360083042537652423)
          ·
            refine ⟨3460445040124563806478635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306963360083042537652423 3460445040124563806478635)
            ·
              refine ⟨5190667560186845709717953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460445040124563806478635 5190667560186845709717953)
              ·
                refine ⟨3893000670140134282288465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5190667560186845709717953 3893000670140134282288465)
                ·
                  refine ⟨2919750502605100711716349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3893000670140134282288465 2919750502605100711716349)
                  ·
                    refine ⟨1094906438476912766893631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2919750502605100711716349 1094906438476912766893631)
                    ·
                      rfl

theorem cell22_3198484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3198484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198484 prefixEnd_3198484 := by exact prefixLift 3198484
  have htrace : WordTrace (prefixWord ++ tailWord_3198484) baseStart_3198484 baseEnd_3198484 := by
    simpa [prefixWord, tailWord_3198484, baseEnd_3198484] using wordTrace_append hprefix tailTrace_3198484
  have hstable : (prefixWord ++ tailWord_3198484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198484).length < 2 ^ (prefixWord ++ tailWord_3198484).sum := by decide
  have hdescent : baseEnd_3198484 < baseStart_3198484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198506 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3198506 : Nat := 118140960795 + 3198506 * 2 ^ 59
def prefixEnd_3198506 : Nat := 4983230072969 + 3 ^ 40 * 3198506 * 2
def baseEnd_3198506 : Nat := 1094913969526512042843563

theorem tailTrace_3198506 : CollatzResearch.WordTrace tailWord_3198506 prefixEnd_3198506 1094913969526512042843563 := by
  unfold tailWord_3198506
  simp only [CollatzResearch.WordTrace]
  refine ⟨29164774437591624544955843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77772731833577665453215581 29164774437591624544955843)
  ·
    refine ⟨43747161656387436817433765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29164774437591624544955843 43747161656387436817433765)
    ·
      refine ⟨8202592810572644403268831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43747161656387436817433765 8202592810572644403268831)
      ·
        refine ⟨12303889215858966604903247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8202592810572644403268831 12303889215858966604903247)
        ·
          refine ⟨18455833823788449907354871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12303889215858966604903247 18455833823788449907354871)
          ·
            refine ⟨27683750735682674861032307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18455833823788449907354871 27683750735682674861032307)
            ·
              refine ⟨41525626103524012291548461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27683750735682674861032307 41525626103524012291548461)
              ·
                refine ⟨15572109788821504609330673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41525626103524012291548461 15572109788821504609330673)
                ·
                  refine ⟨11679082341616128456998005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15572109788821504609330673 11679082341616128456998005)
                  ·
                    refine ⟨1094913969526512042843563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11679082341616128456998005 1094913969526512042843563)
                    ·
                      rfl

theorem cell22_3198506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3198506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198506 prefixEnd_3198506 := by exact prefixLift 3198506
  have htrace : WordTrace (prefixWord ++ tailWord_3198506) baseStart_3198506 baseEnd_3198506 := by
    simpa [prefixWord, tailWord_3198506, baseEnd_3198506] using wordTrace_append hprefix tailTrace_3198506
  have hstable : (prefixWord ++ tailWord_3198506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198506).length < 2 ^ (prefixWord ++ tailWord_3198506).sum := by decide
  have hdescent : baseEnd_3198506 < baseStart_3198506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198647 : List Nat := [1, 1, 3, 1, 5, 2, 2, 3, 1, 3]
def baseStart_3198647 : Nat := 118140960795 + 3198647 * 2 ^ 59
def prefixEnd_3198647 : Nat := 4983230072969 + 3 ^ 40 * 3198647 * 2
def baseEnd_3198647 : Nat := 1094962236708034675068131

theorem tailTrace_3198647 : CollatzResearch.WordTrace tailWord_3198647 prefixEnd_3198647 1094962236708034675068131 := by
  unfold tailWord_3198647
  simp only [CollatzResearch.WordTrace]
  refine ⟨116664240442855679260706195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77776160295237119507137463 116664240442855679260706195)
  ·
    refine ⟨174996360664283518891059293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116664240442855679260706195 174996360664283518891059293)
    ·
      refine ⟨65623635249106319584147235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174996360664283518891059293 65623635249106319584147235)
      ·
        refine ⟨98435452873659479376220853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65623635249106319584147235 98435452873659479376220853)
        ·
          refine ⟨9228323706905576191520705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98435452873659479376220853 9228323706905576191520705)
          ·
            refine ⟨6921242780179182143640529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9228323706905576191520705 6921242780179182143640529)
            ·
              refine ⟨5190932085134386607730397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6921242780179182143640529 5190932085134386607730397)
              ·
                refine ⟨1946599531925394977898899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5190932085134386607730397 1946599531925394977898899)
                ·
                  refine ⟨2919899297888092466848349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946599531925394977898899 2919899297888092466848349)
                  ·
                    refine ⟨1094962236708034675068131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2919899297888092466848349 1094962236708034675068131)
                    ·
                      rfl

theorem cell22_3198647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_3198647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198647 prefixEnd_3198647 := by exact prefixLift 3198647
  have htrace : WordTrace (prefixWord ++ tailWord_3198647) baseStart_3198647 baseEnd_3198647 := by
    simpa [prefixWord, tailWord_3198647, baseEnd_3198647] using wordTrace_append hprefix tailTrace_3198647
  have hstable : (prefixWord ++ tailWord_3198647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198647).length < 2 ^ (prefixWord ++ tailWord_3198647).sum := by decide
  have hdescent : baseEnd_3198647 < baseStart_3198647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198703 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 6, 3]
def baseStart_3198703 : Nat := 118140960795 + 3198703 * 2 ^ 59
def prefixEnd_3198703 : Nat := 4983230072969 + 3 ^ 40 * 3198703 * 2
def baseEnd_3198703 : Nat := 1094981406652469195667959

theorem tailTrace_3198703 : CollatzResearch.WordTrace tailWord_3198703 prefixEnd_3198703 1094981406652469195667959 := by
  unfold tailWord_3198703
  simp only [CollatzResearch.WordTrace]
  refine ⟨116666282930652800824744763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77777521953768533883163175 116666282930652800824744763)
  ·
    refine ⟨174999424395979201237117145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116666282930652800824744763 174999424395979201237117145)
    ·
      refine ⟨131249568296984400927837859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174999424395979201237117145 131249568296984400927837859)
      ·
        refine ⟨196874352445476601391756789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131249568296984400927837859 196874352445476601391756789)
        ·
          refine ⟨18456970541763431380477199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196874352445476601391756789 18456970541763431380477199)
          ·
            refine ⟨27685455812645147070715799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18456970541763431380477199 27685455812645147070715799)
            ·
              refine ⟨41528183718967720606073699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27685455812645147070715799 41528183718967720606073699)
              ·
                refine ⟨62292275578451580909110549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41528183718967720606073699 62292275578451580909110549)
                ·
                  refine ⟨2919950417739917855114557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62292275578451580909110549 2919950417739917855114557)
                  ·
                    refine ⟨1094981406652469195667959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2919950417739917855114557 1094981406652469195667959)
                    ·
                      rfl

theorem cell22_3198703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 3].length) (baseStart_3198703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198703 prefixEnd_3198703 := by exact prefixLift 3198703
  have htrace : WordTrace (prefixWord ++ tailWord_3198703) baseStart_3198703 baseEnd_3198703 := by
    simpa [prefixWord, tailWord_3198703, baseEnd_3198703] using wordTrace_append hprefix tailTrace_3198703
  have hstable : (prefixWord ++ tailWord_3198703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198703).length < 2 ^ (prefixWord ++ tailWord_3198703).sum := by decide
  have hdescent : baseEnd_3198703 < baseStart_3198703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198705 : List Nat := [1, 2, 2, 2, 2, 3, 3, 3, 4]
def baseStart_3198705 : Nat := 118140960795 + 3198705 * 2 ^ 59
def prefixEnd_3198705 : Nat := 4983230072969 + 3 ^ 40 * 3198705 * 2
def baseEnd_3198705 : Nat := 364994030431113952372651

theorem tailTrace_3198705 : CollatzResearch.WordTrace tailWord_3198705 prefixEnd_3198705 364994030431113952372651 := by
  unfold tailWord_3198705
  simp only [CollatzResearch.WordTrace]
  refine ⟨116666355876645555166317569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77777570584430370110878379 116666355876645555166317569)
  ·
    refine ⟨87499766907484166374738177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116666355876645555166317569 87499766907484166374738177)
    ·
      refine ⟨65624825180613124781053633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87499766907484166374738177 65624825180613124781053633)
      ·
        refine ⟨49218618885459843585790225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65624825180613124781053633 49218618885459843585790225)
        ·
          refine ⟨36913964164094882689342669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49218618885459843585790225 36913964164094882689342669)
          ·
            refine ⟨13842736561535581008503501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36913964164094882689342669 13842736561535581008503501)
            ·
              refine ⟨5191026210575842878188813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13842736561535581008503501 5191026210575842878188813)
              ·
                refine ⟨1946634828965941079320805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5191026210575842878188813 1946634828965941079320805)
                ·
                  refine ⟨364994030431113952372651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1946634828965941079320805 364994030431113952372651)
                  ·
                    rfl

theorem cell22_3198705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4].length) (baseStart_3198705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198705 prefixEnd_3198705 := by exact prefixLift 3198705
  have htrace : WordTrace (prefixWord ++ tailWord_3198705) baseStart_3198705 baseEnd_3198705 := by
    simpa [prefixWord, tailWord_3198705, baseEnd_3198705] using wordTrace_append hprefix tailTrace_3198705
  have hstable : (prefixWord ++ tailWord_3198705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198705).length < 2 ^ (prefixWord ++ tailWord_3198705).sum := by decide
  have hdescent : baseEnd_3198705 < baseStart_3198705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198793 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 2, 5]
def baseStart_3198793 : Nat := 118140960795 + 3198793 * 2 ^ 59
def prefixEnd_3198793 : Nat := 4983230072969 + 3 ^ 40 * 3198793 * 2
def baseEnd_3198793 : Nat := 1095012215491738960917683

theorem tailTrace_3198793 : CollatzResearch.WordTrace tailWord_3198793 prefixEnd_3198793 1095012215491738960917683 := by
  unfold tailWord_3198793
  simp only [CollatzResearch.WordTrace]
  refine ⟨116669565500326746195521033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77779710333551164130347355 116669565500326746195521033)
  ·
    refine ⟨87502174125245059646640775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116669565500326746195521033 87502174125245059646640775)
    ·
      refine ⟨131253261187867589469961163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87502174125245059646640775 131253261187867589469961163)
      ·
        refine ⟨196879891781801384204941745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131253261187867589469961163 196879891781801384204941745)
        ·
          refine ⟨147659918836351038153706309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196879891781801384204941745 147659918836351038153706309)
          ·
            refine ⟨27686234781815819653819933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147659918836351038153706309 27686234781815819653819933)
            ·
              refine ⟨10382338043180932370182475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27686234781815819653819933 10382338043180932370182475)
              ·
                refine ⟨15573507064771398555273713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10382338043180932370182475 15573507064771398555273713)
                ·
                  refine ⟨11680130298578548916455285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15573507064771398555273713 11680130298578548916455285)
                  ·
                    refine ⟨1095012215491738960917683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11680130298578548916455285 1095012215491738960917683)
                    ·
                      rfl

theorem cell22_3198793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_3198793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198793 prefixEnd_3198793 := by exact prefixLift 3198793
  have htrace : WordTrace (prefixWord ++ tailWord_3198793) baseStart_3198793 baseEnd_3198793 := by
    simpa [prefixWord, tailWord_3198793, baseEnd_3198793] using wordTrace_append hprefix tailTrace_3198793
  have hstable : (prefixWord ++ tailWord_3198793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198793).length < 2 ^ (prefixWord ++ tailWord_3198793).sum := by decide
  have hdescent : baseEnd_3198793 < baseStart_3198793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198823 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 8]
def baseStart_3198823 : Nat := 118140960795 + 3198823 * 2 ^ 59
def prefixEnd_3198823 : Nat := 4983230072969 + 3 ^ 40 * 3198823 * 2
def baseEnd_3198823 : Nat := 365007495034942960889197

theorem tailTrace_3198823 : CollatzResearch.WordTrace tailWord_3198823 prefixEnd_3198823 365007495034942960889197 := by
  unfold tailWord_3198823
  simp only [CollatzResearch.WordTrace]
  refine ⟨116670659690218061319113123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77780439793478707546075415 116670659690218061319113123)
  ·
    refine ⟨175005989535327091978669685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116670659690218061319113123 175005989535327091978669685)
    ·
      refine ⟨16406811518936914873000283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175005989535327091978669685 16406811518936914873000283)
      ·
        refine ⟨24610217278405372309500425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16406811518936914873000283 24610217278405372309500425)
        ·
          refine ⟨18457662958804029232125319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24610217278405372309500425 18457662958804029232125319)
          ·
            refine ⟨27686494438206043848187979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18457662958804029232125319 27686494438206043848187979)
            ·
              refine ⟨41529741657309065772281969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27686494438206043848187979 41529741657309065772281969)
              ·
                refine ⟨31147306242981799329211477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41529741657309065772281969 31147306242981799329211477)
                ·
                  refine ⟨365007495034942960889197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31147306242981799329211477 365007495034942960889197)
                  ·
                    rfl

theorem cell22_3198823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 8].length) (baseStart_3198823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198823 prefixEnd_3198823 := by exact prefixLift 3198823
  have htrace : WordTrace (prefixWord ++ tailWord_3198823) baseStart_3198823 baseEnd_3198823 := by
    simpa [prefixWord, tailWord_3198823, baseEnd_3198823] using wordTrace_append hprefix tailTrace_3198823
  have hstable : (prefixWord ++ tailWord_3198823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198823).length < 2 ^ (prefixWord ++ tailWord_3198823).sum := by decide
  have hdescent : baseEnd_3198823 < baseStart_3198823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198853 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_3198853 : Nat := 118140960795 + 3198853 * 2 ^ 59
def prefixEnd_3198853 : Nat := 4983230072969 + 3 ^ 40 * 3198853 * 2
def baseEnd_3198853 : Nat := 1095032754717918804417499

theorem tailTrace_3198853 : CollatzResearch.WordTrace tailWord_3198853 prefixEnd_3198853 1095032754717918804417499 := by
  unfold tailWord_3198853
  simp only [CollatzResearch.WordTrace]
  refine ⟨116671753880109376442705213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77781169253406250961803475 116671753880109376442705213)
  ·
    refine ⟨43751907705041016166014455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116671753880109376442705213 43751907705041016166014455)
    ·
      refine ⟨65627861557561524249021683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43751907705041016166014455 65627861557561524249021683)
      ·
        refine ⟨98441792336342286373532525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65627861557561524249021683 98441792336342286373532525)
        ·
          refine ⟨36915672126128357390074697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98441792336342286373532525 36915672126128357390074697)
          ·
            refine ⟨27686754094596268042556023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36915672126128357390074697 27686754094596268042556023)
            ·
              refine ⟨41530131141894402063834035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27686754094596268042556023 41530131141894402063834035)
              ·
                refine ⟨62295196712841603095751053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41530131141894402063834035 62295196712841603095751053)
                ·
                  refine ⟨23360698767315601160906645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62295196712841603095751053 23360698767315601160906645)
                  ·
                    refine ⟨1095032754717918804417499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23360698767315601160906645 1095032754717918804417499)
                    ·
                      rfl

theorem cell22_3198853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_3198853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198853 prefixEnd_3198853 := by exact prefixLift 3198853
  have htrace : WordTrace (prefixWord ++ tailWord_3198853) baseStart_3198853 baseEnd_3198853 := by
    simpa [prefixWord, tailWord_3198853, baseEnd_3198853] using wordTrace_append hprefix tailTrace_3198853
  have hstable : (prefixWord ++ tailWord_3198853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198853).length < 2 ^ (prefixWord ++ tailWord_3198853).sum := by decide
  have hdescent : baseEnd_3198853 < baseStart_3198853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198874 : List Nat := [3, 1, 1, 4, 2, 3, 1, 3, 4]
def baseStart_3198874 : Nat := 118140960795 + 3198874 * 2 ^ 59
def prefixEnd_3198874 : Nat := 4983230072969 + 3 ^ 40 * 3198874 * 2
def baseEnd_3198874 : Nat := 365013314482360583214145

theorem tailTrace_3198874 : CollatzResearch.WordTrace tailWord_3198874 prefixEnd_3198874 365013314482360583214145 := by
  unfold tailWord_3198874
  simp only [CollatzResearch.WordTrace]
  refine ⟨29168129953258324257304919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77781679875355531352813117 29168129953258324257304919)
  ·
    refine ⟨43752194929887486385957379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29168129953258324257304919 43752194929887486385957379)
    ·
      refine ⟨65628292394831229578936069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43752194929887486385957379 65628292394831229578936069)
      ·
        refine ⟨12305304824030855546050513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65628292394831229578936069 12305304824030855546050513)
        ·
          refine ⟨9228978618023141659537885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12305304824030855546050513 9228978618023141659537885)
          ·
            refine ⟨3460866981758678122326707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9228978618023141659537885 3460866981758678122326707)
            ·
              refine ⟨5191300472638017183490061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460866981758678122326707 5191300472638017183490061)
              ·
                refine ⟨1946737677239256443808773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5191300472638017183490061 1946737677239256443808773)
                ·
                  refine ⟨365013314482360583214145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1946737677239256443808773 365013314482360583214145)
                  ·
                    rfl

theorem cell22_3198874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_3198874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198874 prefixEnd_3198874 := by exact prefixLift 3198874
  have htrace : WordTrace (prefixWord ++ tailWord_3198874) baseStart_3198874 baseEnd_3198874 := by
    simpa [prefixWord, tailWord_3198874, baseEnd_3198874] using wordTrace_append hprefix tailTrace_3198874
  have hstable : (prefixWord ++ tailWord_3198874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198874).length < 2 ^ (prefixWord ++ tailWord_3198874).sum := by decide
  have hdescent : baseEnd_3198874 < baseStart_3198874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198887 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3198887 : Nat := 118140960795 + 3198887 * 2 ^ 59
def prefixEnd_3198887 : Nat := 4983230072969 + 3 ^ 40 * 3198887 * 2
def baseEnd_3198887 : Nat := 1095044393612754049067395

theorem tailTrace_3198887 : CollatzResearch.WordTrace tailWord_3198887 prefixEnd_3198887 1095044393612754049067395 := by
  unfold tailWord_3198887
  simp only [CollatzResearch.WordTrace]
  refine ⟨116672993961986200249442915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77781995974657466832961943 116672993961986200249442915)
  ·
    refine ⟨175009490942979300374164373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116672993961986200249442915 175009490942979300374164373)
    ·
      refine ⟨8203569887952154705038955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175009490942979300374164373 8203569887952154705038955)
      ·
        refine ⟨12305354831928232057558433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8203569887952154705038955 12305354831928232057558433)
        ·
          refine ⟨9229016123946174043168825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12305354831928232057558433 9229016123946174043168825)
          ·
            refine ⟨6921762092959630532376619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9229016123946174043168825 6921762092959630532376619)
            ·
              refine ⟨10382643139439445798564929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6921762092959630532376619 10382643139439445798564929)
              ·
                refine ⟨7786982354579584348923697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10382643139439445798564929 7786982354579584348923697)
                ·
                  refine ⟨5840236765934688261692773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7786982354579584348923697 5840236765934688261692773)
                  ·
                    refine ⟨1095044393612754049067395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5840236765934688261692773 1095044393612754049067395)
                    ·
                      rfl

theorem cell22_3198887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3198887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198887 prefixEnd_3198887 := by exact prefixLift 3198887
  have htrace : WordTrace (prefixWord ++ tailWord_3198887) baseStart_3198887 baseEnd_3198887 := by
    simpa [prefixWord, tailWord_3198887, baseEnd_3198887] using wordTrace_append hprefix tailTrace_3198887
  have hstable : (prefixWord ++ tailWord_3198887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198887).length < 2 ^ (prefixWord ++ tailWord_3198887).sum := by decide
  have hdescent : baseEnd_3198887 < baseStart_3198887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198947 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 5]
def baseStart_3198947 : Nat := 118140960795 + 3198947 * 2 ^ 59
def prefixEnd_3198947 : Nat := 4983230072969 + 3 ^ 40 * 3198947 * 2
def baseEnd_3198947 : Nat := 365021644279644630855737

theorem tailTrace_3198947 : CollatzResearch.WordTrace tailWord_3198947 prefixEnd_3198947 365021644279644630855737 := by
  unfold tailWord_3198947
  simp only [CollatzResearch.WordTrace]
  refine ⟨116675182341768830496627095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77783454894512553664418063 116675182341768830496627095)
  ·
    refine ⟨175012773512653245744940643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116675182341768830496627095 175012773512653245744940643)
    ·
      refine ⟨262519160268979868617410965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175012773512653245744940643 262519160268979868617410965)
      ·
        refine ⟨12305585637608431341441139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 262519160268979868617410965 12305585637608431341441139)
        ·
          refine ⟨18458378456412647012161709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12305585637608431341441139 18458378456412647012161709)
          ·
            refine ⟨6921891921154742629560641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18458378456412647012161709 6921891921154742629560641)
            ·
              refine ⟨5191418940866056972170481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6921891921154742629560641 5191418940866056972170481)
              ·
                refine ⟨3893564205649542729127861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5191418940866056972170481 3893564205649542729127861)
                ·
                  refine ⟨365021644279644630855737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3893564205649542729127861 365021644279644630855737)
                  ·
                    rfl

theorem cell22_3198947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 5].length) (baseStart_3198947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198947 prefixEnd_3198947 := by exact prefixLift 3198947
  have htrace : WordTrace (prefixWord ++ tailWord_3198947) baseStart_3198947 baseEnd_3198947 := by
    simpa [prefixWord, tailWord_3198947, baseEnd_3198947] using wordTrace_append hprefix tailTrace_3198947
  have hstable : (prefixWord ++ tailWord_3198947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198947).length < 2 ^ (prefixWord ++ tailWord_3198947).sum := by decide
  have hdescent : baseEnd_3198947 < baseStart_3198947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198951 : List Nat := [1, 1, 5, 2, 3, 1, 1, 4, 1, 3]
def baseStart_3198951 : Nat := 118140960795 + 3198951 * 2 ^ 59
def prefixEnd_3198951 : Nat := 4983230072969 + 3 ^ 40 * 3198951 * 2
def baseEnd_3198951 : Nat := 1095066302120679215467199

theorem tailTrace_3198951 : CollatzResearch.WordTrace tailWord_3198951 prefixEnd_3198951 1095066302120679215467199 := by
  unfold tailWord_3198951
  simp only [CollatzResearch.WordTrace]
  refine ⟨116675328233754339179772707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77783552155836226119848471 116675328233754339179772707)
  ·
    refine ⟨175012992350631508769659061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116675328233754339179772707 175012992350631508769659061)
    ·
      refine ⟨16407468032871703947155537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175012992350631508769659061 16407468032871703947155537)
      ·
        refine ⟨12305601024653777960366653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16407468032871703947155537 12305601024653777960366653)
        ·
          refine ⟨4614600384245166735137495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12305601024653777960366653 4614600384245166735137495)
          ·
            refine ⟨6921900576367750102706243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614600384245166735137495 6921900576367750102706243)
            ·
              refine ⟨10382850864551625154059365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6921900576367750102706243 10382850864551625154059365)
              ·
                refine ⟨1946784537103429716386131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10382850864551625154059365 1946784537103429716386131)
                ·
                  refine ⟨2920176805655144574579197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946784537103429716386131 2920176805655144574579197)
                  ·
                    refine ⟨1095066302120679215467199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2920176805655144574579197 1095066302120679215467199)
                    ·
                      rfl

theorem cell22_3198951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_3198951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198951 prefixEnd_3198951 := by exact prefixLift 3198951
  have htrace : WordTrace (prefixWord ++ tailWord_3198951) baseStart_3198951 baseEnd_3198951 := by
    simpa [prefixWord, tailWord_3198951, baseEnd_3198951] using wordTrace_append hprefix tailTrace_3198951
  have hstable : (prefixWord ++ tailWord_3198951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198951).length < 2 ^ (prefixWord ++ tailWord_3198951).sum := by decide
  have hdescent : baseEnd_3198951 < baseStart_3198951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198960 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 3, 4]
def baseStart_3198960 : Nat := 118140960795 + 3198960 * 2 ^ 59
def prefixEnd_3198960 : Nat := 4983230072969 + 3 ^ 40 * 3198960 * 2
def baseEnd_3198960 : Nat := 1095069383004606191992171

theorem tailTrace_3198960 : CollatzResearch.WordTrace tailWord_3198960 prefixEnd_3198960 1095069383004606191992171 := by
  unfold tailWord_3198960
  simp only [CollatzResearch.WordTrace]
  refine ⟨58337828245360866858425167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77783770993814489144566889 58337828245360866858425167)
  ·
    refine ⟨87506742368041300287637751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58337828245360866858425167 87506742368041300287637751)
    ·
      refine ⟨131260113552061950431456627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87506742368041300287637751 131260113552061950431456627)
      ·
        refine ⟨196890170328092925647184941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131260113552061950431456627 196890170328092925647184941)
        ·
          refine ⟨73833813873034847117694353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196890170328092925647184941 73833813873034847117694353)
          ·
            refine ⟨55375360404776135338270765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73833813873034847117694353 55375360404776135338270765)
            ·
              refine ⟨20765760151791050751851537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55375360404776135338270765 20765760151791050751851537)
              ·
                refine ⟨15574320113843288063888653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20765760151791050751851537 15574320113843288063888653)
                ·
                  refine ⟨5840370042691233023958245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15574320113843288063888653 5840370042691233023958245)
                  ·
                    refine ⟨1095069383004606191992171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5840370042691233023958245 1095069383004606191992171)
                    ·
                      rfl

theorem cell22_3198960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_3198960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198960 prefixEnd_3198960 := by exact prefixLift 3198960
  have htrace : WordTrace (prefixWord ++ tailWord_3198960) baseStart_3198960 baseEnd_3198960 := by
    simpa [prefixWord, tailWord_3198960, baseEnd_3198960] using wordTrace_append hprefix tailTrace_3198960
  have hstable : (prefixWord ++ tailWord_3198960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198960).length < 2 ^ (prefixWord ++ tailWord_3198960).sum := by decide
  have hdescent : baseEnd_3198960 < baseStart_3198960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3198977 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3198977 : Nat := 118140960795 + 3198977 * 2 ^ 59
def prefixEnd_3198977 : Nat := 4983230072969 + 3 ^ 40 * 3198977 * 2
def baseEnd_3198977 : Nat := 1095075202452023814317119

theorem tailTrace_3198977 : CollatzResearch.WordTrace tailWord_3198977 prefixEnd_3198977 1095075202452023814317119 := by
  unfold tailWord_3198977
  simp only [CollatzResearch.WordTrace]
  refine ⟨116676276531660145620219185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77784184354440097080146123 116676276531660145620219185)
  ·
    refine ⟨87507207398745109215164389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116676276531660145620219185 87507207398745109215164389)
    ·
      refine ⟨16407601387264707977843323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87507207398745109215164389 16407601387264707977843323)
      ·
        refine ⟨24611402080897061966764985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16407601387264707977843323 24611402080897061966764985)
        ·
          refine ⟨18458551560672796475073739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24611402080897061966764985 18458551560672796475073739)
          ·
            refine ⟨27687827341009194712610609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18458551560672796475073739 27687827341009194712610609)
            ·
              refine ⟨20765870505756896034457957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27687827341009194712610609 20765870505756896034457957)
              ·
                refine ⟨3893600719829418006460867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20765870505756896034457957 3893600719829418006460867)
                ·
                  refine ⟨5840401079744127009691301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893600719829418006460867 5840401079744127009691301)
                  ·
                    refine ⟨1095075202452023814317119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5840401079744127009691301 1095075202452023814317119)
                    ·
                      rfl

theorem cell22_3198977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3198977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3198977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3198977 prefixEnd_3198977 := by exact prefixLift 3198977
  have htrace : WordTrace (prefixWord ++ tailWord_3198977) baseStart_3198977 baseEnd_3198977 := by
    simpa [prefixWord, tailWord_3198977, baseEnd_3198977] using wordTrace_append hprefix tailTrace_3198977
  have hstable : (prefixWord ++ tailWord_3198977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3198977).length < 2 ^ (prefixWord ++ tailWord_3198977).sum := by decide
  have hdescent : baseEnd_3198977 < baseStart_3198977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3198977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199007 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 4, 3]
def baseStart_3199007 : Nat := 118140960795 + 3199007 * 2 ^ 59
def prefixEnd_3199007 : Nat := 4983230072969 + 3 ^ 40 * 3199007 * 2
def baseEnd_3199007 : Nat := 1095085472065113736067027

theorem tailTrace_3199007 : CollatzResearch.WordTrace tailWord_3199007 prefixEnd_3199007 1095085472065113736067027 := by
  unfold tailWord_3199007
  simp only [CollatzResearch.WordTrace]
  refine ⟨116677370721551460743811275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77784913814367640495874183 116677370721551460743811275)
  ·
    refine ⟨175016056082327191115716913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116677370721551460743811275 175016056082327191115716913)
    ·
      refine ⟨131262042061745393336787685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175016056082327191115716913 131262042061745393336787685)
      ·
        refine ⟨24611632886577261250647691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131262042061745393336787685 24611632886577261250647691)
        ·
          refine ⟨36917449329865891875971537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24611632886577261250647691 36917449329865891875971537)
          ·
            refine ⟨27688086997399418906978653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36917449329865891875971537 27688086997399418906978653)
            ·
              refine ⟨10383032624024782090116995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27688086997399418906978653 10383032624024782090116995)
              ·
                refine ⟨15574548936037173135175493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10383032624024782090116995 15574548936037173135175493)
                ·
                  refine ⟨2920227925506969962845405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15574548936037173135175493 2920227925506969962845405)
                  ·
                    refine ⟨1095085472065113736067027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2920227925506969962845405 1095085472065113736067027)
                    ·
                      rfl

theorem cell22_3199007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 3].length) (baseStart_3199007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199007 prefixEnd_3199007 := by exact prefixLift 3199007
  have htrace : WordTrace (prefixWord ++ tailWord_3199007) baseStart_3199007 baseEnd_3199007 := by
    simpa [prefixWord, tailWord_3199007, baseEnd_3199007] using wordTrace_append hprefix tailTrace_3199007
  have hstable : (prefixWord ++ tailWord_3199007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199007).length < 2 ^ (prefixWord ++ tailWord_3199007).sum := by decide
  have hdescent : baseEnd_3199007 < baseStart_3199007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199022 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3199022 : Nat := 118140960795 + 3199022 * 2 ^ 59
def prefixEnd_3199022 : Nat := 4983230072969 + 3 ^ 40 * 3199022 * 2
def baseEnd_3199022 : Nat := 1095090606871658696941981

theorem tailTrace_3199022 : CollatzResearch.WordTrace tailWord_3199022 prefixEnd_3199022 1095090606871658696941981 := by
  unfold tailWord_3199022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14584739727062139788200915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77785278544331412203738213 14584739727062139788200915)
  ·
    refine ⟨21877109590593209682301373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14584739727062139788200915 21877109590593209682301373)
    ·
      refine ⟨8203916096472453630863015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21877109590593209682301373 8203916096472453630863015)
      ·
        refine ⟨12305874144708680446294523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8203916096472453630863015 12305874144708680446294523)
        ·
          refine ⟨18458811217063020669441785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12305874144708680446294523 18458811217063020669441785)
          ·
            refine ⟨13844108412797265502081339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18458811217063020669441785 13844108412797265502081339)
            ·
              refine ⟨20766162619195898253122009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13844108412797265502081339 20766162619195898253122009)
              ·
                refine ⟨15574621964396923689841507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20766162619195898253122009 15574621964396923689841507)
                ·
                  refine ⟨23361932946595385534762261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15574621964396923689841507 23361932946595385534762261)
                  ·
                    refine ⟨1095090606871658696941981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23361932946595385534762261 1095090606871658696941981)
                    ·
                      rfl

theorem cell22_3199022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3199022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199022 prefixEnd_3199022 := by exact prefixLift 3199022
  have htrace : WordTrace (prefixWord ++ tailWord_3199022) baseStart_3199022 baseEnd_3199022 := by
    simpa [prefixWord, tailWord_3199022, baseEnd_3199022] using wordTrace_append hprefix tailTrace_3199022
  have hstable : (prefixWord ++ tailWord_3199022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199022).length < 2 ^ (prefixWord ++ tailWord_3199022).sum := by decide
  have hdescent : baseEnd_3199022 < baseStart_3199022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199050 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_3199050 : Nat := 118140960795 + 3199050 * 2 ^ 59
def prefixEnd_3199050 : Nat := 4983230072969 + 3 ^ 40 * 3199050 * 2
def baseEnd_3199050 : Nat := 1095100191843875957241895

theorem tailTrace_3199050 : CollatzResearch.WordTrace tailWord_3199050 prefixEnd_3199050 1095100191843875957241895 := by
  unfold tailWord_3199050
  simp only [CollatzResearch.WordTrace]
  refine ⟨29169734765098919771906651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77785959373597119391751069 29169734765098919771906651)
  ·
    refine ⟨43754602147648379657859977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29169734765098919771906651 43754602147648379657859977)
    ·
      refine ⟨32815951610736284743394983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43754602147648379657859977 32815951610736284743394983)
      ·
        refine ⟨49223927416104427115092475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32815951610736284743394983 49223927416104427115092475)
        ·
          refine ⟨73835891124156640672638713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49223927416104427115092475 73835891124156640672638713)
          ·
            refine ⟨55376918343117480504479035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73835891124156640672638713 55376918343117480504479035)
            ·
              refine ⟨83065377514676220756718553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55376918343117480504479035 83065377514676220756718553)
              ·
                refine ⟨62299033136007165567538915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83065377514676220756718553 62299033136007165567538915)
                ·
                  refine ⟨93448549704010748351308373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62299033136007165567538915 93448549704010748351308373)
                  ·
                    refine ⟨1095100191843875957241895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93448549704010748351308373 1095100191843875957241895)
                    ·
                      rfl

theorem cell22_3199050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_3199050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199050 prefixEnd_3199050 := by exact prefixLift 3199050
  have htrace : WordTrace (prefixWord ++ tailWord_3199050) baseStart_3199050 baseEnd_3199050 := by
    simpa [prefixWord, tailWord_3199050, baseEnd_3199050] using wordTrace_append hprefix tailTrace_3199050
  have hstable : (prefixWord ++ tailWord_3199050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199050).length < 2 ^ (prefixWord ++ tailWord_3199050).sum := by decide
  have hdescent : baseEnd_3199050 < baseStart_3199050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199052 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 5, 3]
def baseStart_3199052 : Nat := 118140960795 + 3199052 * 2 ^ 59
def prefixEnd_3199052 : Nat := 4983230072969 + 3 ^ 40 * 3199052 * 2
def baseEnd_3199052 : Nat := 1095100876484748618691889

theorem tailTrace_3199052 : CollatzResearch.WordTrace tailWord_3199052 prefixEnd_3199052 1095100876484748618691889 := by
  unfold tailWord_3199052
  simp only [CollatzResearch.WordTrace]
  refine ⟨58339506003194216714599705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77786008004258955619466273 58339506003194216714599705)
  ·
    refine ⟨43754629502395662535949779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58339506003194216714599705 43754629502395662535949779)
    ·
      refine ⟨65631944253593493803924669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43754629502395662535949779 65631944253593493803924669)
      ·
        refine ⟨24611979095097560176471751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65631944253593493803924669 24611979095097560176471751)
        ·
          refine ⟨36917968642646340264707627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24611979095097560176471751 36917968642646340264707627)
          ·
            refine ⟨55376952963969510397061441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36917968642646340264707627 55376952963969510397061441)
            ·
              refine ⟨41532714722977132797796081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55376952963969510397061441 41532714722977132797796081)
              ·
                refine ⟨31149536042232849598347061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41532714722977132797796081 31149536042232849598347061)
                ·
                  refine ⟨2920269003959329649845037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31149536042232849598347061 2920269003959329649845037)
                  ·
                    refine ⟨1095100876484748618691889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2920269003959329649845037 1095100876484748618691889)
                    ·
                      rfl

theorem cell22_3199052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_3199052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199052 prefixEnd_3199052 := by exact prefixLift 3199052
  have htrace : WordTrace (prefixWord ++ tailWord_3199052) baseStart_3199052 baseEnd_3199052 := by
    simpa [prefixWord, tailWord_3199052, baseEnd_3199052] using wordTrace_append hprefix tailTrace_3199052
  have hstable : (prefixWord ++ tailWord_3199052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199052).length < 2 ^ (prefixWord ++ tailWord_3199052).sum := by decide
  have hdescent : baseEnd_3199052 < baseStart_3199052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199065 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 7]
def baseStart_3199065 : Nat := 118140960795 + 3199065 * 2 ^ 59
def prefixEnd_3199065 : Nat := 4983230072969 + 3 ^ 40 * 3199065 * 2
def baseEnd_3199065 : Nat := 365035108883473639372283

theorem tailTrace_3199065 : CollatzResearch.WordTrace tailWord_3199065 prefixEnd_3199065 365035108883473639372283 := by
  unfold tailWord_3199065
  simp only [CollatzResearch.WordTrace]
  refine ⟨116679486155341336649422649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77786324103560891099615099 116679486155341336649422649)
  ·
    refine ⟨87509614616506002487066987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116679486155341336649422649 87509614616506002487066987)
    ·
      refine ⟨131264421924759003730600481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87509614616506002487066987 131264421924759003730600481)
      ·
        refine ⟨98448316443569252797950361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131264421924759003730600481 98448316443569252797950361)
        ·
          refine ⟨73836237332676939598462771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98448316443569252797950361 73836237332676939598462771)
          ·
            refine ⟨110754355999015409397694157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73836237332676939598462771 110754355999015409397694157)
            ·
              refine ⟨41532883499630778524135309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110754355999015409397694157 41532883499630778524135309)
              ·
                refine ⟨15574831312361541946550741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41532883499630778524135309 15574831312361541946550741)
                ·
                  refine ⟨365035108883473639372283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15574831312361541946550741 365035108883473639372283)
                  ·
                    rfl

theorem cell22_3199065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_3199065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199065 prefixEnd_3199065 := by exact prefixLift 3199065
  have htrace : WordTrace (prefixWord ++ tailWord_3199065) baseStart_3199065 baseEnd_3199065 := by
    simpa [prefixWord, tailWord_3199065, baseEnd_3199065] using wordTrace_append hprefix tailTrace_3199065
  have hstable : (prefixWord ++ tailWord_3199065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199065).length < 2 ^ (prefixWord ++ tailWord_3199065).sum := by decide
  have hdescent : baseEnd_3199065 < baseStart_3199065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199217 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 7]
def baseStart_3199217 : Nat := 118140960795 + 3199217 * 2 ^ 59
def prefixEnd_3199217 : Nat := 4983230072969 + 3 ^ 40 * 3199217 * 2
def baseEnd_3199217 : Nat := 365052453118914396105461

theorem tailTrace_3199217 : CollatzResearch.WordTrace tailWord_3199217 prefixEnd_3199217 365052453118914396105461 := by
  unfold tailWord_3199217
  simp only [CollatzResearch.WordTrace]
  refine ⟨116685030050790666608955905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77790020033860444405970603 116685030050790666608955905)
  ·
    refine ⟨87513772538092999956716929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116685030050790666608955905 87513772538092999956716929)
    ·
      refine ⟨65635329403569749967537697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87513772538092999956716929 65635329403569749967537697)
      ·
        refine ⟨49226497052677312475653273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65635329403569749967537697 49226497052677312475653273)
        ·
          refine ⟨36919872789507984356739955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49226497052677312475653273 36919872789507984356739955)
          ·
            refine ⟨55379809184261976535109933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36919872789507984356739955 55379809184261976535109933)
            ·
              refine ⟨20767428444098241200666225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55379809184261976535109933 20767428444098241200666225)
              ·
                refine ⟨15575571333073680900499669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20767428444098241200666225 15575571333073680900499669)
                ·
                  refine ⟨365052453118914396105461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15575571333073680900499669 365052453118914396105461)
                  ·
                    rfl

theorem cell22_3199217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_3199217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199217 prefixEnd_3199217 := by exact prefixLift 3199217
  have htrace : WordTrace (prefixWord ++ tailWord_3199217) baseStart_3199217 baseEnd_3199217 := by
    simpa [prefixWord, tailWord_3199217, baseEnd_3199217] using wordTrace_append hprefix tailTrace_3199217
  have hstable : (prefixWord ++ tailWord_3199217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199217).length < 2 ^ (prefixWord ++ tailWord_3199217).sum := by decide
  have hdescent : baseEnd_3199217 < baseStart_3199217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199232 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_3199232 : Nat := 118140960795 + 3199232 * 2 ^ 59
def prefixEnd_3199232 : Nat := 4983230072969 + 3 ^ 40 * 3199232 * 2
def baseEnd_3199232 : Nat := 1095162494163288149191337

theorem tailTrace_3199232 : CollatzResearch.WordTrace tailWord_3199232 prefixEnd_3199232 1095162494163288149191337 := by
  unfold tailWord_3199232
  simp only [CollatzResearch.WordTrace]
  refine ⟨58342788572868162085375975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77790384763824216113834633 58342788572868162085375975)
  ·
    refine ⟨87514182859302243128063963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58342788572868162085375975 87514182859302243128063963)
    ·
      refine ⟨131271274288953364692095945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87514182859302243128063963 131271274288953364692095945)
      ·
        refine ⟨98453455716715023519071959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131271274288953364692095945 98453455716715023519071959)
        ·
          refine ⟨147680183575072535278607939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98453455716715023519071959 147680183575072535278607939)
          ·
            refine ⟨221520275362608802917911909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147680183575072535278607939 221520275362608802917911909)
            ·
              refine ⟨41535051630489150547108483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 221520275362608802917911909 41535051630489150547108483)
              ·
                refine ⟨62302577445733725820662725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41535051630489150547108483 62302577445733725820662725)
                ·
                  refine ⟨11681733271075073591374261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62302577445733725820662725 11681733271075073591374261)
                  ·
                    refine ⟨1095162494163288149191337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11681733271075073591374261 1095162494163288149191337)
                    ·
                      rfl

theorem cell22_3199232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_3199232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199232 prefixEnd_3199232 := by exact prefixLift 3199232
  have htrace : WordTrace (prefixWord ++ tailWord_3199232) baseStart_3199232 baseEnd_3199232 := by
    simpa [prefixWord, tailWord_3199232, baseEnd_3199232] using wordTrace_append hprefix tailTrace_3199232
  have hstable : (prefixWord ++ tailWord_3199232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199232).length < 2 ^ (prefixWord ++ tailWord_3199232).sum := by decide
  have hdescent : baseEnd_3199232 < baseStart_3199232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199307 : List Nat := [1, 1, 1, 1, 3, 1, 1, 13]
def baseStart_3199307 : Nat := 118140960795 + 3199307 * 2 ^ 59
def prefixEnd_3199307 : Nat := 4983230072969 + 3 ^ 40 * 3199307 * 2
def baseEnd_3199307 : Nat := 121687574244001439285123

theorem tailTrace_3199307 : CollatzResearch.WordTrace tailWord_3199307 prefixEnd_3199307 121687574244001439285123 := by
  unfold tailWord_3199307
  simp only [CollatzResearch.WordTrace]
  refine ⟨116688312620464611979732175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77792208413643074653154783 116688312620464611979732175)
  ·
    refine ⟨175032468930696917969598263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116688312620464611979732175 175032468930696917969598263)
    ·
      refine ⟨262548703396045376954397395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175032468930696917969598263 262548703396045376954397395)
      ·
        refine ⟨393823055094068065431596093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262548703396045376954397395 393823055094068065431596093)
        ·
          refine ⟨147683645660275524536848535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 393823055094068065431596093 147683645660275524536848535)
          ·
            refine ⟨221525468490413286805272803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147683645660275524536848535 221525468490413286805272803)
            ·
              refine ⟨332288202735619930207909205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221525468490413286805272803 332288202735619930207909205)
              ·
                refine ⟨121687574244001439285123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 332288202735619930207909205 121687574244001439285123)
                ·
                  rfl

theorem cell22_3199307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 13].length) (baseStart_3199307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199307 prefixEnd_3199307 := by exact prefixLift 3199307
  have htrace : WordTrace (prefixWord ++ tailWord_3199307) baseStart_3199307 baseEnd_3199307 := by
    simpa [prefixWord, tailWord_3199307, baseEnd_3199307] using wordTrace_append hprefix tailTrace_3199307
  have hstable : (prefixWord ++ tailWord_3199307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199307).length < 2 ^ (prefixWord ++ tailWord_3199307).sum := by decide
  have hdescent : baseEnd_3199307 < baseStart_3199307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199362 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3199362 : Nat := 118140960795 + 3199362 * 2 ^ 59
def prefixEnd_3199362 : Nat := 4983230072969 + 3 ^ 40 * 3199362 * 2
def baseEnd_3199362 : Nat := 1095206995820011143440939

theorem tailTrace_3199362 : CollatzResearch.WordTrace tailWord_3199362 prefixEnd_3199362 1095206995820011143440939 := by
  unfold tailWord_3199362
  simp only [CollatzResearch.WordTrace]
  refine ⟨29172579658816339093246085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77793545756843570915322893 29172579658816339093246085)
  ·
    refine ⟨5469858686028063579983641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29172579658816339093246085 5469858686028063579983641)
    ·
      refine ⟨4102394014521047684987731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5469858686028063579983641 4102394014521047684987731)
      ·
        refine ⟨6153591021781571527481597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4102394014521047684987731 6153591021781571527481597)
        ·
          refine ⟨2307596633168089322805599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6153591021781571527481597 2307596633168089322805599)
          ·
            refine ⟨3461394949752133984208399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307596633168089322805599 3461394949752133984208399)
            ·
              refine ⟨5192092424628200976312599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461394949752133984208399 5192092424628200976312599)
              ·
                refine ⟨7788138636942301464468899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5192092424628200976312599 7788138636942301464468899)
                ·
                  refine ⟨11682207955413452196703349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7788138636942301464468899 11682207955413452196703349)
                  ·
                    refine ⟨1095206995820011143440939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11682207955413452196703349 1095206995820011143440939)
                    ·
                      rfl

theorem cell22_3199362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3199362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199362 prefixEnd_3199362 := by exact prefixLift 3199362
  have htrace : WordTrace (prefixWord ++ tailWord_3199362) baseStart_3199362 baseEnd_3199362 := by
    simpa [prefixWord, tailWord_3199362, baseEnd_3199362] using wordTrace_append hprefix tailTrace_3199362
  have hstable : (prefixWord ++ tailWord_3199362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199362).length < 2 ^ (prefixWord ++ tailWord_3199362).sum := by decide
  have hdescent : baseEnd_3199362 < baseStart_3199362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199420 : List Nat := [2, 2, 2, 4, 1, 3, 2, 1, 5]
def baseStart_3199420 : Nat := 118140960795 + 3199420 * 2 ^ 59
def prefixEnd_3199420 : Nat := 4983230072969 + 3 ^ 40 * 3199420 * 2
def baseEnd_3199420 : Nat := 365075616801772775163587

theorem tailTrace_3199420 : CollatzResearch.WordTrace tailWord_3199420 prefixEnd_3199420 365075616801772775163587 := by
  unfold tailWord_3199420
  simp only [CollatzResearch.WordTrace]
  refine ⟨58346217034527616139297857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77794956046036821519063809 58346217034527616139297857)
  ·
    refine ⟨43759662775895712104473393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58346217034527616139297857 43759662775895712104473393)
    ·
      refine ⟨32819747081921784078355045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43759662775895712104473393 32819747081921784078355045)
      ·
        refine ⟨6153702577860334514691571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32819747081921784078355045 6153702577860334514691571)
        ·
          refine ⟨9230553866790501772037357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6153702577860334514691571 9230553866790501772037357)
          ·
            refine ⟨3461457700046438164514009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9230553866790501772037357 3461457700046438164514009)
            ·
              refine ⟨2596093275034828623385507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3461457700046438164514009 2596093275034828623385507)
              ·
                refine ⟨3894139912552242935078261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2596093275034828623385507 3894139912552242935078261)
                ·
                  refine ⟨365075616801772775163587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3894139912552242935078261 365075616801772775163587)
                  ·
                    rfl

theorem cell22_3199420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_3199420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199420 prefixEnd_3199420 := by exact prefixLift 3199420
  have htrace : WordTrace (prefixWord ++ tailWord_3199420) baseStart_3199420 baseEnd_3199420 := by
    simpa [prefixWord, tailWord_3199420, baseEnd_3199420] using wordTrace_append hprefix tailTrace_3199420
  have hstable : (prefixWord ++ tailWord_3199420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199420).length < 2 ^ (prefixWord ++ tailWord_3199420).sum := by decide
  have hdescent : baseEnd_3199420 < baseStart_3199420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199429 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_3199429 : Nat := 118140960795 + 3199429 * 2 ^ 59
def prefixEnd_3199429 : Nat := 4983230072969 + 3 ^ 40 * 3199429 * 2
def baseEnd_3199429 : Nat := 1095229931289245302015733

theorem tailTrace_3199429 : CollatzResearch.WordTrace tailWord_3199429 prefixEnd_3199429 1095229931289245302015733 := by
  unfold tailWord_3199429
  simp only [CollatzResearch.WordTrace]
  refine ⟨116692762326022626815673341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77795174884015084543782227 116692762326022626815673341)
  ·
    refine ⟨43759785872258485055877503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116692762326022626815673341 43759785872258485055877503)
    ·
      refine ⟨65639678808387727583816255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43759785872258485055877503 65639678808387727583816255)
      ·
        refine ⟨98459518212581591375724383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65639678808387727583816255 98459518212581591375724383)
        ·
          refine ⟨147689277318872387063586575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98459518212581591375724383 147689277318872387063586575)
          ·
            refine ⟨221533915978308580595379863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147689277318872387063586575 221533915978308580595379863)
            ·
              refine ⟨332300873967462870893069795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221533915978308580595379863 332300873967462870893069795)
              ·
                refine ⟨498451310951194306339604693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332300873967462870893069795 498451310951194306339604693)
                ·
                  refine ⟨11682452600418616554834485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 498451310951194306339604693 11682452600418616554834485)
                  ·
                    refine ⟨1095229931289245302015733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11682452600418616554834485 1095229931289245302015733)
                    ·
                      rfl

theorem cell22_3199429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_3199429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199429 prefixEnd_3199429 := by exact prefixLift 3199429
  have htrace : WordTrace (prefixWord ++ tailWord_3199429) baseStart_3199429 baseEnd_3199429 := by
    simpa [prefixWord, tailWord_3199429, baseEnd_3199429] using wordTrace_append hprefix tailTrace_3199429
  have hstable : (prefixWord ++ tailWord_3199429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199429).length < 2 ^ (prefixWord ++ tailWord_3199429).sum := by decide
  have hdescent : baseEnd_3199429 < baseStart_3199429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199458 : List Nat := [3, 3, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3199458 : Nat := 118140960795 + 3199458 * 2 ^ 59
def prefixEnd_3199458 : Nat := 4983230072969 + 3 ^ 40 * 3199458 * 2
def baseEnd_3199458 : Nat := 1095239858581898893040645

theorem tailTrace_3199458 : CollatzResearch.WordTrace tailWord_3199458 prefixEnd_3199458 1095239858581898893040645 := by
  unfold tailWord_3199458
  simp only [CollatzResearch.WordTrace]
  refine ⟨29173455010729391192119757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77795880028611709845652685 29173455010729391192119757)
  ·
    refine ⟨10940045629023521697044909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29173455010729391192119757 10940045629023521697044909)
    ·
      refine ⟨4102517110883820636391841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10940045629023521697044909 4102517110883820636391841)
      ·
        refine ⟨3076887833162865477293881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4102517110883820636391841 3076887833162865477293881)
        ·
          refine ⟨2307665874872149107970411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3076887833162865477293881 2307665874872149107970411)
          ·
            refine ⟨3461498812308223661955617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307665874872149107970411 3461498812308223661955617)
            ·
              refine ⟨2596124109231167746466713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3461498812308223661955617 2596124109231167746466713)
              ·
                refine ⟨1947093081923375809850035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596124109231167746466713 1947093081923375809850035)
                ·
                  refine ⟨2920639622885063714775053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947093081923375809850035 2920639622885063714775053)
                  ·
                    refine ⟨1095239858581898893040645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2920639622885063714775053 1095239858581898893040645)
                    ·
                      rfl

theorem cell22_3199458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3199458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199458 prefixEnd_3199458 := by exact prefixLift 3199458
  have htrace : WordTrace (prefixWord ++ tailWord_3199458) baseStart_3199458 baseEnd_3199458 := by
    simpa [prefixWord, tailWord_3199458, baseEnd_3199458] using wordTrace_append hprefix tailTrace_3199458
  have hstable : (prefixWord ++ tailWord_3199458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199458).length < 2 ^ (prefixWord ++ tailWord_3199458).sum := by decide
  have hdescent : baseEnd_3199458 < baseStart_3199458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199459 : List Nat := [1, 1, 1, 6, 13]
def baseStart_3199459 : Nat := 118140960795 + 3199459 * 2 ^ 59
def prefixEnd_3199459 : Nat := 4983230072969 + 3 ^ 40 * 3199459 * 2
def baseEnd_3199459 : Nat := 4507161320585741661587

theorem tailTrace_3199459 : CollatzResearch.WordTrace tailWord_3199459 prefixEnd_3199459 4507161320585741661587 := by
  unfold tailWord_3199459
  simp only [CollatzResearch.WordTrace]
  refine ⟨116693856515913941939265431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77795904343942627959510287 116693856515913941939265431)
  ·
    refine ⟨175040784773870912908898147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116693856515913941939265431 175040784773870912908898147)
    ·
      refine ⟨262561177160806369363347221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175040784773870912908898147 262561177160806369363347221)
      ·
        refine ⟨12307555179412798563906901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 262561177160806369363347221 12307555179412798563906901)
        ·
          refine ⟨4507161320585741661587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12307555179412798563906901 4507161320585741661587)
          ·
            rfl

theorem cell22_3199459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 13].length) (baseStart_3199459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199459 prefixEnd_3199459 := by exact prefixLift 3199459
  have htrace : WordTrace (prefixWord ++ tailWord_3199459) baseStart_3199459 baseEnd_3199459 := by
    simpa [prefixWord, tailWord_3199459, baseEnd_3199459] using wordTrace_append hprefix tailTrace_3199459
  have hstable : (prefixWord ++ tailWord_3199459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199459).length < 2 ^ (prefixWord ++ tailWord_3199459).sum := by decide
  have hdescent : baseEnd_3199459 < baseStart_3199459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199495 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 2, 4]
def baseStart_3199495 : Nat := 118140960795 + 3199495 * 2 ^ 59
def prefixEnd_3199495 : Nat := 4983230072969 + 3 ^ 40 * 3199495 * 2
def baseEnd_3199495 : Nat := 1095252524438043129865531

theorem tailTrace_3199495 : CollatzResearch.WordTrace tailWord_3199495 prefixEnd_3199495 1095252524438043129865531 := by
  unfold tailWord_3199495
  simp only [CollatzResearch.WordTrace]
  refine ⟨116695169543783520087575939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77796779695855680058383959 116695169543783520087575939)
  ·
    refine ⟨175042754315675280131363909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116695169543783520087575939 175042754315675280131363909)
    ·
      refine ⟨32820516434189115024630733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175042754315675280131363909 32820516434189115024630733)
      ·
        refine ⟨12307693662820918134236525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32820516434189115024630733 12307693662820918134236525)
        ·
          refine ⟨4615385123557844300338697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12307693662820918134236525 4615385123557844300338697)
          ·
            refine ⟨3461538842668383225254023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4615385123557844300338697 3461538842668383225254023)
            ·
              refine ⟨5192308264002574837881035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461538842668383225254023 5192308264002574837881035)
              ·
                refine ⟨7788462396003862256821553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5192308264002574837881035 7788462396003862256821553)
                ·
                  refine ⟨5841346797002896692616165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7788462396003862256821553 5841346797002896692616165)
                  ·
                    refine ⟨1095252524438043129865531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5841346797002896692616165 1095252524438043129865531)
                    ·
                      rfl

theorem cell22_3199495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_3199495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199495 prefixEnd_3199495 := by exact prefixLift 3199495
  have htrace : WordTrace (prefixWord ++ tailWord_3199495) baseStart_3199495 baseEnd_3199495 := by
    simpa [prefixWord, tailWord_3199495, baseEnd_3199495] using wordTrace_append hprefix tailTrace_3199495
  have hstable : (prefixWord ++ tailWord_3199495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199495).length < 2 ^ (prefixWord ++ tailWord_3199495).sum := by decide
  have hdescent : baseEnd_3199495 < baseStart_3199495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199521 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 7]
def baseStart_3199521 : Nat := 118140960795 + 3199521 * 2 ^ 59
def prefixEnd_3199521 : Nat := 4983230072969 + 3 ^ 40 * 3199521 * 2
def baseEnd_3199521 : Nat := 365087141589795909571817

theorem tailTrace_3199521 : CollatzResearch.WordTrace tailWord_3199521 prefixEnd_3199521 365087141589795909571817 := by
  unfold tailWord_3199521
  simp only [CollatzResearch.WordTrace]
  refine ⟨116696117841689326528022417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77797411894459551018681611 116696117841689326528022417)
  ·
    refine ⟨87522088381266994896016813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116696117841689326528022417 87522088381266994896016813)
    ·
      refine ⟨32820783142975123086006305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87522088381266994896016813 32820783142975123086006305)
      ·
        refine ⟨24615587357231342314504729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32820783142975123086006305 24615587357231342314504729)
        ·
          refine ⟨18461690517923506735878547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24615587357231342314504729 18461690517923506735878547)
          ·
            refine ⟨27692535776885260103817821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18461690517923506735878547 27692535776885260103817821)
            ·
              refine ⟨10384700916331972538931683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27692535776885260103817821 10384700916331972538931683)
              ·
                refine ⟨15577051374497958808397525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10384700916331972538931683 15577051374497958808397525)
                ·
                  refine ⟨365087141589795909571817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15577051374497958808397525 365087141589795909571817)
                  ·
                    rfl

theorem cell22_3199521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_3199521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199521 prefixEnd_3199521 := by exact prefixLift 3199521
  have htrace : WordTrace (prefixWord ++ tailWord_3199521) baseStart_3199521 baseEnd_3199521 := by
    simpa [prefixWord, tailWord_3199521, baseEnd_3199521] using wordTrace_append hprefix tailTrace_3199521
  have hstable : (prefixWord ++ tailWord_3199521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199521).length < 2 ^ (prefixWord ++ tailWord_3199521).sum := by decide
  have hdescent : baseEnd_3199521 < baseStart_3199521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199525 : List Nat := [1, 3, 1, 2, 2, 1, 4, 4, 1, 3]
def baseStart_3199525 : Nat := 118140960795 + 3199525 * 2 ^ 59
def prefixEnd_3199525 : Nat := 4983230072969 + 3 ^ 40 * 3199525 * 2
def baseEnd_3199525 : Nat := 1095262794051133051615439

theorem tailTrace_3199525 : CollatzResearch.WordTrace tailWord_3199525 prefixEnd_3199525 1095262794051133051615439 := by
  unfold tailWord_3199525
  simp only [CollatzResearch.WordTrace]
  refine ⟨116696263733674835211168029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77797509155783223474112019 116696263733674835211168029)
  ·
    refine ⟨43761098900128063204188011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116696263733674835211168029 43761098900128063204188011)
    ·
      refine ⟨65641648350192094806282017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43761098900128063204188011 65641648350192094806282017)
      ·
        refine ⟨49231236262644071104711513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65641648350192094806282017 49231236262644071104711513)
        ·
          refine ⟨36923427196983053328533635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49231236262644071104711513 36923427196983053328533635)
          ·
            refine ⟨55385140795474579992800453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36923427196983053328533635 55385140795474579992800453)
            ·
              refine ⟨10384713899151483748650085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55385140795474579992800453 10384713899151483748650085)
              ·
                refine ⟨1947133856090903202871891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10384713899151483748650085 1947133856090903202871891)
                ·
                  refine ⟨2920700784136354804307837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947133856090903202871891 2920700784136354804307837)
                  ·
                    refine ⟨1095262794051133051615439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2920700784136354804307837 1095262794051133051615439)
                    ·
                      rfl

theorem cell22_3199525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_3199525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199525 prefixEnd_3199525 := by exact prefixLift 3199525
  have htrace : WordTrace (prefixWord ++ tailWord_3199525) baseStart_3199525 baseEnd_3199525 := by
    simpa [prefixWord, tailWord_3199525, baseEnd_3199525] using wordTrace_append hprefix tailTrace_3199525
  have hstable : (prefixWord ++ tailWord_3199525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199525).length < 2 ^ (prefixWord ++ tailWord_3199525).sum := by decide
  have hdescent : baseEnd_3199525 < baseStart_3199525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199536 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 2, 5]
def baseStart_3199536 : Nat := 118140960795 + 3199536 * 2 ^ 59
def prefixEnd_3199536 : Nat := 4983230072969 + 3 ^ 40 * 3199536 * 2
def baseEnd_3199536 : Nat := 1095266559575932689590405

theorem tailTrace_3199536 : CollatzResearch.WordTrace tailWord_3199536 prefixEnd_3199536 1095266559575932689590405 := by
  unfold tailWord_3199536
  simp only [CollatzResearch.WordTrace]
  refine ⟨58348332468317492044909231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77797776624423322726545641 58348332468317492044909231)
  ·
    refine ⟨87522498702476238067363847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58348332468317492044909231 87522498702476238067363847)
    ·
      refine ⟨131283748053714357101045771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87522498702476238067363847 131283748053714357101045771)
      ·
        refine ⟨196925622080571535651568657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131283748053714357101045771 196925622080571535651568657)
        ·
          refine ⟨147694216560428651738676493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196925622080571535651568657 147694216560428651738676493)
          ·
            refine ⟨55385331210160744402003685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147694216560428651738676493 55385331210160744402003685)
            ·
              refine ⟨10384749601905139575375691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55385331210160744402003685 10384749601905139575375691)
              ·
                refine ⟨15577124402857709363063537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10384749601905139575375691 15577124402857709363063537)
                ·
                  refine ⟨11682843302143282022297653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15577124402857709363063537 11682843302143282022297653)
                  ·
                    refine ⟨1095266559575932689590405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11682843302143282022297653 1095266559575932689590405)
                    ·
                      rfl

theorem cell22_3199536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_3199536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199536 prefixEnd_3199536 := by exact prefixLift 3199536
  have htrace : WordTrace (prefixWord ++ tailWord_3199536) baseStart_3199536 baseEnd_3199536 := by
    simpa [prefixWord, tailWord_3199536, baseEnd_3199536] using wordTrace_append hprefix tailTrace_3199536
  have hstable : (prefixWord ++ tailWord_3199536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199536).length < 2 ^ (prefixWord ++ tailWord_3199536).sum := by decide
  have hdescent : baseEnd_3199536 < baseStart_3199536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199566 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_3199566 : Nat := 118140960795 + 3199566 * 2 ^ 59
def prefixEnd_3199566 : Nat := 4983230072969 + 3 ^ 40 * 3199566 * 2
def baseEnd_3199566 : Nat := 365092276396340870446771

theorem tailTrace_3199566 : CollatzResearch.WordTrace tailWord_3199566 prefixEnd_3199566 365092276396340870446771 := by
  unfold tailWord_3199566
  simp only [CollatzResearch.WordTrace]
  refine ⟨14587219890815787401676319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77798506084350866142273701 14587219890815787401676319)
  ·
    refine ⟨21880829836223681102514479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14587219890815787401676319 21880829836223681102514479)
    ·
      refine ⟨32821244754335521653771719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21880829836223681102514479 32821244754335521653771719)
      ·
        refine ⟨49231867131503282480657579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32821244754335521653771719 49231867131503282480657579)
        ·
          refine ⟨73847800697254923720986369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49231867131503282480657579 73847800697254923720986369)
          ·
            refine ⟨55385850522941192790739777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73847800697254923720986369 55385850522941192790739777)
            ·
              refine ⟨41539387892205894593054833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55385850522941192790739777 41539387892205894593054833)
              ·
                refine ⟨31154540919154420944791125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41539387892205894593054833 31154540919154420944791125)
                ·
                  refine ⟨365092276396340870446771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31154540919154420944791125 365092276396340870446771)
                  ·
                    rfl

theorem cell22_3199566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_3199566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199566 prefixEnd_3199566 := by exact prefixLift 3199566
  have htrace : WordTrace (prefixWord ++ tailWord_3199566) baseStart_3199566 baseEnd_3199566 := by
    simpa [prefixWord, tailWord_3199566, baseEnd_3199566] using wordTrace_append hprefix tailTrace_3199566
  have hstable : (prefixWord ++ tailWord_3199566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199566).length < 2 ^ (prefixWord ++ tailWord_3199566).sum := by decide
  have hdescent : baseEnd_3199566 < baseStart_3199566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199583 : List Nat := [1, 1, 2, 3, 1, 1, 1, 8, 4]
def baseStart_3199583 : Nat := 118140960795 + 3199583 * 2 ^ 59
def prefixEnd_3199583 : Nat := 4983230072969 + 3 ^ 40 * 3199583 * 2
def baseEnd_3199583 : Nat := 365094216212146744555087

theorem tailTrace_3199583 : CollatzResearch.WordTrace tailWord_3199583 prefixEnd_3199583 365094216212146744555087 := by
  unfold tailWord_3199583
  simp only [CollatzResearch.WordTrace]
  refine ⟨116698379167464711116779403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77798919444976474077852935 116698379167464711116779403)
  ·
    refine ⟨175047568751197066675169105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116698379167464711116779403 175047568751197066675169105)
    ·
      refine ⟨131285676563397800006376829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175047568751197066675169105 131285676563397800006376829)
      ·
        refine ⟨49232128711274175002391311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131285676563397800006376829 49232128711274175002391311)
        ·
          refine ⟨73848193066911262503586967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49232128711274175002391311 73848193066911262503586967)
          ·
            refine ⟨110772289600366893755380451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73848193066911262503586967 110772289600366893755380451)
            ·
              refine ⟨166158434400550340633070677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110772289600366893755380451 166158434400550340633070677)
              ·
                refine ⟨1947169153131449304293797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 166158434400550340633070677 1947169153131449304293797)
                ·
                  refine ⟨365094216212146744555087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947169153131449304293797 365094216212146744555087)
                  ·
                    rfl

theorem cell22_3199583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 4].length) (baseStart_3199583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199583 prefixEnd_3199583 := by exact prefixLift 3199583
  have htrace : WordTrace (prefixWord ++ tailWord_3199583) baseStart_3199583 baseEnd_3199583 := by
    simpa [prefixWord, tailWord_3199583, baseEnd_3199583] using wordTrace_append hprefix tailTrace_3199583
  have hstable : (prefixWord ++ tailWord_3199583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199583).length < 2 ^ (prefixWord ++ tailWord_3199583).sum := by decide
  have hdescent : baseEnd_3199583 < baseStart_3199583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199596 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_3199596 : Nat := 118140960795 + 3199596 * 2 ^ 59
def prefixEnd_3199596 : Nat := 4983230072969 + 3 ^ 40 * 3199596 * 2
def baseEnd_3199596 : Nat := 1095287098802112533090221

theorem tailTrace_3199596 : CollatzResearch.WordTrace tailWord_3199596 prefixEnd_3199596 1095287098802112533090221 := by
  unfold tailWord_3199596
  simp only [CollatzResearch.WordTrace]
  refine ⟨58349426658208807168501321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77799235544278409558001761 58349426658208807168501321)
  ·
    refine ⟨43762069993656605376375991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58349426658208807168501321 43762069993656605376375991)
    ·
      refine ⟨65643104990484908064563987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43762069993656605376375991 65643104990484908064563987)
      ·
        refine ⟨98464657485727362096845981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65643104990484908064563987 98464657485727362096845981)
        ·
          refine ⟨36924246557147760786317243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98464657485727362096845981 36924246557147760786317243)
          ·
            refine ⟨55386369835721641179475865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36924246557147760786317243 55386369835721641179475865)
            ·
              refine ⟨41539777376791230884606899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55386369835721641179475865 41539777376791230884606899)
              ·
                refine ⟨62309666065186846326910349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41539777376791230884606899 62309666065186846326910349)
                ·
                  refine ⟨23366124774445067372591381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62309666065186846326910349 23366124774445067372591381)
                  ·
                    refine ⟨1095287098802112533090221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23366124774445067372591381 1095287098802112533090221)
                    ·
                      rfl

theorem cell22_3199596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_3199596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199596 prefixEnd_3199596 := by exact prefixLift 3199596
  have htrace : WordTrace (prefixWord ++ tailWord_3199596) baseStart_3199596 baseEnd_3199596 := by
    simpa [prefixWord, tailWord_3199596, baseEnd_3199596] using wordTrace_append hprefix tailTrace_3199596
  have hstable : (prefixWord ++ tailWord_3199596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199596).length < 2 ^ (prefixWord ++ tailWord_3199596).sum := by decide
  have hdescent : baseEnd_3199596 < baseStart_3199596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199602 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_3199602 : Nat := 118140960795 + 3199602 * 2 ^ 59
def prefixEnd_3199602 : Nat := 4983230072969 + 3 ^ 40 * 3199602 * 2
def baseEnd_3199602 : Nat := 1095289152724730517440203

theorem tailTrace_3199602 : CollatzResearch.WordTrace tailWord_3199602 prefixEnd_3199602 1095289152724730517440203 := by
  unfold tailWord_3199602
  simp only [CollatzResearch.WordTrace]
  refine ⟨29174768038598969340430265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77799381436263918241147373 29174768038598969340430265)
  ·
    refine ⟨21881076028949227005322699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29174768038598969340430265 21881076028949227005322699)
    ·
      refine ⟨32821614043423840507984049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21881076028949227005322699 32821614043423840507984049)
      ·
        refine ⟨24616210532567880380988037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32821614043423840507984049 24616210532567880380988037)
        ·
          refine ⟨4615539474856477571435257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24616210532567880380988037 4615539474856477571435257)
          ·
            refine ⟨3461654606142358178576443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4615539474856477571435257 3461654606142358178576443)
            ·
              refine ⟨5192481909213537267864665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461654606142358178576443 5192481909213537267864665)
              ·
                refine ⟨3894361431910152950898499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5192481909213537267864665 3894361431910152950898499)
                ·
                  refine ⟨5841542147865229426347749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3894361431910152950898499 5841542147865229426347749)
                  ·
                    refine ⟨1095289152724730517440203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5841542147865229426347749 1095289152724730517440203)
                    ·
                      rfl

theorem cell22_3199602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_3199602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199602 prefixEnd_3199602 := by exact prefixLift 3199602
  have htrace : WordTrace (prefixWord ++ tailWord_3199602) baseStart_3199602 baseEnd_3199602 := by
    simpa [prefixWord, tailWord_3199602, baseEnd_3199602] using wordTrace_append hprefix tailTrace_3199602
  have hstable : (prefixWord ++ tailWord_3199602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199602).length < 2 ^ (prefixWord ++ tailWord_3199602).sum := by decide
  have hdescent : baseEnd_3199602 < baseStart_3199602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199634 : List Nat := [3, 2, 3, 1, 2, 3, 2, 2, 4]
def baseStart_3199634 : Nat := 118140960795 + 3199634 * 2 ^ 59
def prefixEnd_3199634 : Nat := 4983230072969 + 3 ^ 40 * 3199634 * 2
def baseEnd_3199634 : Nat := 365100035659564366880035

theorem tailTrace_3199634 : CollatzResearch.WordTrace tailWord_3199634 prefixEnd_3199634 365100035659564366880035 := by
  unfold tailWord_3199634
  simp only [CollatzResearch.WordTrace]
  refine ⟨29175059822569986706721489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77800159526853297884590637 29175059822569986706721489)
  ·
    refine ⟨21881294866927490030041117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29175059822569986706721489 21881294866927490030041117)
    ·
      refine ⟨8205485575097808761265419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21881294866927490030041117 8205485575097808761265419)
      ·
        refine ⟨12308228362646713141898129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8205485575097808761265419 12308228362646713141898129)
        ·
          refine ⟨9231171271985034856423597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12308228362646713141898129 9231171271985034856423597)
          ·
            refine ⟨3461689226994388071158849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9231171271985034856423597 3461689226994388071158849)
            ·
              refine ⟨2596266920245791053369137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3461689226994388071158849 2596266920245791053369137)
              ·
                refine ⟨1947200190184343290026853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596266920245791053369137 1947200190184343290026853)
                ·
                  refine ⟨365100035659564366880035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947200190184343290026853 365100035659564366880035)
                  ·
                    rfl

theorem cell22_3199634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_3199634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199634 prefixEnd_3199634 := by exact prefixLift 3199634
  have htrace : WordTrace (prefixWord ++ tailWord_3199634) baseStart_3199634 baseEnd_3199634 := by
    simpa [prefixWord, tailWord_3199634, baseEnd_3199634] using wordTrace_append hprefix tailTrace_3199634
  have hstable : (prefixWord ++ tailWord_3199634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199634).length < 2 ^ (prefixWord ++ tailWord_3199634).sum := by decide
  have hdescent : baseEnd_3199634 < baseStart_3199634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199641 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_3199641 : Nat := 118140960795 + 3199641 * 2 ^ 59
def prefixEnd_3199641 : Nat := 4983230072969 + 3 ^ 40 * 3199641 * 2
def baseEnd_3199641 : Nat := 1095302503221747415715083

theorem tailTrace_3199641 : CollatzResearch.WordTrace tailWord_3199641 prefixEnd_3199641 1095302503221747415715083 := by
  unfold tailWord_3199641
  simp only [CollatzResearch.WordTrace]
  refine ⟨116700494601254587022390777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77800329734169724681593851 116700494601254587022390777)
  ·
    refine ⟨87525370950940940266793083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116700494601254587022390777 87525370950940940266793083)
    ·
      refine ⟨131288056426411410400189625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87525370950940940266793083 131288056426411410400189625)
      ·
        refine ⟨98466042319808557800142219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131288056426411410400189625 98466042319808557800142219)
        ·
          refine ⟨147699063479712836700213329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98466042319808557800142219 147699063479712836700213329)
          ·
            refine ⟨110774297609784627525159997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147699063479712836700213329 110774297609784627525159997)
            ·
              refine ⟨41540361603669235321934999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110774297609784627525159997 41540361603669235321934999)
              ·
                refine ⟨62310542405503852982902499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41540361603669235321934999 62310542405503852982902499)
                ·
                  refine ⟨93465813608255779474353749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62310542405503852982902499 93465813608255779474353749)
                  ·
                    refine ⟨1095302503221747415715083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93465813608255779474353749 1095302503221747415715083)
                    ·
                      rfl

theorem cell22_3199641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_3199641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199641 prefixEnd_3199641 := by exact prefixLift 3199641
  have htrace : WordTrace (prefixWord ++ tailWord_3199641) baseStart_3199641 baseEnd_3199641 := by
    simpa [prefixWord, tailWord_3199641, baseEnd_3199641] using wordTrace_append hprefix tailTrace_3199641
  have hstable : (prefixWord ++ tailWord_3199641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199641).length < 2 ^ (prefixWord ++ tailWord_3199641).sum := by decide
  have hdescent : baseEnd_3199641 < baseStart_3199641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199662 : List Nat := [4, 1, 4, 1, 1, 2, 3, 6]
def baseStart_3199662 : Nat := 118140960795 + 3199662 * 2 ^ 59
def prefixEnd_3199662 : Nat := 4983230072969 + 3 ^ 40 * 3199662 * 2
def baseEnd_3199662 : Nat := 121701076883434484548891

theorem tailTrace_3199662 : CollatzResearch.WordTrace tailWord_3199662 prefixEnd_3199662 121701076883434484548891 := by
  unfold tailWord_3199662
  simp only [CollatzResearch.WordTrace]
  refine ⟨14587657566772313451113155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77800840356119005072603493 14587657566772313451113155)
  ·
    refine ⟨21881486350158470176669733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14587657566772313451113155 21881486350158470176669733)
    ·
      refine ⟨4102778690654713158125575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21881486350158470176669733 4102778690654713158125575)
      ·
        refine ⟨6154168035982069737188363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4102778690654713158125575 6154168035982069737188363)
        ·
          refine ⟨9231252053973104605782545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6154168035982069737188363 9231252053973104605782545)
          ·
            refine ⟨6923439040479828454336909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9231252053973104605782545 6923439040479828454336909)
            ·
              refine ⟨2596289640179935670376341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6923439040479828454336909 2596289640179935670376341)
              ·
                refine ⟨121701076883434484548891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2596289640179935670376341 121701076883434484548891)
                ·
                  rfl

theorem cell22_3199662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_3199662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199662 prefixEnd_3199662 := by exact prefixLift 3199662
  have htrace : WordTrace (prefixWord ++ tailWord_3199662) baseStart_3199662 baseEnd_3199662 := by
    simpa [prefixWord, tailWord_3199662, baseEnd_3199662] using wordTrace_append hprefix tailTrace_3199662
  have hstable : (prefixWord ++ tailWord_3199662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199662).length < 2 ^ (prefixWord ++ tailWord_3199662).sum := by decide
  have hdescent : baseEnd_3199662 < baseStart_3199662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199677 : List Nat := [1, 4, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_3199677 : Nat := 118140960795 + 3199677 * 2 ^ 59
def prefixEnd_3199677 : Nat := 4983230072969 + 3 ^ 40 * 3199677 * 2
def baseEnd_3199677 : Nat := 1095314826757455321814973

theorem tailTrace_3199677 : CollatzResearch.WordTrace tailWord_3199677 prefixEnd_3199677 1095314826757455321814973 := by
  unfold tailWord_3199677
  simp only [CollatzResearch.WordTrace]
  refine ⟨116701807629124165170701285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77801205086082776780467523 116701807629124165170701285)
  ·
    refine ⟨21881588930460780969506491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116701807629124165170701285 21881588930460780969506491)
    ·
      refine ⟨32822383395691171454259737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21881588930460780969506491 32822383395691171454259737)
      ·
        refine ⟨24616787546768378590694803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32822383395691171454259737 24616787546768378590694803)
        ·
          refine ⟨36925181320152567886042205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24616787546768378590694803 36925181320152567886042205)
          ·
            refine ⟨13846942995057212957265827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36925181320152567886042205 13846942995057212957265827)
            ·
              refine ⟨20770414492585819435898741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13846942995057212957265827 20770414492585819435898741)
              ·
                refine ⟨1947226358679920572115507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20770414492585819435898741 1947226358679920572115507)
                ·
                  refine ⟨2920839538019880858173261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947226358679920572115507 2920839538019880858173261)
                  ·
                    refine ⟨1095314826757455321814973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2920839538019880858173261 1095314826757455321814973)
                    ·
                      rfl

theorem cell22_3199677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_3199677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199677 prefixEnd_3199677 := by exact prefixLift 3199677
  have htrace : WordTrace (prefixWord ++ tailWord_3199677) baseStart_3199677 baseEnd_3199677 := by
    simpa [prefixWord, tailWord_3199677, baseEnd_3199677] using wordTrace_append hprefix tailTrace_3199677
  have hstable : (prefixWord ++ tailWord_3199677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199677).length < 2 ^ (prefixWord ++ tailWord_3199677).sum := by decide
  have hdescent : baseEnd_3199677 < baseStart_3199677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199688 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_3199688 : Nat := 118140960795 + 3199688 * 2 ^ 59
def prefixEnd_3199688 : Nat := 4983230072969 + 3 ^ 40 * 3199688 * 2
def baseEnd_3199688 : Nat := 1095318592282254959789939

theorem tailTrace_3199688 : CollatzResearch.WordTrace tailWord_3199688 prefixEnd_3199688 1095318592282254959789939 := by
  unfold tailWord_3199688
  simp only [CollatzResearch.WordTrace]
  refine ⟨58351104416042157024675859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77801472554722876032901145 58351104416042157024675859)
  ·
    refine ⟨87526656624063235537013789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58351104416042157024675859 87526656624063235537013789)
    ·
      refine ⟨32822496234023713326380171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87526656624063235537013789 32822496234023713326380171)
      ·
        refine ⟨49233744351035569989570257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32822496234023713326380171 49233744351035569989570257)
        ·
          refine ⟨36925308263276677492177693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49233744351035569989570257 36925308263276677492177693)
          ·
            refine ⟨13846990598728754059566635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36925308263276677492177693 13846990598728754059566635)
            ·
              refine ⟨20770485898093131089349953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13846990598728754059566635 20770485898093131089349953)
              ·
                refine ⟨15577864423569848317012465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20770485898093131089349953 15577864423569848317012465)
                ·
                  refine ⟨11683398317677386237759349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15577864423569848317012465 11683398317677386237759349)
                  ·
                    refine ⟨1095318592282254959789939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11683398317677386237759349 1095318592282254959789939)
                    ·
                      rfl

theorem cell22_3199688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_3199688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199688 prefixEnd_3199688 := by exact prefixLift 3199688
  have htrace : WordTrace (prefixWord ++ tailWord_3199688) baseStart_3199688 baseEnd_3199688 := by
    simpa [prefixWord, tailWord_3199688, baseEnd_3199688] using wordTrace_append hprefix tailTrace_3199688
  have hstable : (prefixWord ++ tailWord_3199688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199688).length < 2 ^ (prefixWord ++ tailWord_3199688).sum := by decide
  have hdescent : baseEnd_3199688 < baseStart_3199688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199690 : List Nat := [3, 1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_3199690 : Nat := 118140960795 + 3199690 * 2 ^ 59
def prefixEnd_3199690 : Nat := 4983230072969 + 3 ^ 40 * 3199690 * 2
def baseEnd_3199690 : Nat := 365106425641042540413311

theorem tailTrace_3199690 : CollatzResearch.WordTrace tailWord_3199690 prefixEnd_3199690 365106425641042540413311 := by
  unfold tailWord_3199690
  simp only [CollatzResearch.WordTrace]
  refine ⟨29175570444519267097731131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77801521185384712260616349 29175570444519267097731131)
  ·
    refine ⟨43763355666778900646596697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29175570444519267097731131 43763355666778900646596697)
    ·
      refine ⟨32822516750084175484947523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43763355666778900646596697 32822516750084175484947523)
      ·
        refine ⟨49233775125126263227421285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32822516750084175484947523 49233775125126263227421285)
        ·
          refine ⟨9231332835961174355141491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49233775125126263227421285 9231332835961174355141491)
          ·
            refine ⟨13846999253941761532712237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9231332835961174355141491 13846999253941761532712237)
            ·
              refine ⟨5192624720228160574767089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13846999253941761532712237 5192624720228160574767089)
              ·
                refine ⟨3894468540171120431075317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5192624720228160574767089 3894468540171120431075317)
                ·
                  refine ⟨365106425641042540413311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3894468540171120431075317 365106425641042540413311)
                  ·
                    rfl

theorem cell22_3199690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_3199690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199690 prefixEnd_3199690 := by exact prefixLift 3199690
  have htrace : WordTrace (prefixWord ++ tailWord_3199690) baseStart_3199690 baseEnd_3199690 := by
    simpa [prefixWord, tailWord_3199690, baseEnd_3199690] using wordTrace_append hprefix tailTrace_3199690
  have hstable : (prefixWord ++ tailWord_3199690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199690).length < 2 ^ (prefixWord ++ tailWord_3199690).sum := by decide
  have hdescent : baseEnd_3199690 < baseStart_3199690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199763 : List Nat := [1, 1, 1, 2, 1, 3, 6, 7]
def baseStart_3199763 : Nat := 118140960795 + 3199763 * 2 ^ 59
def prefixEnd_3199763 : Nat := 4983230072969 + 3 ^ 40 * 3199763 * 2
def baseEnd_3199763 : Nat := 121704918479442196018301

theorem tailTrace_3199763 : CollatzResearch.WordTrace tailWord_3199763 prefixEnd_3199763 121704918479442196018301 := by
  unfold tailWord_3199763
  simp only [CollatzResearch.WordTrace]
  refine ⟨116704944306812601858331943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77803296204541734572221295 116704944306812601858331943)
  ·
    refine ⟨175057416460218902787497915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116704944306812601858331943 175057416460218902787497915)
    ·
      refine ⟨262586124690328354181246873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175057416460218902787497915 262586124690328354181246873)
      ·
        refine ⟨196939593517746265635935155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262586124690328354181246873 196939593517746265635935155)
        ·
          refine ⟨295409390276619398453902733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196939593517746265635935155 295409390276619398453902733)
          ·
            refine ⟨110778521353732274420213525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295409390276619398453902733 110778521353732274420213525)
            ·
              refine ⟨5192743188456200363447509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110778521353732274420213525 5192743188456200363447509)
              ·
                refine ⟨121704918479442196018301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5192743188456200363447509 121704918479442196018301)
                ·
                  rfl

theorem cell22_3199763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 7].length) (baseStart_3199763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199763 prefixEnd_3199763 := by exact prefixLift 3199763
  have htrace : WordTrace (prefixWord ++ tailWord_3199763) baseStart_3199763 baseEnd_3199763 := by
    simpa [prefixWord, tailWord_3199763, baseEnd_3199763] using wordTrace_append hprefix tailTrace_3199763
  have hstable : (prefixWord ++ tailWord_3199763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199763).length < 2 ^ (prefixWord ++ tailWord_3199763).sum := by decide
  have hdescent : baseEnd_3199763 < baseStart_3199763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199808 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 7]
def baseStart_3199808 : Nat := 118140960795 + 3199808 * 2 ^ 59
def prefixEnd_3199808 : Nat := 4983230072969 + 3 ^ 40 * 3199808 * 2
def baseEnd_3199808 : Nat := 365119890244871548929857

theorem tailTrace_3199808 : CollatzResearch.WordTrace tailWord_3199808 prefixEnd_3199808 365119890244871548929857 := by
  unfold tailWord_3199808
  simp only [CollatzResearch.WordTrace]
  refine ⟨58353292795824787271860039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77804390394433049695813385 58353292795824787271860039)
  ·
    refine ⟨87529939193737180907790059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58353292795824787271860039 87529939193737180907790059)
    ·
      refine ⟨131294908790605771361685089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87529939193737180907790059 131294908790605771361685089)
      ·
        refine ⟨98471181592954328521263817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131294908790605771361685089 98471181592954328521263817)
        ·
          refine ⟨73853386194715746390947863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98471181592954328521263817 73853386194715746390947863)
          ·
            refine ⟨110780079292073619586421795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73853386194715746390947863 110780079292073619586421795)
            ·
              refine ⟨166170118938110429379632693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110780079292073619586421795 166170118938110429379632693)
              ·
                refine ⟨15578448650447852754340565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166170118938110429379632693 15578448650447852754340565)
                ·
                  refine ⟨365119890244871548929857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15578448650447852754340565 365119890244871548929857)
                  ·
                    rfl

theorem cell22_3199808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_3199808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199808 prefixEnd_3199808 := by exact prefixLift 3199808
  have htrace : WordTrace (prefixWord ++ tailWord_3199808) baseStart_3199808 baseEnd_3199808 := by
    simpa [prefixWord, tailWord_3199808, baseEnd_3199808] using wordTrace_append hprefix tailTrace_3199808
  have hstable : (prefixWord ++ tailWord_3199808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199808).length < 2 ^ (prefixWord ++ tailWord_3199808).sum := by decide
  have hdescent : baseEnd_3199808 < baseStart_3199808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199921 : List Nat := [1, 2, 2, 4, 3, 1, 3, 2, 4]
def baseStart_3199921 : Nat := 118140960795 + 3199921 * 2 ^ 59
def prefixEnd_3199921 : Nat := 4983230072969 + 3 ^ 40 * 3199921 * 2
def baseEnd_3199921 : Nat := 365132784314640006238075

theorem tailTrace_3199921 : CollatzResearch.WordTrace tailWord_3199921 prefixEnd_3199921 365132784314640006238075 := by
  unfold tailWord_3199921
  simp only [CollatzResearch.WordTrace]
  refine ⟨116710707040240194842583617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77807138026826796561722411 116710707040240194842583617)
  ·
    refine ⟨87533030280180146131937713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116710707040240194842583617 87533030280180146131937713)
    ·
      refine ⟨65649772710135109598953285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87533030280180146131937713 65649772710135109598953285)
      ·
        refine ⟨12309332383150333049803741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65649772710135109598953285 12309332383150333049803741)
        ·
          refine ⟨4615999643681374893676403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12309332383150333049803741 4615999643681374893676403)
          ·
            refine ⟨6923999465522062340514605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4615999643681374893676403 6923999465522062340514605)
            ·
              refine ⟨2596499799570773377692977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6923999465522062340514605 2596499799570773377692977)
              ·
                refine ⟨1947374849678080033269733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596499799570773377692977 1947374849678080033269733)
                ·
                  refine ⟨365132784314640006238075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947374849678080033269733 365132784314640006238075)
                  ·
                    rfl

theorem cell22_3199921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 2, 4].length) (baseStart_3199921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199921 prefixEnd_3199921 := by exact prefixLift 3199921
  have htrace : WordTrace (prefixWord ++ tailWord_3199921) baseStart_3199921 baseEnd_3199921 := by
    simpa [prefixWord, tailWord_3199921, baseEnd_3199921] using wordTrace_append hprefix tailTrace_3199921
  have hstable : (prefixWord ++ tailWord_3199921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199921).length < 2 ^ (prefixWord ++ tailWord_3199921).sum := by decide
  have hdescent : baseEnd_3199921 < baseStart_3199921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3199936 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 2, 3]
def baseStart_3199936 : Nat := 118140960795 + 3199936 * 2 ^ 59
def prefixEnd_3199936 : Nat := 4983230072969 + 3 ^ 40 * 3199936 * 2
def baseEnd_3199936 : Nat := 1095403487750464979589179

theorem tailTrace_3199936 : CollatzResearch.WordTrace tailWord_3199936 prefixEnd_3199936 1095403487750464979589179 := by
  unfold tailWord_3199936
  simp only [CollatzResearch.WordTrace]
  refine ⟨58355627067592926202189831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77807502756790568269586441 58355627067592926202189831)
  ·
    refine ⟨87533440601389389303284747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58355627067592926202189831 87533440601389389303284747)
    ·
      refine ⟨131300160902084083954927121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87533440601389389303284747 131300160902084083954927121)
      ·
        refine ⟨98475120676563062966195341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131300160902084083954927121 98475120676563062966195341)
        ·
          refine ⟨36928170253711148612323253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98475120676563062966195341 36928170253711148612323253)
          ·
            refine ⟨3462015961285420182405305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36928170253711148612323253 3462015961285420182405305)
            ·
              refine ⟨2596511970964065136803979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462015961285420182405305 2596511970964065136803979)
              ·
                refine ⟨3894767956446097705205969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2596511970964065136803979 3894767956446097705205969)
                ·
                  refine ⟨2921075967334573278904477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3894767956446097705205969 2921075967334573278904477)
                  ·
                    refine ⟨1095403487750464979589179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2921075967334573278904477 1095403487750464979589179)
                    ·
                      rfl

theorem cell22_3199936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 2, 3].length) (baseStart_3199936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3199936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3199936 prefixEnd_3199936 := by exact prefixLift 3199936
  have htrace : WordTrace (prefixWord ++ tailWord_3199936) baseStart_3199936 baseEnd_3199936 := by
    simpa [prefixWord, tailWord_3199936, baseEnd_3199936] using wordTrace_append hprefix tailTrace_3199936
  have hstable : (prefixWord ++ tailWord_3199936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3199936).length < 2 ^ (prefixWord ++ tailWord_3199936).sum := by decide
  have hdescent : baseEnd_3199936 < baseStart_3199936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3199936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200007 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3200007 : Nat := 118140960795 + 3200007 * 2 ^ 59
def prefixEnd_3200007 : Nat := 4983230072969 + 3 ^ 40 * 3200007 * 2
def baseEnd_3200007 : Nat := 1095427792501444461063961

theorem tailTrace_3200007 : CollatzResearch.WordTrace tailWord_3200007 prefixEnd_3200007 1095427792501444461063961 := by
  unfold tailWord_3200007
  simp only [CollatzResearch.WordTrace]
  refine ⟨116713843717928631530214275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77809229145285754353476183 116713843717928631530214275)
  ·
    refine ⟨175070765576892947295321413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116713843717928631530214275 175070765576892947295321413)
    ·
      refine ⟨32825768545667427617872765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175070765576892947295321413 32825768545667427617872765)
      ·
        refine ⟨12309663204625285356702287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32825768545667427617872765 12309663204625285356702287)
        ·
          refine ⟨18464494806937928035053431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12309663204625285356702287 18464494806937928035053431)
          ·
            refine ⟨27696742210406892052580147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18464494806937928035053431 27696742210406892052580147)
            ·
              refine ⟨41545113315610338078870221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27696742210406892052580147 41545113315610338078870221)
              ·
                refine ⟨15579417493353876779576333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41545113315610338078870221 15579417493353876779576333)
                ·
                  refine ⟨5842281560007703792341125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15579417493353876779576333 5842281560007703792341125)
                  ·
                    refine ⟨1095427792501444461063961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5842281560007703792341125 1095427792501444461063961)
                    ·
                      rfl

theorem cell22_3200007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3200007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200007 prefixEnd_3200007 := by exact prefixLift 3200007
  have htrace : WordTrace (prefixWord ++ tailWord_3200007) baseStart_3200007 baseEnd_3200007 := by
    simpa [prefixWord, tailWord_3200007, baseEnd_3200007] using wordTrace_append hprefix tailTrace_3200007
  have hstable : (prefixWord ++ tailWord_3200007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200007).length < 2 ^ (prefixWord ++ tailWord_3200007).sum := by decide
  have hdescent : baseEnd_3200007 < baseStart_3200007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200024 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 1, 4]
def baseStart_3200024 : Nat := 118140960795 + 3200024 * 2 ^ 59
def prefixEnd_3200024 : Nat := 4983230072969 + 3 ^ 40 * 3200024 * 2
def baseEnd_3200024 : Nat := 1095433611948862083388909

theorem tailTrace_3200024 : CollatzResearch.WordTrace tailWord_3200024 prefixEnd_3200024 1095433611948862083388909 := by
  unfold tailWord_3200024
  simp only [CollatzResearch.WordTrace]
  refine ⟨58357231879433521716791563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77809642505911362289055417 58357231879433521716791563)
  ·
    refine ⟨87535847819150282575187345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58357231879433521716791563 87535847819150282575187345)
    ·
      refine ⟨65651885864362711931390509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87535847819150282575187345 65651885864362711931390509)
      ·
        refine ⟨24619457199136016974271441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65651885864362711931390509 24619457199136016974271441)
        ·
          refine ⟨18464592899352012730703581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24619457199136016974271441 18464592899352012730703581)
          ·
            refine ⟨6924222337257004774013843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18464592899352012730703581 6924222337257004774013843)
            ·
              refine ⟨10386333505885507161020765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6924222337257004774013843 10386333505885507161020765)
              ·
                refine ⟨3894875064707065185382787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10386333505885507161020765 3894875064707065185382787)
                ·
                  refine ⟨5842312597060597778074181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3894875064707065185382787 5842312597060597778074181)
                  ·
                    refine ⟨1095433611948862083388909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5842312597060597778074181 1095433611948862083388909)
                    ·
                      rfl

theorem cell22_3200024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_3200024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200024 prefixEnd_3200024 := by exact prefixLift 3200024
  have htrace : WordTrace (prefixWord ++ tailWord_3200024) baseStart_3200024 baseEnd_3200024 := by
    simpa [prefixWord, tailWord_3200024, baseEnd_3200024] using wordTrace_append hprefix tailTrace_3200024
  have hstable : (prefixWord ++ tailWord_3200024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200024).length < 2 ^ (prefixWord ++ tailWord_3200024).sum := by decide
  have hdescent : baseEnd_3200024 < baseStart_3200024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200039 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 6]
def baseStart_3200039 : Nat := 118140960795 + 3200039 * 2 ^ 59
def prefixEnd_3200039 : Nat := 4983230072969 + 3 ^ 40 * 3200039 * 2
def baseEnd_3200039 : Nat := 365146248918469014754621

theorem tailTrace_3200039 : CollatzResearch.WordTrace tailWord_3200039 prefixEnd_3200039 365146248918469014754621 := by
  unfold tailWord_3200039
  simp only [CollatzResearch.WordTrace]
  refine ⟨116715010853812700995379171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77810007235875133996919447 116715010853812700995379171)
  ·
    refine ⟨175072516280719051493068757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116715010853812700995379171 175072516280719051493068757)
    ·
      refine ⟨4103262100329352769368799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 175072516280719051493068757 4103262100329352769368799)
      ·
        refine ⟨6154893150494029154053199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4103262100329352769368799 6154893150494029154053199)
        ·
          refine ⟨9232339725741043731079799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6154893150494029154053199 9232339725741043731079799)
          ·
            refine ⟨13848509588611565596619699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9232339725741043731079799 13848509588611565596619699)
            ·
              refine ⟨20772764382917348394929549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13848509588611565596619699 20772764382917348394929549)
              ·
                refine ⟨7789786643594005648098581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20772764382917348394929549 7789786643594005648098581)
                ·
                  refine ⟨365146248918469014754621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7789786643594005648098581 365146248918469014754621)
                  ·
                    rfl

theorem cell22_3200039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 6].length) (baseStart_3200039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200039 prefixEnd_3200039 := by exact prefixLift 3200039
  have htrace : WordTrace (prefixWord ++ tailWord_3200039) baseStart_3200039 baseEnd_3200039 := by
    simpa [prefixWord, tailWord_3200039, baseEnd_3200039] using wordTrace_append hprefix tailTrace_3200039
  have hstable : (prefixWord ++ tailWord_3200039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200039).length < 2 ^ (prefixWord ++ tailWord_3200039).sum := by decide
  have hdescent : baseEnd_3200039 < baseStart_3200039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200146 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_3200146 : Nat := 118140960795 + 3200146 * 2 ^ 59
def prefixEnd_3200146 : Nat := 4983230072969 + 3 ^ 40 * 3200146 * 2
def baseEnd_3200146 : Nat := 365158458347364810612845

theorem tailTrace_3200146 : CollatzResearch.WordTrace tailWord_3200146 prefixEnd_3200146 365158458347364810612845 := by
  unfold tailWord_3200146
  simp only [CollatzResearch.WordTrace]
  refine ⟨29179728366106264567381073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77812608976283372179682861 29179728366106264567381073)
  ·
    refine ⟨21884796274579698425535805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29179728366106264567381073 21884796274579698425535805)
    ·
      refine ⟨8206798602967386909575927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21884796274579698425535805 8206798602967386909575927)
      ·
        refine ⟨12310197904451080364363891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8206798602967386909575927 12310197904451080364363891)
        ·
          refine ⟨18465296856676620546545837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12310197904451080364363891 18465296856676620546545837)
          ·
            refine ⟨6924486321253732704954689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18465296856676620546545837 6924486321253732704954689)
            ·
              refine ⟨5193364740940299528716017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6924486321253732704954689 5193364740940299528716017)
              ·
                refine ⟨3895023555705224646537013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5193364740940299528716017 3895023555705224646537013)
                ·
                  refine ⟨365158458347364810612845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3895023555705224646537013 365158458347364810612845)
                  ·
                    rfl

theorem cell22_3200146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_3200146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200146 prefixEnd_3200146 := by exact prefixLift 3200146
  have htrace : WordTrace (prefixWord ++ tailWord_3200146) baseStart_3200146 baseEnd_3200146 := by
    simpa [prefixWord, tailWord_3200146, baseEnd_3200146] using wordTrace_append hprefix tailTrace_3200146
  have hstable : (prefixWord ++ tailWord_3200146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200146).length < 2 ^ (prefixWord ++ tailWord_3200146).sum := by decide
  have hdescent : baseEnd_3200146 < baseStart_3200146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200189 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_3200189 : Nat := 118140960795 + 3200189 * 2 ^ 59
def prefixEnd_3200189 : Nat := 4983230072969 + 3 ^ 40 * 3200189 * 2
def baseEnd_3200189 : Nat := 1095490094820856653013403

theorem tailTrace_3200189 : CollatzResearch.WordTrace tailWord_3200189 prefixEnd_3200189 1095490094820856653013403 := by
  unfold tailWord_3200189
  simp only [CollatzResearch.WordTrace]
  refine ⟨116720481803269276613339621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77813654535512851075559747 116720481803269276613339621)
  ·
    refine ⟨21885090338112989365001179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116720481803269276613339621 21885090338112989365001179)
    ·
      refine ⟨32827635507169484047501769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21885090338112989365001179 32827635507169484047501769)
      ·
        refine ⟨24620726630377113035626327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32827635507169484047501769 24620726630377113035626327)
        ·
          refine ⟨36931089945565669553439491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24620726630377113035626327 36931089945565669553439491)
          ·
            refine ⟨55396634918348504330159237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36931089945565669553439491 55396634918348504330159237)
            ·
              refine ⟨10386869047190344561904857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55396634918348504330159237 10386869047190344561904857)
              ·
                refine ⟨7790151785392758421428643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10386869047190344561904857 7790151785392758421428643)
                ·
                  refine ⟨11685227678089137632142965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7790151785392758421428643 11685227678089137632142965)
                  ·
                    refine ⟨1095490094820856653013403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11685227678089137632142965 1095490094820856653013403)
                    ·
                      rfl

theorem cell22_3200189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_3200189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200189 prefixEnd_3200189 := by exact prefixLift 3200189
  have htrace : WordTrace (prefixWord ++ tailWord_3200189) baseStart_3200189 baseEnd_3200189 := by
    simpa [prefixWord, tailWord_3200189, baseEnd_3200189] using wordTrace_append hprefix tailTrace_3200189
  have hstable : (prefixWord ++ tailWord_3200189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200189).length < 2 ^ (prefixWord ++ tailWord_3200189).sum := by decide
  have hdescent : baseEnd_3200189 < baseStart_3200189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200193 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3200193 : Nat := 118140960795 + 3200193 * 2 ^ 59
def prefixEnd_3200193 : Nat := 4983230072969 + 3 ^ 40 * 3200193 * 2
def baseEnd_3200193 : Nat := 1095491464102601975913391

theorem tailTrace_3200193 : CollatzResearch.WordTrace tailWord_3200193 prefixEnd_3200193 1095491464102601975913391 := by
  unfold tailWord_3200193
  simp only [CollatzResearch.WordTrace]
  refine ⟨116720627695254785296485233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77813751796836523530990155 116720627695254785296485233)
  ·
    refine ⟨87540470771441088972363925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116720627695254785296485233 87540470771441088972363925)
    ·
      refine ⟨4103459567411301045579559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87540470771441088972363925 4103459567411301045579559)
      ·
        refine ⟨6155189351116951568369339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4103459567411301045579559 6155189351116951568369339)
        ·
          refine ⟨9232784026675427352554009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6155189351116951568369339 9232784026675427352554009)
          ·
            refine ⟨6924588020006570514415507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9232784026675427352554009 6924588020006570514415507)
            ·
              refine ⟨10386882030009855771623261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6924588020006570514415507 10386882030009855771623261)
              ·
                refine ⟨3895080761253695914358723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10386882030009855771623261 3895080761253695914358723)
                ·
                  refine ⟨5842621141880543871538085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895080761253695914358723 5842621141880543871538085)
                  ·
                    refine ⟨1095491464102601975913391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5842621141880543871538085 1095491464102601975913391)
                    ·
                      rfl

theorem cell22_3200193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3200193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200193 prefixEnd_3200193 := by exact prefixLift 3200193
  have htrace : WordTrace (prefixWord ++ tailWord_3200193) baseStart_3200193 baseEnd_3200193 := by
    simpa [prefixWord, tailWord_3200193, baseEnd_3200193] using wordTrace_append hprefix tailTrace_3200193
  have hstable : (prefixWord ++ tailWord_3200193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200193).length < 2 ^ (prefixWord ++ tailWord_3200193).sum := by decide
  have hdescent : baseEnd_3200193 < baseStart_3200193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200236 : List Nat := [2, 2, 1, 1, 2, 6, 2, 6]
def baseStart_3200236 : Nat := 118140960795 + 3200236 * 2 ^ 59
def prefixEnd_3200236 : Nat := 4983230072969 + 3 ^ 40 * 3200236 * 2
def baseEnd_3200236 : Nat := 121722909320151577454251

theorem tailTrace_3200236 : CollatzResearch.WordTrace tailWord_3200236 prefixEnd_3200236 121722909320151577454251 := by
  unfold tailWord_3200236
  simp only [CollatzResearch.WordTrace]
  refine ⟨58361098017049501820150281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77814797356066002426867041 58361098017049501820150281)
  ·
    refine ⟨43770823512787126365112711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58361098017049501820150281 43770823512787126365112711)
    ·
      refine ⟨65656235269180689547669067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43770823512787126365112711 65656235269180689547669067)
      ·
        refine ⟨98484352903771034321503601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65656235269180689547669067 98484352903771034321503601)
        ·
          refine ⟨73863264677828275741127701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98484352903771034321503601 73863264677828275741127701)
          ·
            refine ⟨3462340531773200425365361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73863264677828275741127701 3462340531773200425365361)
            ·
              refine ⟨2596755398829900319024021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462340531773200425365361 2596755398829900319024021)
              ·
                refine ⟨121722909320151577454251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2596755398829900319024021 121722909320151577454251)
                ·
                  rfl

theorem cell22_3200236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 6].length) (baseStart_3200236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200236 prefixEnd_3200236 := by exact prefixLift 3200236
  have htrace : WordTrace (prefixWord ++ tailWord_3200236) baseStart_3200236 baseEnd_3200236 := by
    simpa [prefixWord, tailWord_3200236, baseEnd_3200236] using wordTrace_append hprefix tailTrace_3200236
  have hstable : (prefixWord ++ tailWord_3200236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200236).length < 2 ^ (prefixWord ++ tailWord_3200236).sum := by decide
  have hdescent : baseEnd_3200236 < baseStart_3200236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200268 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 3, 3]
def baseStart_3200268 : Nat := 118140960795 + 3200268 * 2 ^ 59
def prefixEnd_3200268 : Nat := 4983230072969 + 3 ^ 40 * 3200268 * 2
def baseEnd_3200268 : Nat := 1095517138135326780288161

theorem tailTrace_3200268 : CollatzResearch.WordTrace tailWord_3200268 prefixEnd_3200268 1095517138135326780288161 := by
  unfold tailWord_3200268
  simp only [CollatzResearch.WordTrace]
  refine ⟨58361681584991536552732729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77815575446655382070310305 58361681584991536552732729)
  ·
    refine ⟨43771261188743652414549547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58361681584991536552732729 43771261188743652414549547)
    ·
      refine ⟨65656891783115478621824321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43771261188743652414549547 65656891783115478621824321)
      ·
        refine ⟨49242668837336608966368241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65656891783115478621824321 49242668837336608966368241)
        ·
          refine ⟨36932001628002456724776181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49242668837336608966368241 36932001628002456724776181)
          ·
            refine ⟨3462375152625230317947767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36932001628002456724776181 3462375152625230317947767)
            ·
              refine ⟨5193562728937845476921651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462375152625230317947767 5193562728937845476921651)
              ·
                refine ⟨7790344093406768215382477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5193562728937845476921651 7790344093406768215382477)
                ·
                  refine ⟨2921379035027538080768429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7790344093406768215382477 2921379035027538080768429)
                  ·
                    refine ⟨1095517138135326780288161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2921379035027538080768429 1095517138135326780288161)
                    ·
                      rfl

theorem cell22_3200268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_3200268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200268 prefixEnd_3200268 := by exact prefixLift 3200268
  have htrace : WordTrace (prefixWord ++ tailWord_3200268) baseStart_3200268 baseEnd_3200268 := by
    simpa [prefixWord, tailWord_3200268, baseEnd_3200268] using wordTrace_append hprefix tailTrace_3200268
  have hstable : (prefixWord ++ tailWord_3200268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200268).length < 2 ^ (prefixWord ++ tailWord_3200268).sum := by decide
  have hdescent : baseEnd_3200268 < baseStart_3200268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200274 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_3200274 : Nat := 118140960795 + 3200274 * 2 ^ 59
def prefixEnd_3200274 : Nat := 4983230072969 + 3 ^ 40 * 3200274 * 2
def baseEnd_3200274 : Nat := 1095519192057944764638143

theorem tailTrace_3200274 : CollatzResearch.WordTrace tailWord_3200274 prefixEnd_3200274 1095519192057944764638143 := by
  unfold tailWord_3200274
  simp only [CollatzResearch.WordTrace]
  refine ⟨29180895501990334032545969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77815721338640890753455917 29180895501990334032545969)
  ·
    refine ⟨21885671626492750524409477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29180895501990334032545969 21885671626492750524409477)
    ·
      refine ⟨4103563429967390723326777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21885671626492750524409477 4103563429967390723326777)
      ·
        refine ⟨3077672572475543042495083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4103563429967390723326777 3077672572475543042495083)
        ·
          refine ⟨4616508858713314563742625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3077672572475543042495083 4616508858713314563742625)
          ·
            refine ⟨3462381644034985922806969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4616508858713314563742625 3462381644034985922806969)
            ·
              refine ⟨2596786233026239442105227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462381644034985922806969 2596786233026239442105227)
              ·
                refine ⟨3895179349539359163157841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2596786233026239442105227 3895179349539359163157841)
                ·
                  refine ⟨2921384512154519372368381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3895179349539359163157841 2921384512154519372368381)
                  ·
                    refine ⟨1095519192057944764638143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2921384512154519372368381 1095519192057944764638143)
                    ·
                      rfl

theorem cell22_3200274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_3200274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200274 prefixEnd_3200274 := by exact prefixLift 3200274
  have htrace : WordTrace (prefixWord ++ tailWord_3200274) baseStart_3200274 baseEnd_3200274 := by
    simpa [prefixWord, tailWord_3200274, baseEnd_3200274] using wordTrace_append hprefix tailTrace_3200274
  have hstable : (prefixWord ++ tailWord_3200274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200274).length < 2 ^ (prefixWord ++ tailWord_3200274).sum := by decide
  have hdescent : baseEnd_3200274 < baseStart_3200274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200279 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 1, 7]
def baseStart_3200279 : Nat := 118140960795 + 3200279 * 2 ^ 59
def prefixEnd_3200279 : Nat := 4983230072969 + 3 ^ 40 * 3200279 * 2
def baseEnd_3200279 : Nat := 1095520903660126418263127

theorem tailTrace_3200279 : CollatzResearch.WordTrace tailWord_3200279 prefixEnd_3200279 1095520903660126418263127 := by
  unfold tailWord_3200279
  simp only [CollatzResearch.WordTrace]
  refine ⟨116723764372943221984115891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77815842915295481322743927 116723764372943221984115891)
  ·
    refine ⟨175085646559414832976173837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116723764372943221984115891 175085646559414832976173837)
    ·
      refine ⟨65657117459780562366065189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175085646559414832976173837 65657117459780562366065189)
      ·
        refine ⟨12310709523708855443637223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65657117459780562366065189 12310709523708855443637223)
        ·
          refine ⟨18466064285563283165455835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12310709523708855443637223 18466064285563283165455835)
          ·
            refine ⟨27699096428344924748183753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18466064285563283165455835 27699096428344924748183753)
            ·
              refine ⟨20774322321258693561137815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27699096428344924748183753 20774322321258693561137815)
              ·
                refine ⟨31161483481888040341706723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20774322321258693561137815 31161483481888040341706723)
                ·
                  refine ⟨46742225222832060512560085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31161483481888040341706723 46742225222832060512560085)
                  ·
                    refine ⟨1095520903660126418263127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46742225222832060512560085 1095520903660126418263127)
                    ·
                      rfl

theorem cell22_3200279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_3200279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200279 prefixEnd_3200279 := by exact prefixLift 3200279
  have htrace : WordTrace (prefixWord ++ tailWord_3200279) baseStart_3200279 baseEnd_3200279 := by
    simpa [prefixWord, tailWord_3200279, baseEnd_3200279] using wordTrace_append hprefix tailTrace_3200279
  have hstable : (prefixWord ++ tailWord_3200279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200279).length < 2 ^ (prefixWord ++ tailWord_3200279).sum := by decide
  have hdescent : baseEnd_3200279 < baseStart_3200279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200339 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 1, 6]
def baseStart_3200339 : Nat := 118140960795 + 3200339 * 2 ^ 59
def prefixEnd_3200339 : Nat := 4983230072969 + 3 ^ 40 * 3200339 * 2
def baseEnd_3200339 : Nat := 1095541442886306261762943

theorem tailTrace_3200339 : CollatzResearch.WordTrace tailWord_3200339 prefixEnd_3200339 1095541442886306261762943 := by
  unfold tailWord_3200339
  simp only [CollatzResearch.WordTrace]
  refine ⟨116725952752725852231300071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77817301835150568154200047 116725952752725852231300071)
  ·
    refine ⟨175088929129088778346950107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116725952752725852231300071 175088929129088778346950107)
    ·
      refine ⟨262633393693633167520425161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175088929129088778346950107 262633393693633167520425161)
      ·
        refine ⟨196975045270224875640318871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262633393693633167520425161 196975045270224875640318871)
        ·
          refine ⟨295462567905337313460478307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196975045270224875640318871 295462567905337313460478307)
          ·
            refine ⟨443193851858005970190717461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295462567905337313460478307 443193851858005970190717461)
            ·
              refine ⟨20774711805844029852689881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 443193851858005970190717461 20774711805844029852689881)
              ·
                refine ⟨15581033854383022389517411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20774711805844029852689881 15581033854383022389517411)
                ·
                  refine ⟨23371550781574533584276117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15581033854383022389517411 23371550781574533584276117)
                  ·
                    refine ⟨1095541442886306261762943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23371550781574533584276117 1095541442886306261762943)
                    ·
                      rfl

theorem cell22_3200339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_3200339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200339 prefixEnd_3200339 := by exact prefixLift 3200339
  have htrace : WordTrace (prefixWord ++ tailWord_3200339) baseStart_3200339 baseEnd_3200339 := by
    simpa [prefixWord, tailWord_3200339, baseEnd_3200339] using wordTrace_append hprefix tailTrace_3200339
  have hstable : (prefixWord ++ tailWord_3200339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200339).length < 2 ^ (prefixWord ++ tailWord_3200339).sum := by decide
  have hdescent : baseEnd_3200339 < baseStart_3200339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200341 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3200341 : Nat := 118140960795 + 3200341 * 2 ^ 59
def prefixEnd_3200341 : Nat := 4983230072969 + 3 ^ 40 * 3200341 * 2
def baseEnd_3200341 : Nat := 1095542127527178923212937

theorem tailTrace_3200341 : CollatzResearch.WordTrace tailWord_3200341 prefixEnd_3200341 1095542127527178923212937 := by
  unfold tailWord_3200341
  simp only [CollatzResearch.WordTrace]
  refine ⟨116726025698718606572872877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77817350465812404381915251 116726025698718606572872877)
  ·
    refine ⟨43772259637019477464827329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116726025698718606572872877 43772259637019477464827329)
    ·
      refine ⟨32829194727764608098620497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43772259637019477464827329 32829194727764608098620497)
      ·
        refine ⟨24621896045823456073965373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32829194727764608098620497 24621896045823456073965373)
        ·
          refine ⟨9233211017183796027737015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24621896045823456073965373 9233211017183796027737015)
          ·
            refine ⟨13849816525775694041605523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9233211017183796027737015 13849816525775694041605523)
            ·
              refine ⟨20774724788663541062408285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13849816525775694041605523 20774724788663541062408285)
              ·
                refine ⟨7790521795748827898403107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20774724788663541062408285 7790521795748827898403107)
                ·
                  refine ⟨11685782693623241847604661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7790521795748827898403107 11685782693623241847604661)
                  ·
                    refine ⟨1095542127527178923212937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11685782693623241847604661 1095542127527178923212937)
                    ·
                      rfl

theorem cell22_3200341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3200341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200341 prefixEnd_3200341 := by exact prefixLift 3200341
  have htrace : WordTrace (prefixWord ++ tailWord_3200341) baseStart_3200341 baseEnd_3200341 := by
    simpa [prefixWord, tailWord_3200341, baseEnd_3200341] using wordTrace_append hprefix tailTrace_3200341
  have hstable : (prefixWord ++ tailWord_3200341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200341).length < 2 ^ (prefixWord ++ tailWord_3200341).sum := by decide
  have hdescent : baseEnd_3200341 < baseStart_3200341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200356 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 1, 6]
def baseStart_3200356 : Nat := 118140960795 + 3200356 * 2 ^ 59
def prefixEnd_3200356 : Nat := 4983230072969 + 3 ^ 40 * 3200356 * 2
def baseEnd_3200356 : Nat := 1095547262333723884087891

theorem tailTrace_3200356 : CollatzResearch.WordTrace tailWord_3200356 prefixEnd_3200356 1095547262333723884087891 := by
  unfold tailWord_3200356
  simp only [CollatzResearch.WordTrace]
  refine ⟨58363286396832132067334461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77817715195776176089779281 58363286396832132067334461)
  ·
    refine ⟨21886232398812049525250423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58363286396832132067334461 21886232398812049525250423)
    ·
      refine ⟨32829348598218074287875635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21886232398812049525250423 32829348598218074287875635)
      ·
        refine ⟨49244022897327111431813453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32829348598218074287875635 49244022897327111431813453)
        ·
          refine ⟨18466508586497666786930045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49244022897327111431813453 18466508586497666786930045)
          ·
            refine ⟨6924940719936625045098767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18466508586497666786930045 6924940719936625045098767)
            ·
              refine ⟨10387411079904937567648151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6924940719936625045098767 10387411079904937567648151)
              ·
                refine ⟨15581116619857406351472227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10387411079904937567648151 15581116619857406351472227)
                ·
                  refine ⟨23371674929786109527208341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15581116619857406351472227 23371674929786109527208341)
                  ·
                    refine ⟨1095547262333723884087891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23371674929786109527208341 1095547262333723884087891)
                    ·
                      rfl

theorem cell22_3200356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_3200356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200356 prefixEnd_3200356 := by exact prefixLift 3200356
  have htrace : WordTrace (prefixWord ++ tailWord_3200356) baseStart_3200356 baseEnd_3200356 := by
    simpa [prefixWord, tailWord_3200356, baseEnd_3200356] using wordTrace_append hprefix tailTrace_3200356
  have hstable : (prefixWord ++ tailWord_3200356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200356).length < 2 ^ (prefixWord ++ tailWord_3200356).sum := by decide
  have hdescent : baseEnd_3200356 < baseStart_3200356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200360 : List Nat := [2, 1, 4, 2, 3, 1, 2, 3, 4]
def baseStart_3200360 : Nat := 118140960795 + 3200360 * 2 ^ 59
def prefixEnd_3200360 : Nat := 4983230072969 + 3 ^ 40 * 3200360 * 2
def baseEnd_3200360 : Nat := 365182877205156402329293

theorem tailTrace_3200360 : CollatzResearch.WordTrace tailWord_3200360 prefixEnd_3200360 365182877205156402329293 := by
  unfold tailWord_3200360
  simp only [CollatzResearch.WordTrace]
  refine ⟨58363359342824886408907267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77817812457099848545209689 58363359342824886408907267)
  ·
    refine ⟨87545039014237329613360901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58363359342824886408907267 87545039014237329613360901)
    ·
      refine ⟨16414694815169499302505169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87545039014237329613360901 16414694815169499302505169)
      ·
        refine ⟨12311021111377124476878877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16414694815169499302505169 12311021111377124476878877)
        ·
          refine ⟨4616632916766421678829579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12311021111377124476878877 4616632916766421678829579)
          ·
            refine ⟨6924949375149632518244369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4616632916766421678829579 6924949375149632518244369)
            ·
              refine ⟨5193712031362224388683277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6924949375149632518244369 5193712031362224388683277)
              ·
                refine ⟨1947642011760834145756229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5193712031362224388683277 1947642011760834145756229)
                ·
                  refine ⟨365182877205156402329293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947642011760834145756229 365182877205156402329293)
                  ·
                    rfl

theorem cell22_3200360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 4].length) (baseStart_3200360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200360 prefixEnd_3200360 := by exact prefixLift 3200360
  have htrace : WordTrace (prefixWord ++ tailWord_3200360) baseStart_3200360 baseEnd_3200360 := by
    simpa [prefixWord, tailWord_3200360, baseEnd_3200360] using wordTrace_append hprefix tailTrace_3200360
  have hstable : (prefixWord ++ tailWord_3200360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200360).length < 2 ^ (prefixWord ++ tailWord_3200360).sum := by decide
  have hdescent : baseEnd_3200360 < baseStart_3200360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200362 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 1, 4]
def baseStart_3200362 : Nat := 118140960795 + 3200362 * 2 ^ 59
def prefixEnd_3200362 : Nat := 4983230072969 + 3 ^ 40 * 3200362 * 2
def baseEnd_3200362 : Nat := 1095549316256341868437873

theorem tailTrace_3200362 : CollatzResearch.WordTrace tailWord_3200362 prefixEnd_3200362 1095549316256341868437873 := by
  unfold tailWord_3200362
  simp only [CollatzResearch.WordTrace]
  refine ⟨29181697907910631789846835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77817861087761684772924893 29181697907910631789846835)
  ·
    refine ⟨43772546861865947684770253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29181697907910631789846835 43772546861865947684770253)
    ·
      refine ⟨16414705073199730381788845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43772546861865947684770253 16414705073199730381788845)
      ·
        refine ⟨6155514402449898893170817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16414705073199730381788845 6155514402449898893170817)
        ·
          refine ⟨4616635801837424169878113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6155514402449898893170817 4616635801837424169878113)
          ·
            refine ⟨3462476851378068127408585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4616635801837424169878113 3462476851378068127408585)
            ·
              refine ⟨2596857638533551095556439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462476851378068127408585 2596857638533551095556439)
              ·
                refine ⟨3895286457800326643334659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2596857638533551095556439 3895286457800326643334659)
                ·
                  refine ⟨5842929686700489965001989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895286457800326643334659 5842929686700489965001989)
                  ·
                    refine ⟨1095549316256341868437873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5842929686700489965001989 1095549316256341868437873)
                    ·
                      rfl

theorem cell22_3200362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_3200362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200362 prefixEnd_3200362 := by exact prefixLift 3200362
  have htrace : WordTrace (prefixWord ++ tailWord_3200362) baseStart_3200362 baseEnd_3200362 := by
    simpa [prefixWord, tailWord_3200362, baseEnd_3200362] using wordTrace_append hprefix tailTrace_3200362
  have hstable : (prefixWord ++ tailWord_3200362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200362).length < 2 ^ (prefixWord ++ tailWord_3200362).sum := by decide
  have hdescent : baseEnd_3200362 < baseStart_3200362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200384 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_3200384 : Nat := 118140960795 + 3200384 * 2 ^ 59
def prefixEnd_3200384 : Nat := 4983230072969 + 3 ^ 40 * 3200384 * 2
def baseEnd_3200384 : Nat := 1095556847305941144387805

theorem tailTrace_3200384 : CollatzResearch.WordTrace tailWord_3200384 prefixEnd_3200384 1095556847305941144387805 := by
  unfold tailWord_3200384
  simp only [CollatzResearch.WordTrace]
  refine ⟨58363797018781412458344103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77818396025041883277792137 58363797018781412458344103)
  ·
    refine ⟨87545695528172118687516155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58363797018781412458344103 87545695528172118687516155)
    ·
      refine ⟨131318543292258178031274233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87545695528172118687516155 131318543292258178031274233)
      ·
        refine ⟨98488907469193633523455675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131318543292258178031274233 98488907469193633523455675)
        ·
          refine ⟨147733361203790450285183513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98488907469193633523455675 147733361203790450285183513)
          ·
            refine ⟨110800020902842837713887635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147733361203790450285183513 110800020902842837713887635)
            ·
              refine ⟨166200031354264256570831453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110800020902842837713887635 166200031354264256570831453)
              ·
                refine ⟨62325011757849096214061795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166200031354264256570831453 62325011757849096214061795)
                ·
                  refine ⟨93487517636773644321092693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62325011757849096214061795 93487517636773644321092693)
                  ·
                    refine ⟨1095556847305941144387805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93487517636773644321092693 1095556847305941144387805)
                    ·
                      rfl

theorem cell22_3200384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_3200384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200384 prefixEnd_3200384 := by exact prefixLift 3200384
  have htrace : WordTrace (prefixWord ++ tailWord_3200384) baseStart_3200384 baseEnd_3200384 := by
    simpa [prefixWord, tailWord_3200384, baseEnd_3200384] using wordTrace_append hprefix tailTrace_3200384
  have hstable : (prefixWord ++ tailWord_3200384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200384).length < 2 ^ (prefixWord ++ tailWord_3200384).sum := by decide
  have hdescent : baseEnd_3200384 < baseStart_3200384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200446 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_3200446 : Nat := 118140960795 + 3200446 * 2 ^ 59
def prefixEnd_3200446 : Nat := 4983230072969 + 3 ^ 40 * 3200446 * 2
def baseEnd_3200446 : Nat := 1095578071172993649337615

theorem tailTrace_3200446 : CollatzResearch.WordTrace tailWord_3200446 prefixEnd_3200446 1095578071172993649337615 := by
  unfold tailWord_3200446
  simp only [CollatzResearch.WordTrace]
  refine ⟨14591231920417276188180649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77819903575558806336963461 14591231920417276188180649)
  ·
    refine ⟨10943423940312957141135487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14591231920417276188180649 10943423940312957141135487)
    ·
      refine ⟨16415135910469435711703231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10943423940312957141135487 16415135910469435711703231)
      ·
        refine ⟨24622703865704153567554847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16415135910469435711703231 24622703865704153567554847)
        ·
          refine ⟨36934055798556230351332271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24622703865704153567554847 36934055798556230351332271)
          ·
            refine ⟨55401083697834345526998407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36934055798556230351332271 55401083697834345526998407)
            ·
              refine ⟨83101625546751518290497611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55401083697834345526998407 83101625546751518290497611)
              ·
                refine ⟨124652438320127277435746417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83101625546751518290497611 124652438320127277435746417)
                ·
                  refine ⟨93489328740095458076809813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124652438320127277435746417 93489328740095458076809813)
                  ·
                    refine ⟨1095578071172993649337615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93489328740095458076809813 1095578071172993649337615)
                    ·
                      rfl

theorem cell22_3200446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_3200446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200446 prefixEnd_3200446 := by exact prefixLift 3200446
  have htrace : WordTrace (prefixWord ++ tailWord_3200446) baseStart_3200446 baseEnd_3200446 := by
    simpa [prefixWord, tailWord_3200446, baseEnd_3200446] using wordTrace_append hprefix tailTrace_3200446
  have hstable : (prefixWord ++ tailWord_3200446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200446).length < 2 ^ (prefixWord ++ tailWord_3200446).sum := by decide
  have hdescent : baseEnd_3200446 < baseStart_3200446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200463 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 1, 4]
def baseStart_3200463 : Nat := 118140960795 + 3200463 * 2 ^ 59
def prefixEnd_3200463 : Nat := 4983230072969 + 3 ^ 40 * 3200463 * 2
def baseEnd_3200463 : Nat := 1095583890620411271662563

theorem tailTrace_3200463 : CollatzResearch.WordTrace tailWord_3200463 prefixEnd_3200463 1095583890620411271662563 := by
  unfold tailWord_3200463
  simp only [CollatzResearch.WordTrace]
  refine ⟨116730475404276621408814043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77820316936184414272542695 116730475404276621408814043)
  ·
    refine ⟨175095713106414932113221065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116730475404276621408814043 175095713106414932113221065)
    ·
      refine ⟨131321784829811199084915799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175095713106414932113221065 131321784829811199084915799)
      ·
        refine ⟨196982677244716798627373699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131321784829811199084915799 196982677244716798627373699)
        ·
          refine ⟨295474015867075197941060549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196982677244716798627373699 295474015867075197941060549)
          ·
            refine ⟨55401377975076599613948853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295474015867075197941060549 55401377975076599613948853)
            ·
              refine ⟨5193879185163431213807705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55401377975076599613948853 5193879185163431213807705)
              ·
                refine ⟨3895409388872573410355779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5193879185163431213807705 3895409388872573410355779)
                ·
                  refine ⟨5843114083308860115533669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895409388872573410355779 5843114083308860115533669)
                  ·
                    refine ⟨1095583890620411271662563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5843114083308860115533669 1095583890620411271662563)
                    ·
                      rfl

theorem cell22_3200463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_3200463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200463 prefixEnd_3200463 := by exact prefixLift 3200463
  have htrace : WordTrace (prefixWord ++ tailWord_3200463) baseStart_3200463 baseEnd_3200463 := by
    simpa [prefixWord, tailWord_3200463, baseEnd_3200463] using wordTrace_append hprefix tailTrace_3200463
  have hstable : (prefixWord ++ tailWord_3200463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200463).length < 2 ^ (prefixWord ++ tailWord_3200463).sum := by decide
  have hdescent : baseEnd_3200463 < baseStart_3200463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200491 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 4, 4]
def baseStart_3200491 : Nat := 118140960795 + 3200491 * 2 ^ 59
def prefixEnd_3200491 : Nat := 4983230072969 + 3 ^ 40 * 3200491 * 2
def baseEnd_3200491 : Nat := 1095593475592628531962477

theorem tailTrace_3200491 : CollatzResearch.WordTrace tailWord_3200491 prefixEnd_3200491 1095593475592628531962477 := by
  unfold tailWord_3200491
  simp only [CollatzResearch.WordTrace]
  refine ⟨116731496648175182190833327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77820997765450121460555551 116731496648175182190833327)
  ·
    refine ⟨175097244972262773286249991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116731496648175182190833327 175097244972262773286249991)
    ·
      refine ⟨262645867458394159929374987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175097244972262773286249991 262645867458394159929374987)
      ·
        refine ⟨393968801187591239894062481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262645867458394159929374987 393968801187591239894062481)
        ·
          refine ⟨295476600890693429920546861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393968801187591239894062481 295476600890693429920546861)
          ·
            refine ⟨110803725334010036220205073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 295476600890693429920546861 110803725334010036220205073)
            ·
              refine ⟨83102794000507527165153805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110803725334010036220205073 83102794000507527165153805)
              ·
                refine ⟨31163547750190322686932677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83102794000507527165153805 31163547750190322686932677)
                ·
                  refine ⟨5843165203160685503799877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31163547750190322686932677 5843165203160685503799877)
                  ·
                    refine ⟨1095593475592628531962477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5843165203160685503799877 1095593475592628531962477)
                    ·
                      rfl

theorem cell22_3200491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 4].length) (baseStart_3200491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200491 prefixEnd_3200491 := by exact prefixLift 3200491
  have htrace : WordTrace (prefixWord ++ tailWord_3200491) baseStart_3200491 baseEnd_3200491 := by
    simpa [prefixWord, tailWord_3200491, baseEnd_3200491] using wordTrace_append hprefix tailTrace_3200491
  have hstable : (prefixWord ++ tailWord_3200491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200491).length < 2 ^ (prefixWord ++ tailWord_3200491).sum := by decide
  have hdescent : baseEnd_3200491 < baseStart_3200491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200495 : List Nat := [1, 1, 2, 1, 4, 1, 6, 2, 4]
def baseStart_3200495 : Nat := 118140960795 + 3200495 * 2 ^ 59
def prefixEnd_3200495 : Nat := 4983230072969 + 3 ^ 40 * 3200495 * 2
def baseEnd_3200495 : Nat := 365198281624791284954155

theorem tailTrace_3200495 : CollatzResearch.WordTrace tailWord_3200495 prefixEnd_3200495 365198281624791284954155 := by
  unfold tailWord_3200495
  simp only [CollatzResearch.WordTrace]
  refine ⟨116731642540160690873978939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77821095026773793915985959 116731642540160690873978939)
  ·
    refine ⟨175097463810241036310968409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116731642540160690873978939 175097463810241036310968409)
    ·
      refine ⟨131323097857680777233226307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175097463810241036310968409 131323097857680777233226307)
      ·
        refine ⟨196984646786521165849839461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131323097857680777233226307 196984646786521165849839461)
        ·
          refine ⟨36934621272472718596844899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196984646786521165849839461 36934621272472718596844899)
          ·
            refine ⟨55401931908709077895267349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36934621272472718596844899 55401931908709077895267349)
            ·
              refine ⟨2596965558220738026340657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55401931908709077895267349 2596965558220738026340657)
              ·
                refine ⟨1947724168665553519755493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596965558220738026340657 1947724168665553519755493)
                ·
                  refine ⟨365198281624791284954155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947724168665553519755493 365198281624791284954155)
                  ·
                    rfl

theorem cell22_3200495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 4].length) (baseStart_3200495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200495 prefixEnd_3200495 := by exact prefixLift 3200495
  have htrace : WordTrace (prefixWord ++ tailWord_3200495) baseStart_3200495 baseEnd_3200495 := by
    simpa [prefixWord, tailWord_3200495, baseEnd_3200495] using wordTrace_append hprefix tailTrace_3200495
  have hstable : (prefixWord ++ tailWord_3200495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200495).length < 2 ^ (prefixWord ++ tailWord_3200495).sum := by decide
  have hdescent : baseEnd_3200495 < baseStart_3200495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200538 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 7, 3]
def baseStart_3200538 : Nat := 118140960795 + 3200538 * 2 ^ 59
def prefixEnd_3200538 : Nat := 4983230072969 + 3 ^ 40 * 3200538 * 2
def baseEnd_3200538 : Nat := 1095609564653136076037333

theorem tailTrace_3200538 : CollatzResearch.WordTrace tailWord_3200538 prefixEnd_3200538 1095609564653136076037333 := by
  unfold tailWord_3200538
  simp only [CollatzResearch.WordTrace]
  refine ⟨29183302719751227304448567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77822140586003272811862845 29183302719751227304448567)
  ·
    refine ⟨43774954079626840956672851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29183302719751227304448567 43774954079626840956672851)
    ·
      refine ⟨65662431119440261435009277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43774954079626840956672851 65662431119440261435009277)
      ·
        refine ⟨24623411669790098038128479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65662431119440261435009277 24623411669790098038128479)
        ·
          refine ⟨36935117504685147057192719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24623411669790098038128479 36935117504685147057192719)
          ·
            refine ⟨55402676257027720585789079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36935117504685147057192719 55402676257027720585789079)
            ·
              refine ⟨83104014385541580878683619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55402676257027720585789079 83104014385541580878683619)
              ·
                refine ⟨124656021578312371318025429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83104014385541580878683619 124656021578312371318025429)
                ·
                  refine ⟨2921625505741696202766221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 124656021578312371318025429 2921625505741696202766221)
                  ·
                    refine ⟨1095609564653136076037333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2921625505741696202766221 1095609564653136076037333)
                    ·
                      rfl

theorem cell22_3200538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_3200538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200538 prefixEnd_3200538 := by exact prefixLift 3200538
  have htrace : WordTrace (prefixWord ++ tailWord_3200538) baseStart_3200538 baseEnd_3200538 := by
    simpa [prefixWord, tailWord_3200538, baseEnd_3200538] using wordTrace_append hprefix tailTrace_3200538
  have hstable : (prefixWord ++ tailWord_3200538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200538).length < 2 ^ (prefixWord ++ tailWord_3200538).sum := by decide
  have hdescent : baseEnd_3200538 < baseStart_3200538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200658 : List Nat := [3, 2, 3, 1, 13]
def baseStart_3200658 : Nat := 118140960795 + 3200658 * 2 ^ 59
def prefixEnd_3200658 : Nat := 4983230072969 + 3 ^ 40 * 3200658 * 2
def baseEnd_3200658 : Nat := 4508850383150188325255

theorem tailTrace_3200658 : CollatzResearch.WordTrace tailWord_3200658 prefixEnd_3200658 4508850383150188325255 := by
  unfold tailWord_3200658
  simp only [CollatzResearch.WordTrace]
  refine ⟨29184396909642542428040657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77825058425713446474775085 29184396909642542428040657)
  ·
    refine ⟨21888297682231906821030493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29184396909642542428040657 21888297682231906821030493)
    ·
      refine ⟨8208111630836965057886435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21888297682231906821030493 8208111630836965057886435)
      ·
        refine ⟨12312167446255447586829653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8208111630836965057886435 12312167446255447586829653)
        ·
          refine ⟨4508850383150188325255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12312167446255447586829653 4508850383150188325255)
          ·
            rfl

theorem cell22_3200658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 13].length) (baseStart_3200658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200658 prefixEnd_3200658 := by exact prefixLift 3200658
  have htrace : WordTrace (prefixWord ++ tailWord_3200658) baseStart_3200658 baseEnd_3200658 := by
    simpa [prefixWord, tailWord_3200658, baseEnd_3200658] using wordTrace_append hprefix tailTrace_3200658
  have hstable : (prefixWord ++ tailWord_3200658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200658).length < 2 ^ (prefixWord ++ tailWord_3200658).sum := by decide
  have hdescent : baseEnd_3200658 < baseStart_3200658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200664 : List Nat := [2, 1, 2, 4, 1, 4, 2, 2, 4]
def baseStart_3200664 : Nat := 118140960795 + 3200664 * 2 ^ 59
def prefixEnd_3200664 : Nat := 4983230072969 + 3 ^ 40 * 3200664 * 2
def baseEnd_3200664 : Nat := 365217565676037915795649

theorem tailTrace_3200664 : CollatzResearch.WordTrace tailWord_3200664 prefixEnd_3200664 365217565676037915795649 := by
  unfold tailWord_3200664
  simp only [CollatzResearch.WordTrace]
  refine ⟨58368903238274216368440523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77825204317698955157920697 58368903238274216368440523)
  ·
    refine ⟨87553354857411324552660785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58368903238274216368440523 87553354857411324552660785)
    ·
      refine ⟨65665016143058493414495589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87553354857411324552660785 65665016143058493414495589)
      ·
        refine ⟨12312190526823467515217923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65665016143058493414495589 12312190526823467515217923)
        ·
          refine ⟨18468285790235201272826885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12312190526823467515217923 18468285790235201272826885)
          ·
            refine ⟨3462803585669100238655041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18468285790235201272826885 3462803585669100238655041)
            ·
              refine ⟨2597102689251825178991281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462803585669100238655041 2597102689251825178991281)
              ·
                refine ⟨1947827016938868884243461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2597102689251825178991281 1947827016938868884243461)
                ·
                  refine ⟨365217565676037915795649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947827016938868884243461 365217565676037915795649)
                  ·
                    rfl

theorem cell22_3200664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 4].length) (baseStart_3200664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200664 prefixEnd_3200664 := by exact prefixLift 3200664
  have htrace : WordTrace (prefixWord ++ tailWord_3200664) baseStart_3200664 baseEnd_3200664 := by
    simpa [prefixWord, tailWord_3200664, baseEnd_3200664] using wordTrace_append hprefix tailTrace_3200664
  have hstable : (prefixWord ++ tailWord_3200664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200664).length < 2 ^ (prefixWord ++ tailWord_3200664).sum := by decide
  have hdescent : baseEnd_3200664 < baseStart_3200664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200690 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_3200690 : Nat := 118140960795 + 3200690 * 2 ^ 59
def prefixEnd_3200690 : Nat := 4983230072969 + 3 ^ 40 * 3200690 * 2
def baseEnd_3200690 : Nat := 1095661597359458346236867

theorem tailTrace_3200690 : CollatzResearch.WordTrace tailWord_3200690 prefixEnd_3200690 1095661597359458346236867 := by
  unfold tailWord_3200690
  simp only [CollatzResearch.WordTrace]
  refine ⟨29184688693613559794331881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77825836516302826118218349 29184688693613559794331881)
  ·
    refine ⟨21888516520210169845748911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29184688693613559794331881 21888516520210169845748911)
    ·
      refine ⟨32832774780315254768623367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21888516520210169845748911 32832774780315254768623367)
      ·
        refine ⟨49249162170472882152935051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32832774780315254768623367 49249162170472882152935051)
        ·
          refine ⟨73873743255709323229402577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49249162170472882152935051 73873743255709323229402577)
          ·
            refine ⟨55405307441781992422051933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73873743255709323229402577 55405307441781992422051933)
            ·
              refine ⟨20776990290668247158269475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55405307441781992422051933 20776990290668247158269475)
              ·
                refine ⟨31165485436002370737404213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20776990290668247158269475 31165485436002370737404213)
                ·
                  refine ⟨2921764259625222256631645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31165485436002370737404213 2921764259625222256631645)
                  ·
                    refine ⟨1095661597359458346236867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2921764259625222256631645 1095661597359458346236867)
                    ·
                      rfl

theorem cell22_3200690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_3200690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200690 prefixEnd_3200690 := by exact prefixLift 3200690
  have htrace : WordTrace (prefixWord ++ tailWord_3200690) baseStart_3200690 baseEnd_3200690 := by
    simpa [prefixWord, tailWord_3200690, baseEnd_3200690] using wordTrace_append hprefix tailTrace_3200690
  have hstable : (prefixWord ++ tailWord_3200690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200690).length < 2 ^ (prefixWord ++ tailWord_3200690).sum := by decide
  have hdescent : baseEnd_3200690 < baseStart_3200690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200694 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3200694 : Nat := 118140960795 + 3200694 * 2 ^ 59
def prefixEnd_3200694 : Nat := 4983230072969 + 3 ^ 40 * 3200694 * 2
def baseEnd_3200694 : Nat := 1095662966641203669136855

theorem tailTrace_3200694 : CollatzResearch.WordTrace tailWord_3200694 prefixEnd_3200694 1095662966641203669136855 := by
  unfold tailWord_3200694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7296181291652484241279571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77825933777626498573648757 7296181291652484241279571)
  ·
    refine ⟨10944271937478726361919357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7296181291652484241279571 10944271937478726361919357)
    ·
      refine ⟨4104101976554522385719759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10944271937478726361919357 4104101976554522385719759)
      ·
        refine ⟨6156152964831783578579639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104101976554522385719759 6156152964831783578579639)
        ·
          refine ⟨9234229447247675367869459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6156152964831783578579639 9234229447247675367869459)
          ·
            refine ⟨13851344170871513051804189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9234229447247675367869459 13851344170871513051804189)
            ·
              refine ⟨5194254064076817394426571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13851344170871513051804189 5194254064076817394426571)
              ·
                refine ⟨7791381096115226091639857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194254064076817394426571 7791381096115226091639857)
                ·
                  refine ⟨5843535822086419568729893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7791381096115226091639857 5843535822086419568729893)
                  ·
                    refine ⟨1095662966641203669136855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5843535822086419568729893 1095662966641203669136855)
                    ·
                      rfl

theorem cell22_3200694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3200694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200694 prefixEnd_3200694 := by exact prefixLift 3200694
  have htrace : WordTrace (prefixWord ++ tailWord_3200694) baseStart_3200694 baseEnd_3200694 := by
    simpa [prefixWord, tailWord_3200694, baseEnd_3200694] using wordTrace_append hprefix tailTrace_3200694
  have hstable : (prefixWord ++ tailWord_3200694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200694).length < 2 ^ (prefixWord ++ tailWord_3200694).sum := by decide
  have hdescent : baseEnd_3200694 < baseStart_3200694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200703 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 7]
def baseStart_3200703 : Nat := 118140960795 + 3200703 * 2 ^ 59
def prefixEnd_3200703 : Nat := 4983230072969 + 3 ^ 40 * 3200703 * 2
def baseEnd_3200703 : Nat := 365222015841710215220609

theorem tailTrace_3200703 : CollatzResearch.WordTrace tailWord_3200703 prefixEnd_3200703 365222015841710215220609 := by
  unfold tailWord_3200703
  simp only [CollatzResearch.WordTrace]
  refine ⟨116739228923407142397550763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77826152615604761598367175 116739228923407142397550763)
  ·
    refine ⟨175108843385110713596326145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116739228923407142397550763 175108843385110713596326145)
    ·
      refine ⟨131331632538833035197244609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175108843385110713596326145 131331632538833035197244609)
      ·
        refine ⟨98498724404124776397933457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131331632538833035197244609 98498724404124776397933457)
        ·
          refine ⟨73874043303093582298450093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98498724404124776397933457 73874043303093582298450093)
          ·
            refine ⟨27702766238660093361918785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73874043303093582298450093 27702766238660093361918785)
            ·
              refine ⟨20777074678995070021439089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27702766238660093361918785 20777074678995070021439089)
              ·
                refine ⟨15582806009246302516079317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20777074678995070021439089 15582806009246302516079317)
                ·
                  refine ⟨365222015841710215220609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15582806009246302516079317 365222015841710215220609)
                  ·
                    rfl

theorem cell22_3200703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 7].length) (baseStart_3200703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200703 prefixEnd_3200703 := by exact prefixLift 3200703
  have htrace : WordTrace (prefixWord ++ tailWord_3200703) baseStart_3200703 baseEnd_3200703 := by
    simpa [prefixWord, tailWord_3200703, baseEnd_3200703] using wordTrace_append hprefix tailTrace_3200703
  have hstable : (prefixWord ++ tailWord_3200703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200703).length < 2 ^ (prefixWord ++ tailWord_3200703).sum := by decide
  have hdescent : baseEnd_3200703 < baseStart_3200703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200724 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_3200724 : Nat := 118140960795 + 3200724 * 2 ^ 59
def prefixEnd_3200724 : Nat := 4983230072969 + 3 ^ 40 * 3200724 * 2
def baseEnd_3200724 : Nat := 1095673236254293590886763

theorem tailTrace_3200724 : CollatzResearch.WordTrace tailWord_3200724 prefixEnd_3200724 1095673236254293590886763 := by
  unfold tailWord_3200724
  simp only [CollatzResearch.WordTrace]
  refine ⟨58369997428165531492032613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77826663237554041989376817 58369997428165531492032613)
  ·
    refine ⟨10944374517781037154756115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58369997428165531492032613 10944374517781037154756115)
    ·
      refine ⟨16416561776671555732134173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10944374517781037154756115 16416561776671555732134173)
      ·
        refine ⟨6156210666251833399550315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16416561776671555732134173 6156210666251833399550315)
        ·
          refine ⟨9234315999377750099325473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6156210666251833399550315 9234315999377750099325473)
          ·
            refine ⟨6925736999533312574494105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9234315999377750099325473 6925736999533312574494105)
            ·
              refine ⟨5194302749649984430870579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6925736999533312574494105 5194302749649984430870579)
              ·
                refine ⟨7791454124474976646305869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194302749649984430870579 7791454124474976646305869)
                ·
                  refine ⟨2921795296678116242364701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7791454124474976646305869 2921795296678116242364701)
                  ·
                    refine ⟨1095673236254293590886763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2921795296678116242364701 1095673236254293590886763)
                    ·
                      rfl

theorem cell22_3200724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_3200724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200724 prefixEnd_3200724 := by exact prefixLift 3200724
  have htrace : WordTrace (prefixWord ++ tailWord_3200724) baseStart_3200724 baseEnd_3200724 := by
    simpa [prefixWord, tailWord_3200724, baseEnd_3200724] using wordTrace_append hprefix tailTrace_3200724
  have hstable : (prefixWord ++ tailWord_3200724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200724).length < 2 ^ (prefixWord ++ tailWord_3200724).sum := by decide
  have hdescent : baseEnd_3200724 < baseStart_3200724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200782 : List Nat := [4, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_3200782 : Nat := 118140960795 + 3200782 * 2 ^ 59
def prefixEnd_3200782 : Nat := 4983230072969 + 3 ^ 40 * 3200782 * 2
def baseEnd_3200782 : Nat := 365231030279866924312195

theorem tailTrace_3200782 : CollatzResearch.WordTrace tailWord_3200782 prefixEnd_3200782 365231030279866924312195 := by
  unfold tailWord_3200782
  simp only [CollatzResearch.WordTrace]
  refine ⟨14592763786265117361209575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77828073526747292593117733 14592763786265117361209575)
  ·
    refine ⟨21889145679397676041814363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14592763786265117361209575 21889145679397676041814363)
    ·
      refine ⟨32833718519096514062721545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21889145679397676041814363 32833718519096514062721545)
      ·
        refine ⟨24625288889322385547041159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32833718519096514062721545 24625288889322385547041159)
        ·
          refine ⟨36937933333983578320561739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24625288889322385547041159 36937933333983578320561739)
          ·
            refine ⟨55406900000975367480842609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36937933333983578320561739 55406900000975367480842609)
            ·
              refine ⟨41555175000731525610631957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55406900000975367480842609 41555175000731525610631957)
              ·
                refine ⟨1947898828159290262998373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41555175000731525610631957 1947898828159290262998373)
                ·
                  refine ⟨365231030279866924312195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1947898828159290262998373 365231030279866924312195)
                  ·
                    rfl

theorem cell22_3200782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_3200782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200782 prefixEnd_3200782 := by exact prefixLift 3200782
  have htrace : WordTrace (prefixWord ++ tailWord_3200782) baseStart_3200782 baseEnd_3200782 := by
    simpa [prefixWord, tailWord_3200782, baseEnd_3200782] using wordTrace_append hprefix tailTrace_3200782
  have hstable : (prefixWord ++ tailWord_3200782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200782).length < 2 ^ (prefixWord ++ tailWord_3200782).sum := by decide
  have hdescent : baseEnd_3200782 < baseStart_3200782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200812 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 2, 4]
def baseStart_3200812 : Nat := 118140960795 + 3200812 * 2 ^ 59
def prefixEnd_3200812 : Nat := 4983230072969 + 3 ^ 40 * 3200812 * 2
def baseEnd_3200812 : Nat := 1095703360452690694686493

theorem tailTrace_3200812 : CollatzResearch.WordTrace tailWord_3200812 prefixEnd_3200812 1095703360452690694686493 := by
  unfold tailWord_3200812
  simp only [CollatzResearch.WordTrace]
  refine ⟨58371602240006127006634345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77828802986674836008845793 58371602240006127006634345)
  ·
    refine ⟨43778701680004595254975759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58371602240006127006634345 43778701680004595254975759)
    ·
      refine ⟨65668052520006892882463639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43778701680004595254975759 65668052520006892882463639)
      ·
        refine ⟨98502078780010339323695459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65668052520006892882463639 98502078780010339323695459)
        ·
          refine ⟨147753118170015508985543189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98502078780010339323695459 147753118170015508985543189)
          ·
            refine ⟨6925927414219476983697337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147753118170015508985543189 6925927414219476983697337)
            ·
              refine ⟨5194445560664607737773003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6925927414219476983697337 5194445560664607737773003)
              ·
                refine ⟨7791668340996911606659505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194445560664607737773003 7791668340996911606659505)
                ·
                  refine ⟨5843751255747683704994629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7791668340996911606659505 5843751255747683704994629)
                  ·
                    refine ⟨1095703360452690694686493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5843751255747683704994629 1095703360452690694686493)
                    ·
                      rfl

theorem cell22_3200812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_3200812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200812 prefixEnd_3200812 := by exact prefixLift 3200812
  have htrace : WordTrace (prefixWord ++ tailWord_3200812) baseStart_3200812 baseEnd_3200812 := by
    simpa [prefixWord, tailWord_3200812, baseEnd_3200812] using wordTrace_append hprefix tailTrace_3200812
  have hstable : (prefixWord ++ tailWord_3200812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200812).length < 2 ^ (prefixWord ++ tailWord_3200812).sum := by decide
  have hdescent : baseEnd_3200812 < baseStart_3200812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200814 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3200814 : Nat := 118140960795 + 3200814 * 2 ^ 59
def prefixEnd_3200814 : Nat := 4983230072969 + 3 ^ 40 * 3200814 * 2
def baseEnd_3200814 : Nat := 1095704045093563356136487

theorem tailTrace_3200814 : CollatzResearch.WordTrace tailWord_3200814 prefixEnd_3200814 1095704045093563356136487 := by
  unfold tailWord_3200814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14592909678250626044355187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77828851617336672236560997 14592909678250626044355187)
  ·
    refine ⟨21889364517375939066532781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14592909678250626044355187 21889364517375939066532781)
    ·
      refine ⟨8208511694015977149949793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21889364517375939066532781 8208511694015977149949793)
      ·
        refine ⟨6156383770511982862462345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8208511694015977149949793 6156383770511982862462345)
        ·
          refine ⟨4617287827883987146846759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6156383770511982862462345 4617287827883987146846759)
          ·
            refine ⟨6925931741825980720270139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617287827883987146846759 6925931741825980720270139)
            ·
              refine ⟨10388897612738971080405209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6925931741825980720270139 10388897612738971080405209)
              ·
                refine ⟨7791673209554228310303907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10388897612738971080405209 7791673209554228310303907)
                ·
                  refine ⟨11687509814331342465455861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7791673209554228310303907 11687509814331342465455861)
                  ·
                    refine ⟨1095704045093563356136487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11687509814331342465455861 1095704045093563356136487)
                    ·
                      rfl

theorem cell22_3200814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3200814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200814 prefixEnd_3200814 := by exact prefixLift 3200814
  have htrace : WordTrace (prefixWord ++ tailWord_3200814) baseStart_3200814 baseEnd_3200814 := by
    simpa [prefixWord, tailWord_3200814, baseEnd_3200814] using wordTrace_append hprefix tailTrace_3200814
  have hstable : (prefixWord ++ tailWord_3200814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200814).length < 2 ^ (prefixWord ++ tailWord_3200814).sum := by decide
  have hdescent : baseEnd_3200814 < baseStart_3200814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200840 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_3200840 : Nat := 118140960795 + 3200840 * 2 ^ 59
def prefixEnd_3200840 : Nat := 4983230072969 + 3 ^ 40 * 3200840 * 2
def baseEnd_3200840 : Nat := 1095712945424907954986407

theorem tailTrace_3200840 : CollatzResearch.WordTrace tailWord_3200840 prefixEnd_3200840 1095712945424907954986407 := by
  unfold tailWord_3200840
  simp only [CollatzResearch.WordTrace]
  refine ⟨58372112861955407397643987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77829483815940543196858649 58372112861955407397643987)
  ·
    refine ⟨87558169292933111096465981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58372112861955407397643987 87558169292933111096465981)
    ·
      refine ⟨32834313484849916661174743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87558169292933111096465981 32834313484849916661174743)
      ·
        refine ⟨49251470227274874991762115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32834313484849916661174743 49251470227274874991762115)
        ·
          refine ⟨73877205340912312487643173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49251470227274874991762115 73877205340912312487643173)
          ·
            refine ⟨13851976001421058591433095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73877205340912312487643173 13851976001421058591433095)
            ·
              refine ⟨20777964002131587887149643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13851976001421058591433095 20777964002131587887149643)
              ·
                refine ⟨31166946003197381830724465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20777964002131587887149643 31166946003197381830724465)
                ·
                  refine ⟨23375209502398036373043349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31166946003197381830724465 23375209502398036373043349)
                  ·
                    refine ⟨1095712945424907954986407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23375209502398036373043349 1095712945424907954986407)
                    ·
                      rfl

theorem cell22_3200840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_3200840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200840 prefixEnd_3200840 := by exact prefixLift 3200840
  have htrace : WordTrace (prefixWord ++ tailWord_3200840) baseStart_3200840 baseEnd_3200840 := by
    simpa [prefixWord, tailWord_3200840, baseEnd_3200840] using wordTrace_append hprefix tailTrace_3200840
  have hstable : (prefixWord ++ tailWord_3200840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200840).length < 2 ^ (prefixWord ++ tailWord_3200840).sum := by decide
  have hdescent : baseEnd_3200840 < baseStart_3200840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200842 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 3, 3]
def baseStart_3200842 : Nat := 118140960795 + 3200842 * 2 ^ 59
def prefixEnd_3200842 : Nat := 4983230072969 + 3 ^ 40 * 3200842 * 2
def baseEnd_3200842 : Nat := 1095713630065780616436401

theorem tailTrace_3200842 : CollatzResearch.WordTrace tailWord_3200842 prefixEnd_3200842 1095713630065780616436401 := by
  unfold tailWord_3200842
  simp only [CollatzResearch.WordTrace]
  refine ⟨29186074667475892284215195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77829532446602379424573853 29186074667475892284215195)
  ·
    refine ⟨43779112001213838426322793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29186074667475892284215195 43779112001213838426322793)
    ·
      refine ⟨32834334000910378819742095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43779112001213838426322793 32834334000910378819742095)
      ·
        refine ⟨49251501001365568229613143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32834334000910378819742095 49251501001365568229613143)
        ·
          refine ⟨73877251502048352344419715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49251501001365568229613143 73877251502048352344419715)
          ·
            refine ⟨110815877253072528516629573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73877251502048352344419715 110815877253072528516629573)
            ·
              refine ⟨20777976984951099096868045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110815877253072528516629573 20777976984951099096868045)
              ·
                refine ⟨7791741369356662161325517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20777976984951099096868045 7791741369356662161325517)
                ·
                  refine ⟨2921903013508748310497069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7791741369356662161325517 2921903013508748310497069)
                  ·
                    refine ⟨1095713630065780616436401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2921903013508748310497069 1095713630065780616436401)
                    ·
                      rfl

theorem cell22_3200842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_3200842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200842 prefixEnd_3200842 := by exact prefixLift 3200842
  have htrace : WordTrace (prefixWord ++ tailWord_3200842) baseStart_3200842 baseEnd_3200842 := by
    simpa [prefixWord, tailWord_3200842, baseEnd_3200842] using wordTrace_append hprefix tailTrace_3200842
  have hstable : (prefixWord ++ tailWord_3200842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200842).length < 2 ^ (prefixWord ++ tailWord_3200842).sum := by decide
  have hdescent : baseEnd_3200842 < baseStart_3200842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200844 : List Nat := [2, 2, 1, 3, 5, 1, 1, 7]
def baseStart_3200844 : Nat := 118140960795 + 3200844 * 2 ^ 59
def prefixEnd_3200844 : Nat := 4983230072969 + 3 ^ 40 * 3200844 * 2
def baseEnd_3200844 : Nat := 121746034967405919765155

theorem tailTrace_3200844 : CollatzResearch.WordTrace tailWord_3200844 prefixEnd_3200844 121746034967405919765155 := by
  unfold tailWord_3200844
  simp only [CollatzResearch.WordTrace]
  refine ⟨58372185807948161739216793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77829581077264215652289057 58372185807948161739216793)
  ·
    refine ⟨43779139355961121304412595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58372185807948161739216793 43779139355961121304412595)
    ·
      refine ⟨65668709033941681956618893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43779139355961121304412595 65668709033941681956618893)
      ·
        refine ⟨24625765887728130733732085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65668709033941681956618893 24625765887728130733732085)
        ·
          refine ⟨2308665551974512256287383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24625765887728130733732085 2308665551974512256287383)
          ·
            refine ⟨3462998327961768384431075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308665551974512256287383 3462998327961768384431075)
            ·
              refine ⟨5194497491942652576646613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462998327961768384431075 5194497491942652576646613)
              ·
                refine ⟨121746034967405919765155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5194497491942652576646613 121746034967405919765155)
                ·
                  rfl

theorem cell22_3200844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 7].length) (baseStart_3200844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200844 prefixEnd_3200844 := by exact prefixLift 3200844
  have htrace : WordTrace (prefixWord ++ tailWord_3200844) baseStart_3200844 baseEnd_3200844 := by
    simpa [prefixWord, tailWord_3200844, baseEnd_3200844] using wordTrace_append hprefix tailTrace_3200844
  have hstable : (prefixWord ++ tailWord_3200844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200844).length < 2 ^ (prefixWord ++ tailWord_3200844).sum := by decide
  have hdescent : baseEnd_3200844 < baseStart_3200844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200876 : List Nat := [2, 2, 1, 1, 4, 3, 2, 3, 1, 3]
def baseStart_3200876 : Nat := 118140960795 + 3200876 * 2 ^ 59
def prefixEnd_3200876 : Nat := 4983230072969 + 3 ^ 40 * 3200876 * 2
def baseEnd_3200876 : Nat := 1095725268960615861086297

theorem tailTrace_3200876 : CollatzResearch.WordTrace tailWord_3200876 prefixEnd_3200876 1095725268960615861086297 := by
  unfold tailWord_3200876
  simp only [CollatzResearch.WordTrace]
  refine ⟨58372769375890196471799241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77830359167853595295732321 58372769375890196471799241)
  ·
    refine ⟨43779577031917647353849431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58372769375890196471799241 43779577031917647353849431)
    ·
      refine ⟨65669365547876471030774147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43779577031917647353849431 65669365547876471030774147)
      ·
        refine ⟨98504048321814706546161221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65669365547876471030774147 98504048321814706546161221)
        ·
          refine ⟨18469509060340257477405229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98504048321814706546161221 18469509060340257477405229)
          ·
            refine ⟨6926065897627596554026961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18469509060340257477405229 6926065897627596554026961)
            ·
              refine ⟨5194549423220697415520221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6926065897627596554026961 5194549423220697415520221)
              ·
                refine ⟨1947956033707761530820083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5194549423220697415520221 1947956033707761530820083)
                ·
                  refine ⟨2921934050561642296230125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947956033707761530820083 2921934050561642296230125)
                  ·
                    refine ⟨1095725268960615861086297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2921934050561642296230125 1095725268960615861086297)
                    ·
                      rfl

theorem cell22_3200876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_3200876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200876 prefixEnd_3200876 := by exact prefixLift 3200876
  have htrace : WordTrace (prefixWord ++ tailWord_3200876) baseStart_3200876 baseEnd_3200876 := by
    simpa [prefixWord, tailWord_3200876, baseEnd_3200876] using wordTrace_append hprefix tailTrace_3200876
  have hstable : (prefixWord ++ tailWord_3200876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200876).length < 2 ^ (prefixWord ++ tailWord_3200876).sum := by decide
  have hdescent : baseEnd_3200876 < baseStart_3200876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200906 : List Nat := [3, 1, 2, 4, 2, 1, 3, 1, 5]
def baseStart_3200906 : Nat := 118140960795 + 3200906 * 2 ^ 59
def prefixEnd_3200906 : Nat := 4983230072969 + 3 ^ 40 * 3200906 * 2
def baseEnd_3200906 : Nat := 365245179524568594278735

theorem tailTrace_3200906 : CollatzResearch.WordTrace tailWord_3200906 prefixEnd_3200906 365245179524568594278735 := by
  unfold tailWord_3200906
  simp only [CollatzResearch.WordTrace]
  refine ⟨29186658235417927016797643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77831088627781138711460381 29186658235417927016797643)
  ·
    refine ⟨43779987353126890525196465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29186658235417927016797643 43779987353126890525196465)
    ·
      refine ⟨32834990514845167893897349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43779987353126890525196465 32834990514845167893897349)
      ·
        refine ⟨6156560721533468980105753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32834990514845167893897349 6156560721533468980105753)
        ·
          refine ⟨4617420541150101735079315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6156560721533468980105753 4617420541150101735079315)
          ·
            refine ⟨6926130811725152602618973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617420541150101735079315 6926130811725152602618973)
            ·
              refine ⟨2597299054396932225982115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6926130811725152602618973 2597299054396932225982115)
              ·
                refine ⟨3895948581595398338973173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2597299054396932225982115 3895948581595398338973173)
                ·
                  refine ⟨365245179524568594278735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3895948581595398338973173 365245179524568594278735)
                  ·
                    rfl

theorem cell22_3200906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_3200906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200906 prefixEnd_3200906 := by exact prefixLift 3200906
  have htrace : WordTrace (prefixWord ++ tailWord_3200906) baseStart_3200906 baseEnd_3200906 := by
    simpa [prefixWord, tailWord_3200906, baseEnd_3200906] using wordTrace_append hprefix tailTrace_3200906
  have hstable : (prefixWord ++ tailWord_3200906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200906).length < 2 ^ (prefixWord ++ tailWord_3200906).sum := by decide
  have hdescent : baseEnd_3200906 < baseStart_3200906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200919 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 1, 4]
def baseStart_3200919 : Nat := 118140960795 + 3200919 * 2 ^ 59
def prefixEnd_3200919 : Nat := 4983230072969 + 3 ^ 40 * 3200919 * 2
def baseEnd_3200919 : Nat := 1095739988739378082261165

theorem tailTrace_3200919 : CollatzResearch.WordTrace tailWord_3200919 prefixEnd_3200919 1095739988739378082261165 := by
  unfold tailWord_3200919
  simp only [CollatzResearch.WordTrace]
  refine ⟨116747107090624611287413811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77831404727083074191609207 116747107090624611287413811)
  ·
    refine ⟨175120660635936916931120717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116747107090624611287413811 175120660635936916931120717)
    ·
      refine ⟨65670247738476343849170269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175120660635936916931120717 65670247738476343849170269)
      ·
        refine ⟨24626342901928628943438851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65670247738476343849170269 24626342901928628943438851)
        ·
          refine ⟨36939514352892943415158277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24626342901928628943438851 36939514352892943415158277)
          ·
            refine ⟨6926158941167426890342177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36939514352892943415158277 6926158941167426890342177)
            ·
              refine ⟨5194619205875570167756633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6926158941167426890342177 5194619205875570167756633)
              ·
                refine ⟨3895964404406677625817475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5194619205875570167756633 3895964404406677625817475)
                ·
                  refine ⟨5843946606610016438726213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895964404406677625817475 5843946606610016438726213)
                  ·
                    refine ⟨1095739988739378082261165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5843946606610016438726213 1095739988739378082261165)
                    ·
                      rfl

theorem cell22_3200919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_3200919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200919 prefixEnd_3200919 := by exact prefixLift 3200919
  have htrace : WordTrace (prefixWord ++ tailWord_3200919) baseStart_3200919 baseEnd_3200919 := by
    simpa [prefixWord, tailWord_3200919, baseEnd_3200919] using wordTrace_append hprefix tailTrace_3200919
  have hstable : (prefixWord ++ tailWord_3200919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200919).length < 2 ^ (prefixWord ++ tailWord_3200919).sum := by decide
  have hdescent : baseEnd_3200919 < baseStart_3200919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200947 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 2, 4]
def baseStart_3200947 : Nat := 118140960795 + 3200947 * 2 ^ 59
def prefixEnd_3200947 : Nat := 4983230072969 + 3 ^ 40 * 3200947 * 2
def baseEnd_3200947 : Nat := 1095749573711595342561079

theorem tailTrace_3200947 : CollatzResearch.WordTrace tailWord_3200947 prefixEnd_3200947 1095749573711595342561079 := by
  unfold tailWord_3200947
  simp only [CollatzResearch.WordTrace]
  refine ⟨116748128334523172069433095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77832085556348781379622063 116748128334523172069433095)
  ·
    refine ⟨175122192501784758104149643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116748128334523172069433095 175122192501784758104149643)
    ·
      refine ⟨262683288752677137156224465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175122192501784758104149643 262683288752677137156224465)
      ·
        refine ⟨197012466564507852867168349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 262683288752677137156224465 197012466564507852867168349)
        ·
          refine ⟨73879674961690444825188131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197012466564507852867168349 73879674961690444825188131)
          ·
            refine ⟨110819512442535667237782197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73879674961690444825188131 110819512442535667237782197)
            ·
              refine ⟨10389329291487718803542081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110819512442535667237782197 10389329291487718803542081)
              ·
                refine ⟨7791996968615789102656561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10389329291487718803542081 7791996968615789102656561)
                ·
                  refine ⟨5843997726461841826992421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7791996968615789102656561 5843997726461841826992421)
                  ·
                    refine ⟨1095749573711595342561079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5843997726461841826992421 1095749573711595342561079)
                    ·
                      rfl

theorem cell22_3200947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 4].length) (baseStart_3200947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200947 prefixEnd_3200947 := by exact prefixLift 3200947
  have htrace : WordTrace (prefixWord ++ tailWord_3200947) baseStart_3200947 baseEnd_3200947 := by
    simpa [prefixWord, tailWord_3200947, baseEnd_3200947] using wordTrace_append hprefix tailTrace_3200947
  have hstable : (prefixWord ++ tailWord_3200947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200947).length < 2 ^ (prefixWord ++ tailWord_3200947).sum := by decide
  have hdescent : baseEnd_3200947 < baseStart_3200947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3200949 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 4, 3]
def baseStart_3200949 : Nat := 118140960795 + 3200949 * 2 ^ 59
def prefixEnd_3200949 : Nat := 4983230072969 + 3 ^ 40 * 3200949 * 2
def baseEnd_3200949 : Nat := 1095750258352468004011073

theorem tailTrace_3200949 : CollatzResearch.WordTrace tailWord_3200949 prefixEnd_3200949 1095750258352468004011073 := by
  unfold tailWord_3200949
  simp only [CollatzResearch.WordTrace]
  refine ⟨116748201280515926411005901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77832134187010617607337267 116748201280515926411005901)
  ·
    refine ⟨43780575480193472404127213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116748201280515926411005901 43780575480193472404127213)
    ·
      refine ⟨16417715805072552151547705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43780575480193472404127213 16417715805072552151547705)
      ·
        refine ⟨12313286853804414113660779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16417715805072552151547705 12313286853804414113660779)
        ·
          refine ⟨18469930280706621170491169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12313286853804414113660779 18469930280706621170491169)
          ·
            refine ⟨13852447710529965877868377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18469930280706621170491169 13852447710529965877868377)
            ·
              refine ⟨10389335782897474408401283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13852447710529965877868377 10389335782897474408401283)
              ·
                refine ⟨15584003674346211612601925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10389335782897474408401283 15584003674346211612601925)
                ·
                  refine ⟨2922000688939914677362861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15584003674346211612601925 2922000688939914677362861)
                  ·
                    refine ⟨1095750258352468004011073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922000688939914677362861 1095750258352468004011073)
                    ·
                      rfl

theorem cell22_3200949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_3200949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3200949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3200949 prefixEnd_3200949 := by exact prefixLift 3200949
  have htrace : WordTrace (prefixWord ++ tailWord_3200949) baseStart_3200949 baseEnd_3200949 := by
    simpa [prefixWord, tailWord_3200949, baseEnd_3200949] using wordTrace_append hprefix tailTrace_3200949
  have hstable : (prefixWord ++ tailWord_3200949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3200949).length < 2 ^ (prefixWord ++ tailWord_3200949).sum := by decide
  have hdescent : baseEnd_3200949 < baseStart_3200949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3200949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201028 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 3, 3]
def baseStart_3201028 : Nat := 118140960795 + 3201028 * 2 ^ 59
def prefixEnd_3201028 : Nat := 4983230072969 + 3 ^ 40 * 3201028 * 2
def baseEnd_3201028 : Nat := 1095777301666938131285831

theorem tailTrace_3201028 : CollatzResearch.WordTrace tailWord_3201028 prefixEnd_3201028 1095777301666938131285831 := by
  unfold tailWord_3201028
  simp only [CollatzResearch.WordTrace]
  refine ⟨58375541323614861451565869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77834055098153148602087825 58375541323614861451565869)
  ·
    refine ⟨21890827996355573044337201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58375541323614861451565869 21890827996355573044337201)
    ·
      refine ⟨16418120997266679783252901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21890827996355573044337201 16418120997266679783252901)
      ·
        refine ⟨3078397686987502459359919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16418120997266679783252901 3078397686987502459359919)
        ·
          refine ⟨4617596530481253689039879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078397686987502459359919 4617596530481253689039879)
          ·
            refine ⟨6926394795721880533559819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617596530481253689039879 6926394795721880533559819)
            ·
              refine ⟨10389592193582820800339729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6926394795721880533559819 10389592193582820800339729)
              ·
                refine ⟨7792194145187115600254797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10389592193582820800339729 7792194145187115600254797)
                ·
                  refine ⟨2922072804445168350095549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7792194145187115600254797 2922072804445168350095549)
                  ·
                    refine ⟨1095777301666938131285831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922072804445168350095549 1095777301666938131285831)
                    ·
                      rfl

theorem cell22_3201028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_3201028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201028 prefixEnd_3201028 := by exact prefixLift 3201028
  have htrace : WordTrace (prefixWord ++ tailWord_3201028) baseStart_3201028 baseEnd_3201028 := by
    simpa [prefixWord, tailWord_3201028, baseEnd_3201028] using wordTrace_append hprefix tailTrace_3201028
  have hstable : (prefixWord ++ tailWord_3201028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201028).length < 2 ^ (prefixWord ++ tailWord_3201028).sum := by decide
  have hdescent : baseEnd_3201028 < baseStart_3201028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201097 : List Nat := [1, 2, 1, 1, 2, 2, 5, 8]
def baseStart_3201097 : Nat := 118140960795 + 3201097 * 2 ^ 59
def prefixEnd_3201097 : Nat := 4983230072969 + 3 ^ 40 * 3201097 * 2
def baseEnd_3201097 : Nat := 121755657975227216812291

theorem tailTrace_3201097 : CollatzResearch.WordTrace tailWord_3201097 prefixEnd_3201097 121755657975227216812291 := by
  unfold tailWord_3201097
  simp only [CollatzResearch.WordTrace]
  refine ⟨116753599283979747687393545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77835732855986498458262363 116753599283979747687393545)
  ·
    refine ⟨87565199462984810765545159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116753599283979747687393545 87565199462984810765545159)
    ·
      refine ⟨131347799194477216148317739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87565199462984810765545159 131347799194477216148317739)
      ·
        refine ⟨197021698791715824222476609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131347799194477216148317739 197021698791715824222476609)
        ·
          refine ⟨147766274093786868166857457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197021698791715824222476609 147766274093786868166857457)
          ·
            refine ⟨110824705570340151125143093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147766274093786868166857457 110824705570340151125143093)
            ·
              refine ⟨10389816147219389167982165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110824705570340151125143093 10389816147219389167982165)
              ·
                refine ⟨121755657975227216812291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10389816147219389167982165 121755657975227216812291)
                ·
                  rfl

theorem cell22_3201097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 8].length) (baseStart_3201097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201097 prefixEnd_3201097 := by exact prefixLift 3201097
  have htrace : WordTrace (prefixWord ++ tailWord_3201097) baseStart_3201097 baseEnd_3201097 := by
    simpa [prefixWord, tailWord_3201097, baseEnd_3201097] using wordTrace_append hprefix tailTrace_3201097
  have hstable : (prefixWord ++ tailWord_3201097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201097).length < 2 ^ (prefixWord ++ tailWord_3201097).sum := by decide
  have hdescent : baseEnd_3201097 < baseStart_3201097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201101 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3201101 : Nat := 118140960795 + 3201101 * 2 ^ 59
def prefixEnd_3201101 : Nat := 4983230072969 + 3 ^ 40 * 3201101 * 2
def baseEnd_3201101 : Nat := 1095802291058790274210607

theorem tailTrace_3201101 : CollatzResearch.WordTrace tailWord_3201101 prefixEnd_3201101 1095802291058790274210607 := by
  unfold tailWord_3201101
  simp only [CollatzResearch.WordTrace]
  refine ⟨116753745175965256370539157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77835830117310170913692771 116753745175965256370539157)
  ·
    refine ⟨5472831805123371392369023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116753745175965256370539157 5472831805123371392369023)
    ·
      refine ⟨8209247707685057088553535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5472831805123371392369023 8209247707685057088553535)
      ·
        refine ⟨12313871561527585632830303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8209247707685057088553535 12313871561527585632830303)
        ·
          refine ⟨18470807342291378449245455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12313871561527585632830303 18470807342291378449245455)
          ·
            refine ⟨27706211013437067673868183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18470807342291378449245455 27706211013437067673868183)
            ·
              refine ⟨41559316520155601510802275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27706211013437067673868183 41559316520155601510802275)
              ·
                refine ⟨62338974780233402266203413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41559316520155601510802275 62338974780233402266203413)
                ·
                  refine ⟨2922139442823440731228285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62338974780233402266203413 2922139442823440731228285)
                  ·
                    refine ⟨1095802291058790274210607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922139442823440731228285 1095802291058790274210607)
                    ·
                      rfl

theorem cell22_3201101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3201101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201101 prefixEnd_3201101 := by exact prefixLift 3201101
  have htrace : WordTrace (prefixWord ++ tailWord_3201101) baseStart_3201101 baseEnd_3201101 := by
    simpa [prefixWord, tailWord_3201101, baseEnd_3201101] using wordTrace_append hprefix tailTrace_3201101
  have hstable : (prefixWord ++ tailWord_3201101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201101).length < 2 ^ (prefixWord ++ tailWord_3201101).sum := by decide
  have hdescent : baseEnd_3201101 < baseStart_3201101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201116 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3201116 : Nat := 118140960795 + 3201116 * 2 ^ 59
def prefixEnd_3201116 : Nat := 4983230072969 + 3 ^ 40 * 3201116 * 2
def baseEnd_3201116 : Nat := 1095807425865335235085561

theorem tailTrace_3201116 : CollatzResearch.WordTrace tailWord_3201116 prefixEnd_3201116 1095807425865335235085561 := by
  unfold tailWord_3201116
  simp only [CollatzResearch.WordTrace]
  refine ⟨58377146135455456966167601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77836194847273942621556801 58377146135455456966167601)
  ·
    refine ⟨43782859601591592724625701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58377146135455456966167601 43782859601591592724625701)
    ·
      refine ⟨8209286175298423635867319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43782859601591592724625701 8209286175298423635867319)
      ·
        refine ⟨12313929262947635453800979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8209286175298423635867319 12313929262947635453800979)
        ·
          refine ⟨18470893894421453180701469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12313929262947635453800979 18470893894421453180701469)
          ·
            refine ⟨6926585210408044942763051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18470893894421453180701469 6926585210408044942763051)
            ·
              refine ⟨10389877815612067414144577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6926585210408044942763051 10389877815612067414144577)
              ·
                refine ⟨7792408361709050560608433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10389877815612067414144577 7792408361709050560608433)
                ·
                  refine ⟨5844306271281787920456325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7792408361709050560608433 5844306271281787920456325)
                  ·
                    refine ⟨1095807425865335235085561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5844306271281787920456325 1095807425865335235085561)
                    ·
                      rfl

theorem cell22_3201116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3201116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201116 prefixEnd_3201116 := by exact prefixLift 3201116
  have htrace : WordTrace (prefixWord ++ tailWord_3201116) baseStart_3201116 baseEnd_3201116 := by
    simpa [prefixWord, tailWord_3201116, baseEnd_3201116] using wordTrace_append hprefix tailTrace_3201116
  have hstable : (prefixWord ++ tailWord_3201116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201116).length < 2 ^ (prefixWord ++ tailWord_3201116).sum := by decide
  have hdescent : baseEnd_3201116 < baseStart_3201116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201189 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_3201189 : Nat := 118140960795 + 3201189 * 2 ^ 59
def prefixEnd_3201189 : Nat := 4983230072969 + 3 ^ 40 * 3201189 * 2
def baseEnd_3201189 : Nat := 1095832415257187378010337

theorem tailTrace_3201189 : CollatzResearch.WordTrace tailWord_3201189 prefixEnd_3201189 1095832415257187378010337 := by
  unfold tailWord_3201189
  simp only [CollatzResearch.WordTrace]
  refine ⟨116756954799646447399742621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77837969866430964933161747 116756954799646447399742621)
  ·
    refine ⟨43783858049867417774903483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116756954799646447399742621 43783858049867417774903483)
    ·
      refine ⟨65675787074801126662355225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43783858049867417774903483 65675787074801126662355225)
      ·
        refine ⟨49256840306100844996766419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65675787074801126662355225 49256840306100844996766419)
        ·
          refine ⟨73885260459151267495149629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49256840306100844996766419 73885260459151267495149629)
          ·
            refine ⟨27706972672181725310681111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73885260459151267495149629 27706972672181725310681111)
            ·
              refine ⟨41560459008272587966021667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27706972672181725310681111 41560459008272587966021667)
              ·
                refine ⟨62340688512408881949032501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41560459008272587966021667 62340688512408881949032501)
                ·
                  refine ⟨5844439548038332682721797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62340688512408881949032501 5844439548038332682721797)
                  ·
                    refine ⟨1095832415257187378010337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5844439548038332682721797 1095832415257187378010337)
                    ·
                      rfl

theorem cell22_3201189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_3201189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201189 prefixEnd_3201189 := by exact prefixLift 3201189
  have htrace : WordTrace (prefixWord ++ tailWord_3201189) baseStart_3201189 baseEnd_3201189 := by
    simpa [prefixWord, tailWord_3201189, baseEnd_3201189] using wordTrace_append hprefix tailTrace_3201189
  have hstable : (prefixWord ++ tailWord_3201189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201189).length < 2 ^ (prefixWord ++ tailWord_3201189).sum := by decide
  have hdescent : baseEnd_3201189 < baseStart_3201189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201221 : List Nat := [1, 3, 1, 1, 1, 1, 5, 5, 4]
def baseStart_3201221 : Nat := 118140960795 + 3201221 * 2 ^ 59
def prefixEnd_3201221 : Nat := 4983230072969 + 3 ^ 40 * 3201221 * 2
def baseEnd_3201221 : Nat := 365281123170383320403413

theorem tailTrace_3201221 : CollatzResearch.WordTrace tailWord_3201221 prefixEnd_3201221 365281123170383320403413 := by
  unfold tailWord_3201221
  simp only [CollatzResearch.WordTrace]
  refine ⟨116758121935530516864907517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77838747957020344576605011 116758121935530516864907517)
  ·
    refine ⟨43784295725823943824340319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116758121935530516864907517 43784295725823943824340319)
    ·
      refine ⟨65676443588735915736510479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43784295725823943824340319 65676443588735915736510479)
      ·
        refine ⟨98514665383103873604765719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65676443588735915736510479 98514665383103873604765719)
        ·
          refine ⟨147771998074655810407148579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98514665383103873604765719 147771998074655810407148579)
          ·
            refine ⟨221657997111983715610722869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147771998074655810407148579 221657997111983715610722869)
            ·
              refine ⟨20780437229248473338505269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221657997111983715610722869 20780437229248473338505269)
              ·
                refine ⟨1948165990242044375484869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20780437229248473338505269 1948165990242044375484869)
                ·
                  refine ⟨365281123170383320403413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1948165990242044375484869 365281123170383320403413)
                  ·
                    rfl

theorem cell22_3201221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_3201221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201221 prefixEnd_3201221 := by exact prefixLift 3201221
  have htrace : WordTrace (prefixWord ++ tailWord_3201221) baseStart_3201221 baseEnd_3201221 := by
    simpa [prefixWord, tailWord_3201221, baseEnd_3201221] using wordTrace_append hprefix tailTrace_3201221
  have hstable : (prefixWord ++ tailWord_3201221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201221).length < 2 ^ (prefixWord ++ tailWord_3201221).sum := by decide
  have hdescent : baseEnd_3201221 < baseStart_3201221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201238 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3201238 : Nat := 118140960795 + 3201238 * 2 ^ 59
def prefixEnd_3201238 : Nat := 4983230072969 + 3 ^ 40 * 3201238 * 2
def baseEnd_3201238 : Nat := 365283062986189194511729

theorem tailTrace_3201238 : CollatzResearch.WordTrace tailWord_3201238 prefixEnd_3201238 365283062986189194511729 := by
  unfold tailWord_3201238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7297421373529308048017273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77839161317645952512184245 7297421373529308048017273)
  ·
    refine ⟨5473066030146981036012955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7297421373529308048017273 5473066030146981036012955)
    ·
      refine ⟨8209599045220471554019433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5473066030146981036012955 8209599045220471554019433)
      ·
        refine ⟨6157199283915353665514575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8209599045220471554019433 6157199283915353665514575)
        ·
          refine ⟨9235798925873030498271863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6157199283915353665514575 9235798925873030498271863)
          ·
            refine ⟨13853698388809545747407795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9235798925873030498271863 13853698388809545747407795)
            ·
              refine ⟨20780547583214318621111693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13853698388809545747407795 20780547583214318621111693)
              ·
                refine ⟨7792705343705369482916885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20780547583214318621111693 7792705343705369482916885)
                ·
                  refine ⟨365283062986189194511729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7792705343705369482916885 365283062986189194511729)
                  ·
                    rfl

theorem cell22_3201238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3201238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201238 prefixEnd_3201238 := by exact prefixLift 3201238
  have htrace : WordTrace (prefixWord ++ tailWord_3201238) baseStart_3201238 baseEnd_3201238 := by
    simpa [prefixWord, tailWord_3201238, baseEnd_3201238] using wordTrace_append hprefix tailTrace_3201238
  have hstable : (prefixWord ++ tailWord_3201238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201238).length < 2 ^ (prefixWord ++ tailWord_3201238).sum := by decide
  have hdescent : baseEnd_3201238 < baseStart_3201238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201249 : List Nat := [1, 2, 3, 1, 3, 1, 2, 9]
def baseStart_3201249 : Nat := 118140960795 + 3201249 * 2 ^ 59
def prefixEnd_3201249 : Nat := 4983230072969 + 3 ^ 40 * 3201249 * 2
def baseEnd_3201249 : Nat := 121761439387040802390017

theorem tailTrace_3201249 : CollatzResearch.WordTrace tailWord_3201249 prefixEnd_3201249 121761439387040802390017 := by
  unfold tailWord_3201249
  simp only [CollatzResearch.WordTrace]
  refine ⟨116759143179429077646926801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77839428786286051764617867 116759143179429077646926801)
  ·
    refine ⟨87569357384571808235195101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116759143179429077646926801 87569357384571808235195101)
    ·
      refine ⟨32838509019214428088198163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87569357384571808235195101 32838509019214428088198163)
      ·
        refine ⟨49257763528821642132297245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32838509019214428088198163 49257763528821642132297245)
        ·
          refine ⟨18471661323308115799611467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49257763528821642132297245 18471661323308115799611467)
          ·
            refine ⟨27707491984962173699417201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18471661323308115799611467 27707491984962173699417201)
            ·
              refine ⟨20780618988721630274562901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27707491984962173699417201 20780618988721630274562901)
              ·
                refine ⟨121761439387040802390017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20780618988721630274562901 121761439387040802390017)
                ·
                  rfl

theorem cell22_3201249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 9].length) (baseStart_3201249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201249 prefixEnd_3201249 := by exact prefixLift 3201249
  have htrace : WordTrace (prefixWord ++ tailWord_3201249) baseStart_3201249 baseEnd_3201249 := by
    simpa [prefixWord, tailWord_3201249, baseEnd_3201249] using wordTrace_append hprefix tailTrace_3201249
  have hstable : (prefixWord ++ tailWord_3201249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201249).length < 2 ^ (prefixWord ++ tailWord_3201249).sum := by decide
  have hdescent : baseEnd_3201249 < baseStart_3201249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201253 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 1, 5]
def baseStart_3201253 : Nat := 118140960795 + 3201253 * 2 ^ 59
def prefixEnd_3201253 : Nat := 4983230072969 + 3 ^ 40 * 3201253 * 2
def baseEnd_3201253 : Nat := 1095854323765112544410141

theorem tailTrace_3201253 : CollatzResearch.WordTrace tailWord_3201253 prefixEnd_3201253 1095854323765112544410141 := by
  unfold tailWord_3201253
  simp only [CollatzResearch.WordTrace]
  refine ⟨116759289071414586330072413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77839526047609724220048275 116759289071414586330072413)
  ·
    refine ⟨43784733401780469873777155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116759289071414586330072413 43784733401780469873777155)
    ·
      refine ⟨65677100102670704810665733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43784733401780469873777155 65677100102670704810665733)
      ·
        refine ⟨12314456269250757151999825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65677100102670704810665733 12314456269250757151999825)
        ·
          refine ⟨9235842201938067863999869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12314456269250757151999825 9235842201938067863999869)
          ·
            refine ⟨3463440825726775448999951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9235842201938067863999869 3463440825726775448999951)
            ·
              refine ⟨5195161238590163173499927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463440825726775448999951 5195161238590163173499927)
              ·
                refine ⟨7792741857885244760249891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5195161238590163173499927 7792741857885244760249891)
                ·
                  refine ⟨11689112786827867140374837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7792741857885244760249891 11689112786827867140374837)
                  ·
                    refine ⟨1095854323765112544410141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11689112786827867140374837 1095854323765112544410141)
                    ·
                      rfl

theorem cell22_3201253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_3201253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201253 prefixEnd_3201253 := by exact prefixLift 3201253
  have htrace : WordTrace (prefixWord ++ tailWord_3201253) baseStart_3201253 baseEnd_3201253 := by
    simpa [prefixWord, tailWord_3201253, baseEnd_3201253] using wordTrace_append hprefix tailTrace_3201253
  have hstable : (prefixWord ++ tailWord_3201253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201253).length < 2 ^ (prefixWord ++ tailWord_3201253).sum := by decide
  have hdescent : baseEnd_3201253 < baseStart_3201253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201266 : List Nat := [3, 2, 1, 3, 2, 2, 1, 8]
def baseStart_3201266 : Nat := 118140960795 + 3201266 * 2 ^ 59
def prefixEnd_3201266 : Nat := 4983230072969 + 3 ^ 40 * 3201266 * 2
def baseEnd_3201266 : Nat := 121762085992309427092789

theorem tailTrace_3201266 : CollatzResearch.WordTrace tailWord_3201266 prefixEnd_3201266 121762085992309427092789 := by
  unfold tailWord_3201266
  simp only [CollatzResearch.WordTrace]
  refine ⟨29189940805091872387573913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77839842146911659700197101 29189940805091872387573913)
  ·
    refine ⟨21892455603818904290680435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29189940805091872387573913 21892455603818904290680435)
    ·
      refine ⟨32838683405728356436020653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21892455603818904290680435 32838683405728356436020653)
      ·
        refine ⟨12314506277148133663507745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32838683405728356436020653 12314506277148133663507745)
        ·
          refine ⟨9235879707861100247630809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12314506277148133663507745 9235879707861100247630809)
          ·
            refine ⟨6926909780895825185723107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9235879707861100247630809 6926909780895825185723107)
            ·
              refine ⟨10390364671343737778584661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6926909780895825185723107 10390364671343737778584661)
              ·
                refine ⟨121762085992309427092789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10390364671343737778584661 121762085992309427092789)
                ·
                  rfl

theorem cell22_3201266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_3201266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201266 prefixEnd_3201266 := by exact prefixLift 3201266
  have htrace : WordTrace (prefixWord ++ tailWord_3201266) baseStart_3201266 baseEnd_3201266 := by
    simpa [prefixWord, tailWord_3201266, baseEnd_3201266] using wordTrace_append hprefix tailTrace_3201266
  have hstable : (prefixWord ++ tailWord_3201266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201266).length < 2 ^ (prefixWord ++ tailWord_3201266).sum := by decide
  have hdescent : baseEnd_3201266 < baseStart_3201266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201345 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 5]
def baseStart_3201345 : Nat := 118140960795 + 3201345 * 2 ^ 59
def prefixEnd_3201345 : Nat := 4983230072969 + 3 ^ 40 * 3201345 * 2
def baseEnd_3201345 : Nat := 365295272415084990369953

theorem tailTrace_3201345 : CollatzResearch.WordTrace tailWord_3201345 prefixEnd_3201345 365295272415084990369953 := by
  unfold tailWord_3201345
  simp only [CollatzResearch.WordTrace]
  refine ⟨116762644587081286042421489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77841763058054190694947659 116762644587081286042421489)
  ·
    refine ⟨87571983440310964531816117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116762644587081286042421489 87571983440310964531816117)
    ·
      refine ⟨8209873447529152924857761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87571983440310964531816117 8209873447529152924857761)
      ·
        refine ⟨6157405085646864693643321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8209873447529152924857761 6157405085646864693643321)
        ·
          refine ⟨4618053814235148520232491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6157405085646864693643321 4618053814235148520232491)
          ·
            refine ⟨6927080721352722780348737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4618053814235148520232491 6927080721352722780348737)
            ·
              refine ⟨5195310541014542085261553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6927080721352722780348737 5195310541014542085261553)
              ·
                refine ⟨3896482905760906563946165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5195310541014542085261553 3896482905760906563946165)
                ·
                  refine ⟨365295272415084990369953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3896482905760906563946165 365295272415084990369953)
                  ·
                    rfl

theorem cell22_3201345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_3201345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201345 prefixEnd_3201345 := by exact prefixLift 3201345
  have htrace : WordTrace (prefixWord ++ tailWord_3201345) baseStart_3201345 baseEnd_3201345 := by
    simpa [prefixWord, tailWord_3201345, baseEnd_3201345] using wordTrace_append hprefix tailTrace_3201345
  have hstable : (prefixWord ++ tailWord_3201345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201345).length < 2 ^ (prefixWord ++ tailWord_3201345).sum := by decide
  have hdescent : baseEnd_3201345 < baseStart_3201345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201356 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 6]
def baseStart_3201356 : Nat := 118140960795 + 3201356 * 2 ^ 59
def prefixEnd_3201356 : Nat := 4983230072969 + 3 ^ 40 * 3201356 * 2
def baseEnd_3201356 : Nat := 365296527590018203028275

theorem tailTrace_3201356 : CollatzResearch.WordTrace tailWord_3201356 prefixEnd_3201356 365296527590018203028275 := by
  unfold tailWord_3201356
  simp only [CollatzResearch.WordTrace]
  refine ⟨58381522895020717460535961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77842030526694289947381281 58381522895020717460535961)
  ·
    refine ⟨43786142171265538095401971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58381522895020717460535961 43786142171265538095401971)
    ·
      refine ⟨65679213256898307143102957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43786142171265538095401971 65679213256898307143102957)
      ·
        refine ⟨24629704971336865178663609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65679213256898307143102957 24629704971336865178663609)
        ·
          refine ⟨18472278728502648883997707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24629704971336865178663609 18472278728502648883997707)
          ·
            refine ⟨27708418092753973325996561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18472278728502648883997707 27708418092753973325996561)
            ·
              refine ⟨20781313569565479994497421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27708418092753973325996561 20781313569565479994497421)
              ·
                refine ⟨7792992588587054997936533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20781313569565479994497421 7792992588587054997936533)
                ·
                  refine ⟨365296527590018203028275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7792992588587054997936533 365296527590018203028275)
                  ·
                    rfl

theorem cell22_3201356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_3201356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201356 prefixEnd_3201356 := by exact prefixLift 3201356
  have htrace : WordTrace (prefixWord ++ tailWord_3201356) baseStart_3201356 baseEnd_3201356 := by
    simpa [prefixWord, tailWord_3201356, baseEnd_3201356] using wordTrace_append hprefix tailTrace_3201356
  have hstable : (prefixWord ++ tailWord_3201356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201356).length < 2 ^ (prefixWord ++ tailWord_3201356).sum := by decide
  have hdescent : baseEnd_3201356 < baseStart_3201356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201405 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_3201405 : Nat := 118140960795 + 3201405 * 2 ^ 59
def prefixEnd_3201405 : Nat := 4983230072969 + 3 ^ 40 * 3201405 * 2
def baseEnd_3201405 : Nat := 1095906356471434814609675

theorem tailTrace_3201405 : CollatzResearch.WordTrace tailWord_3201405 prefixEnd_3201405 1095906356471434814609675 := by
  unfold tailWord_3201405
  simp only [CollatzResearch.WordTrace]
  refine ⟨116764832966863916289605669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77843221977909277526403779 116764832966863916289605669)
  ·
    refine ⟨21893406181286984304301063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116764832966863916289605669 21893406181286984304301063)
    ·
      refine ⟨32840109271930476456451595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21893406181286984304301063 32840109271930476456451595)
      ·
        refine ⟨49260163907895714684677393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32840109271930476456451595 49260163907895714684677393)
        ·
          refine ⟨36945122930921786013508045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49260163907895714684677393 36945122930921786013508045)
          ·
            refine ⟨13854421099095669755065517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36945122930921786013508045 13854421099095669755065517)
            ·
              refine ⟨5195407912160876158149569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13854421099095669755065517 5195407912160876158149569)
              ·
                refine ⟨3896555934120657118612177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5195407912160876158149569 3896555934120657118612177)
                ·
                  refine ⟨2922416950590492838959133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3896555934120657118612177 2922416950590492838959133)
                  ·
                    refine ⟨1095906356471434814609675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922416950590492838959133 1095906356471434814609675)
                    ·
                      rfl

theorem cell22_3201405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_3201405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201405 prefixEnd_3201405 := by exact prefixLift 3201405
  have htrace : WordTrace (prefixWord ++ tailWord_3201405) baseStart_3201405 baseEnd_3201405 := by
    simpa [prefixWord, tailWord_3201405, baseEnd_3201405] using wordTrace_append hprefix tailTrace_3201405
  have hstable : (prefixWord ++ tailWord_3201405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201405).length < 2 ^ (prefixWord ++ tailWord_3201405).sum := by decide
  have hdescent : baseEnd_3201405 < baseStart_3201405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201431 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 2, 6]
def baseStart_3201431 : Nat := 118140960795 + 3201431 * 2 ^ 59
def prefixEnd_3201431 : Nat := 4983230072969 + 3 ^ 40 * 3201431 * 2
def baseEnd_3201431 : Nat := 1095915256802779413459595

theorem tailTrace_3201431 : CollatzResearch.WordTrace tailWord_3201431 prefixEnd_3201431 1095915256802779413459595 := by
  unfold tailWord_3201431
  simp only [CollatzResearch.WordTrace]
  refine ⟨116765781264769722730052147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77843854176513148486701431 116765781264769722730052147)
  ·
    refine ⟨175148671897154584095078221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116765781264769722730052147 175148671897154584095078221)
    ·
      refine ⟨65680751961432969035654333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175148671897154584095078221 65680751961432969035654333)
      ·
        refine ⟨24630281985537363388370375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65680751961432969035654333 24630281985537363388370375)
        ·
          refine ⟨36945422978306045082555563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24630281985537363388370375 36945422978306045082555563)
          ·
            refine ⟨55418134467459067623833345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36945422978306045082555563 55418134467459067623833345)
            ·
              refine ⟨41563600850594300717875009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55418134467459067623833345 41563600850594300717875009)
              ·
                refine ⟨31172700637945725538406257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41563600850594300717875009 31172700637945725538406257)
                ·
                  refine ⟨23379525478459294153804693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31172700637945725538406257 23379525478459294153804693)
                  ·
                    refine ⟨1095915256802779413459595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23379525478459294153804693 1095915256802779413459595)
                    ·
                      rfl

theorem cell22_3201431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_3201431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201431 prefixEnd_3201431 := by exact prefixLift 3201431
  have htrace : WordTrace (prefixWord ++ tailWord_3201431) baseStart_3201431 baseEnd_3201431 := by
    simpa [prefixWord, tailWord_3201431, baseEnd_3201431] using wordTrace_append hprefix tailTrace_3201431
  have hstable : (prefixWord ++ tailWord_3201431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201431).length < 2 ^ (prefixWord ++ tailWord_3201431).sum := by decide
  have hdescent : baseEnd_3201431 < baseStart_3201431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201433 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 3, 3]
def baseStart_3201433 : Nat := 118140960795 + 3201433 * 2 ^ 59
def prefixEnd_3201433 : Nat := 4983230072969 + 3 ^ 40 * 3201433 * 2
def baseEnd_3201433 : Nat := 1095915941443652074909589

theorem tailTrace_3201433 : CollatzResearch.WordTrace tailWord_3201433 prefixEnd_3201433 1095915941443652074909589 := by
  unfold tailWord_3201433
  simp only [CollatzResearch.WordTrace]
  refine ⟨116765854210762477071624953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77843902807174984714416635 116765854210762477071624953)
  ·
    refine ⟨87574390658071857803718715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116765854210762477071624953 87574390658071857803718715)
    ·
      refine ⟨131361585987107786705578073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87574390658071857803718715 131361585987107786705578073)
      ·
        refine ⟨98521189490330840029183555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131361585987107786705578073 98521189490330840029183555)
        ·
          refine ⟨147781784235496260043775333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98521189490330840029183555 147781784235496260043775333)
          ·
            refine ⟨27709084544155548758207875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147781784235496260043775333 27709084544155548758207875)
            ·
              refine ⟨41563626816233323137311813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27709084544155548758207875 41563626816233323137311813)
              ·
                refine ⟨7793180028043748088245965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41563626816233323137311813 7793180028043748088245965)
                ·
                  refine ⟨2922442510516405533092237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7793180028043748088245965 2922442510516405533092237)
                  ·
                    refine ⟨1095915941443652074909589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922442510516405533092237 1095915941443652074909589)
                    ·
                      rfl

theorem cell22_3201433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 3].length) (baseStart_3201433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201433 prefixEnd_3201433 := by exact prefixLift 3201433
  have htrace : WordTrace (prefixWord ++ tailWord_3201433) baseStart_3201433 baseEnd_3201433 := by
    simpa [prefixWord, tailWord_3201433, baseEnd_3201433] using wordTrace_append hprefix tailTrace_3201433
  have hstable : (prefixWord ++ tailWord_3201433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201433).length < 2 ^ (prefixWord ++ tailWord_3201433).sum := by decide
  have hdescent : baseEnd_3201433 < baseStart_3201433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201473 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3201473 : Nat := 118140960795 + 3201473 * 2 ^ 59
def prefixEnd_3201473 : Nat := 4983230072969 + 3 ^ 40 * 3201473 * 2
def baseEnd_3201473 : Nat := 1095929634261105303909467

theorem tailTrace_3201473 : CollatzResearch.WordTrace tailWord_3201473 prefixEnd_3201473 1095929634261105303909467 := by
  unfold tailWord_3201473
  simp only [CollatzResearch.WordTrace]
  refine ⟨116767313130617563903081073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77844875420411709268720715 116767313130617563903081073)
  ·
    refine ⟨87575484847963172927310805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116767313130617563903081073 87575484847963172927310805)
    ·
      refine ⟨2052550426124136865483847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 87575484847963172927310805 2052550426124136865483847)
      ·
        refine ⟨3078825639186205298225771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052550426124136865483847 3078825639186205298225771)
        ·
          refine ⟨4618238458779307947338657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078825639186205298225771 4618238458779307947338657)
          ·
            refine ⟨3463678844084480960503993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4618238458779307947338657 3463678844084480960503993)
            ·
              refine ⟨2597759133063360720377995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3463678844084480960503993 2597759133063360720377995)
              ·
                refine ⟨3896638699595041080566993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2597759133063360720377995 3896638699595041080566993)
                ·
                  refine ⟨2922479024696280810425245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3896638699595041080566993 2922479024696280810425245)
                  ·
                    refine ⟨1095929634261105303909467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922479024696280810425245 1095929634261105303909467)
                    ·
                      rfl

theorem cell22_3201473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3201473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201473 prefixEnd_3201473 := by exact prefixLift 3201473
  have htrace : WordTrace (prefixWord ++ tailWord_3201473) baseStart_3201473 baseEnd_3201473 := by
    simpa [prefixWord, tailWord_3201473, baseEnd_3201473] using wordTrace_append hprefix tailTrace_3201473
  have hstable : (prefixWord ++ tailWord_3201473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201473).length < 2 ^ (prefixWord ++ tailWord_3201473).sum := by decide
  have hdescent : baseEnd_3201473 < baseStart_3201473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201480 : List Nat := [2, 1, 3, 1, 3, 2, 4, 1, 5]
def baseStart_3201480 : Nat := 118140960795 + 3201480 * 2 ^ 59
def prefixEnd_3201480 : Nat := 4983230072969 + 3 ^ 40 * 3201480 * 2
def baseEnd_3201480 : Nat := 365310676834719872994815

theorem tailTrace_3201480 : CollatzResearch.WordTrace tailWord_3201480 prefixEnd_3201480 365310676834719872994815 := by
  unfold tailWord_3201480
  simp only [CollatzResearch.WordTrace]
  refine ⟨58383784220796102049292947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77845045627728136065723929 58383784220796102049292947)
  ·
    refine ⟨87575676331194153073939421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58383784220796102049292947 87575676331194153073939421)
    ·
      refine ⟨32840878624197807402727283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87575676331194153073939421 32840878624197807402727283)
      ·
        refine ⟨49261317936296711104090925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32840878624197807402727283 49261317936296711104090925)
        ·
          refine ⟨18472994226111266664034097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49261317936296711104090925 18472994226111266664034097)
          ·
            refine ⟨13854745669583449998025573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18472994226111266664034097 13854745669583449998025573)
            ·
              refine ⟨2597764813046896874629795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13854745669583449998025573 2597764813046896874629795)
              ·
                refine ⟨3896647219570345311944693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2597764813046896874629795 3896647219570345311944693)
                ·
                  refine ⟨365310676834719872994815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3896647219570345311944693 365310676834719872994815)
                  ·
                    rfl

theorem cell22_3201480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 1, 5].length) (baseStart_3201480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201480 prefixEnd_3201480 := by exact prefixLift 3201480
  have htrace : WordTrace (prefixWord ++ tailWord_3201480) baseStart_3201480 baseEnd_3201480 := by
    simpa [prefixWord, tailWord_3201480, baseEnd_3201480] using wordTrace_append hprefix tailTrace_3201480
  have hstable : (prefixWord ++ tailWord_3201480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201480).length < 2 ^ (prefixWord ++ tailWord_3201480).sum := by decide
  have hdescent : baseEnd_3201480 < baseStart_3201480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201540 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_3201540 : Nat := 118140960795 + 3201540 * 2 ^ 59
def prefixEnd_3201540 : Nat := 4983230072969 + 3 ^ 40 * 3201540 * 2
def baseEnd_3201540 : Nat := 1095952569730339462484261

theorem tailTrace_3201540 : CollatzResearch.WordTrace tailWord_3201540 prefixEnd_3201540 1095952569730339462484261 := by
  unfold tailWord_3201540
  simp only [CollatzResearch.WordTrace]
  refine ⟨58384878410687417172885037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77846504547583222897180049 58384878410687417172885037)
  ·
    refine ⟨21894329404007781439831889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58384878410687417172885037 21894329404007781439831889)
    ·
      refine ⟨16420747053005836079873917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21894329404007781439831889 16420747053005836079873917)
      ·
        refine ⟨6157780144877188529952719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16420747053005836079873917 6157780144877188529952719)
        ·
          refine ⟨9236670217315782794929079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6157780144877188529952719 9236670217315782794929079)
          ·
            refine ⟨13855005325973674192393619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9236670217315782794929079 13855005325973674192393619)
            ·
              refine ⟨20782507988960511288590429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13855005325973674192393619 20782507988960511288590429)
              ·
                refine ⟨7793440495860191733221411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20782507988960511288590429 7793440495860191733221411)
                ·
                  refine ⟨11690160743790287599832117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7793440495860191733221411 11690160743790287599832117)
                  ·
                    refine ⟨1095952569730339462484261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11690160743790287599832117 1095952569730339462484261)
                    ·
                      rfl

theorem cell22_3201540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_3201540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201540 prefixEnd_3201540 := by exact prefixLift 3201540
  have htrace : WordTrace (prefixWord ++ tailWord_3201540) baseStart_3201540 baseEnd_3201540 := by
    simpa [prefixWord, tailWord_3201540, baseEnd_3201540] using wordTrace_append hprefix tailTrace_3201540
  have hstable : (prefixWord ++ tailWord_3201540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201540).length < 2 ^ (prefixWord ++ tailWord_3201540).sum := by decide
  have hdescent : baseEnd_3201540 < baseStart_3201540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201559 : List Nat := [1, 1, 3, 6, 1, 1, 2, 3, 4]
def baseStart_3201559 : Nat := 118140960795 + 3201559 * 2 ^ 59
def prefixEnd_3201559 : Nat := 4983230072969 + 3 ^ 40 * 3201559 * 2
def baseEnd_3201559 : Nat := 365319691272876582086401

theorem tailTrace_3201559 : CollatzResearch.WordTrace tailWord_3201559 prefixEnd_3201559 365319691272876582086401 := by
  unfold tailWord_3201559
  simp only [CollatzResearch.WordTrace]
  refine ⟨116770449808306000590711731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77846966538870667060474487 116770449808306000590711731)
  ·
    refine ⟨175155674712459000886067597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116770449808306000590711731 175155674712459000886067597)
    ·
      refine ⟨65683378017172125332275349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175155674712459000886067597 65683378017172125332275349)
      ·
        refine ⟨3078908344554943374950407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65683378017172125332275349 3078908344554943374950407)
        ·
          refine ⟨4618362516832415062425611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078908344554943374950407 4618362516832415062425611)
          ·
            refine ⟨6927543775248622593638417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4618362516832415062425611 6927543775248622593638417)
            ·
              refine ⟨5195657831436466945228813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6927543775248622593638417 5195657831436466945228813)
              ·
                refine ⟨1948371686788675104460805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5195657831436466945228813 1948371686788675104460805)
                ·
                  refine ⟨365319691272876582086401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1948371686788675104460805 365319691272876582086401)
                  ·
                    rfl

theorem cell22_3201559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 4].length) (baseStart_3201559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201559 prefixEnd_3201559 := by exact prefixLift 3201559
  have htrace : WordTrace (prefixWord ++ tailWord_3201559) baseStart_3201559 baseEnd_3201559 := by
    simpa [prefixWord, tailWord_3201559, baseEnd_3201559] using wordTrace_append hprefix tailTrace_3201559
  have hstable : (prefixWord ++ tailWord_3201559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201559).length < 2 ^ (prefixWord ++ tailWord_3201559).sum := by decide
  have hdescent : baseEnd_3201559 < baseStart_3201559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201585 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 3, 3]
def baseStart_3201585 : Nat := 118140960795 + 3201585 * 2 ^ 59
def prefixEnd_3201585 : Nat := 4983230072969 + 3 ^ 40 * 3201585 * 2
def baseEnd_3201585 : Nat := 1095967974149974345109123

theorem tailTrace_3201585 : CollatzResearch.WordTrace tailWord_3201585 prefixEnd_3201585 1095967974149974345109123 := by
  unfold tailWord_3201585
  simp only [CollatzResearch.WordTrace]
  refine ⟨116771398106211807031158209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77847598737474538020772139 116771398106211807031158209)
  ·
    refine ⟨87578548579658855273368657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116771398106211807031158209 87578548579658855273368657)
    ·
      refine ⟨65683911434744141455026493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87578548579658855273368657 65683911434744141455026493)
      ·
        refine ⟨24631466788029053045634935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65683911434744141455026493 24631466788029053045634935)
        ·
          refine ⟨36947200182043579568452403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24631466788029053045634935 36947200182043579568452403)
          ·
            refine ⟨55420800273065369352678605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36947200182043579568452403 55420800273065369352678605)
            ·
              refine ⟨20782800102399513507254477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55420800273065369352678605 20782800102399513507254477)
              ·
                refine ⟨7793550038399817565220429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20782800102399513507254477 7793550038399817565220429)
                ·
                  refine ⟨2922581264399931586957661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7793550038399817565220429 2922581264399931586957661)
                  ·
                    refine ⟨1095967974149974345109123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922581264399931586957661 1095967974149974345109123)
                    ·
                      rfl

theorem cell22_3201585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_3201585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201585 prefixEnd_3201585 := by exact prefixLift 3201585
  have htrace : WordTrace (prefixWord ++ tailWord_3201585) baseStart_3201585 baseEnd_3201585 := by
    simpa [prefixWord, tailWord_3201585, baseEnd_3201585] using wordTrace_append hprefix tailTrace_3201585
  have hstable : (prefixWord ++ tailWord_3201585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201585).length < 2 ^ (prefixWord ++ tailWord_3201585).sum := by decide
  have hdescent : baseEnd_3201585 < baseStart_3201585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201604 : List Nat := [2, 3, 5, 1, 1, 1, 1, 8]
def baseStart_3201604 : Nat := 118140960795 + 3201604 * 2 ^ 59
def prefixEnd_3201604 : Nat := 4983230072969 + 3 ^ 40 * 3201604 * 2
def baseEnd_3201604 : Nat := 121774942026473847653785

theorem tailTrace_3201604 : CollatzResearch.WordTrace tailWord_3201604 prefixEnd_3201604 121774942026473847653785 := by
  unfold tailWord_3201604
  simp only [CollatzResearch.WordTrace]
  refine ⟨58386045546571486638049933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77848060728761982184066577 58386045546571486638049933)
  ·
    refine ⟨21894767079964307489268725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58386045546571486638049933 21894767079964307489268725)
    ·
      refine ⟨2052634413746653827118943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21894767079964307489268725 2052634413746653827118943)
      ·
        refine ⟨3078951620619980740678415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052634413746653827118943 3078951620619980740678415)
        ·
          refine ⟨4618427430929971111017623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078951620619980740678415 4618427430929971111017623)
          ·
            refine ⟨6927641146394956666526435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4618427430929971111017623 6927641146394956666526435)
            ·
              refine ⟨10391461719592434999789653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6927641146394956666526435 10391461719592434999789653)
              ·
                refine ⟨121774942026473847653785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10391461719592434999789653 121774942026473847653785)
                ·
                  rfl

theorem cell22_3201604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 8].length) (baseStart_3201604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201604 prefixEnd_3201604 := by exact prefixLift 3201604
  have htrace : WordTrace (prefixWord ++ tailWord_3201604) baseStart_3201604 baseEnd_3201604 := by
    simpa [prefixWord, tailWord_3201604, baseEnd_3201604] using wordTrace_append hprefix tailTrace_3201604
  have hstable : (prefixWord ++ tailWord_3201604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201604).length < 2 ^ (prefixWord ++ tailWord_3201604).sum := by decide
  have hdescent : baseEnd_3201604 < baseStart_3201604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201643 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 6]
def baseStart_3201643 : Nat := 118140960795 + 3201643 * 2 ^ 59
def prefixEnd_3201643 : Nat := 4983230072969 + 3 ^ 40 * 3201643 * 2
def baseEnd_3201643 : Nat := 365329276245093842386315

theorem tailTrace_3201643 : CollatzResearch.WordTrace tailWord_3201643 prefixEnd_3201643 365329276245093842386315 := by
  unfold tailWord_3201643
  simp only [CollatzResearch.WordTrace]
  refine ⟨116773513540001682936769583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77849009026667788624513055 116773513540001682936769583)
  ·
    refine ⟨175160270310002524405154375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116773513540001682936769583 175160270310002524405154375)
    ·
      refine ⟨262740405465003786607731563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175160270310002524405154375 262740405465003786607731563)
      ·
        refine ⟨394110608197505679911597345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262740405465003786607731563 394110608197505679911597345)
        ·
          refine ⟨295582956148129259933698009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394110608197505679911597345 295582956148129259933698009)
          ·
            refine ⟨221687217111096944950273507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295582956148129259933698009 221687217111096944950273507)
            ·
              refine ⟨332530825666645417425410261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221687217111096944950273507 332530825666645417425410261)
              ·
                refine ⟨7793691226562001970908053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 332530825666645417425410261 7793691226562001970908053)
                ·
                  refine ⟨365329276245093842386315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7793691226562001970908053 365329276245093842386315)
                  ·
                    rfl

theorem cell22_3201643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 6].length) (baseStart_3201643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201643 prefixEnd_3201643 := by exact prefixLift 3201643
  have htrace : WordTrace (prefixWord ++ tailWord_3201643) baseStart_3201643 baseEnd_3201643 := by
    simpa [prefixWord, tailWord_3201643, baseEnd_3201643] using wordTrace_append hprefix tailTrace_3201643
  have hstable : (prefixWord ++ tailWord_3201643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201643).length < 2 ^ (prefixWord ++ tailWord_3201643).sum := by decide
  have hdescent : baseEnd_3201643 < baseStart_3201643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201675 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 4, 3]
def baseStart_3201675 : Nat := 118140960795 + 3201675 * 2 ^ 59
def prefixEnd_3201675 : Nat := 4983230072969 + 3 ^ 40 * 3201675 * 2
def baseEnd_3201675 : Nat := 1095998782989244110358847

theorem tailTrace_3201675 : CollatzResearch.WordTrace tailWord_3201675 prefixEnd_3201675 1095998782989244110358847 := by
  unfold tailWord_3201675
  simp only [CollatzResearch.WordTrace]
  refine ⟨116774680675885752401934479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77849787117257168267956319 116774680675885752401934479)
  ·
    refine ⟨175162021013828628602901719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116774680675885752401934479 175162021013828628602901719)
    ·
      refine ⟨262743031520742942904352579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175162021013828628602901719 262743031520742942904352579)
      ·
        refine ⟨394114547281114414356528869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262743031520742942904352579 394114547281114414356528869)
        ·
          refine ⟨73896477615208952691849163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 394114547281114414356528869 73896477615208952691849163)
          ·
            refine ⟨110844716422813429037773745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73896477615208952691849163 110844716422813429037773745)
            ·
              refine ⟨83133537317110071778330309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110844716422813429037773745 83133537317110071778330309)
              ·
                refine ⟨15587538246958138458436933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83133537317110071778330309 15587538246958138458436933)
                ·
                  refine ⟨2922663421304650960956925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15587538246958138458436933 2922663421304650960956925)
                  ·
                    refine ⟨1095998782989244110358847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922663421304650960956925 1095998782989244110358847)
                    ·
                      rfl

theorem cell22_3201675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 3].length) (baseStart_3201675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201675 prefixEnd_3201675 := by exact prefixLift 3201675
  have htrace : WordTrace (prefixWord ++ tailWord_3201675) baseStart_3201675 baseEnd_3201675 := by
    simpa [prefixWord, tailWord_3201675, baseEnd_3201675] using wordTrace_append hprefix tailTrace_3201675
  have hstable : (prefixWord ++ tailWord_3201675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201675).length < 2 ^ (prefixWord ++ tailWord_3201675).sum := by decide
  have hdescent : baseEnd_3201675 < baseStart_3201675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201694 : List Nat := [4, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3201694 : Nat := 118140960795 + 3201694 * 2 ^ 59
def prefixEnd_3201694 : Nat := 4983230072969 + 3 ^ 40 * 3201694 * 2
def baseEnd_3201694 : Nat := 365335095692511464711263

theorem tailTrace_3201694 : CollatzResearch.WordTrace tailWord_3201694 prefixEnd_3201694 365335095692511464711263 := by
  unfold tailWord_3201694
  simp only [CollatzResearch.WordTrace]
  refine ⟨14596921707852114830859517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77850249108544612431250757 14596921707852114830859517)
  ·
    refine ⟨5473845640444543061572319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14596921707852114830859517 5473845640444543061572319)
    ·
      refine ⟨8210768460666814592358479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5473845640444543061572319 8210768460666814592358479)
      ·
        refine ⟨12316152691000221888537719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8210768460666814592358479 12316152691000221888537719)
        ·
          refine ⟨18474229036500332832806579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12316152691000221888537719 18474229036500332832806579)
          ·
            refine ⟨27711343554750499249209869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18474229036500332832806579 27711343554750499249209869)
            ·
              refine ⟨10391753833031437218453701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27711343554750499249209869 10391753833031437218453701)
              ·
                refine ⟨1948453843693394478460069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10391753833031437218453701 1948453843693394478460069)
                ·
                  refine ⟨365335095692511464711263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1948453843693394478460069 365335095692511464711263)
                  ·
                    rfl

theorem cell22_3201694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3201694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201694 prefixEnd_3201694 := by exact prefixLift 3201694
  have htrace : WordTrace (prefixWord ++ tailWord_3201694) baseStart_3201694 baseEnd_3201694 := by
    simpa [prefixWord, tailWord_3201694, baseEnd_3201694] using wordTrace_append hprefix tailTrace_3201694
  have hstable : (prefixWord ++ tailWord_3201694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201694).length < 2 ^ (prefixWord ++ tailWord_3201694).sum := by decide
  have hdescent : baseEnd_3201694 < baseStart_3201694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201709 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_3201709 : Nat := 118140960795 + 3201709 * 2 ^ 59
def prefixEnd_3201709 : Nat := 4983230072969 + 3 ^ 40 * 3201709 * 2
def baseEnd_3201709 : Nat := 1096010421884079355008743

theorem tailTrace_3201709 : CollatzResearch.WordTrace tailWord_3201709 prefixEnd_3201709 1096010421884079355008743 := by
  unfold tailWord_3201709
  simp only [CollatzResearch.WordTrace]
  refine ⟨116775920757762576208672181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77850613838508384139114787 116775920757762576208672181)
  ·
    refine ⟨10947742571040241519563017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116775920757762576208672181 10947742571040241519563017)
    ·
      refine ⟨8210806928280181139672263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10947742571040241519563017 8210806928280181139672263)
      ·
        refine ⟨12316210392420271709508395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8210806928280181139672263 12316210392420271709508395)
        ·
          refine ⟨18474315588630407564262593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12316210392420271709508395 18474315588630407564262593)
          ·
            refine ⟨13855736691472805673196945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18474315588630407564262593 13855736691472805673196945)
            ·
              refine ⟨10391802518604604254897709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13855736691472805673196945 10391802518604604254897709)
              ·
                refine ⟨3896925944476726595586641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10391802518604604254897709 3896925944476726595586641)
                ·
                  refine ⟨2922694458357544946689981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3896925944476726595586641 2922694458357544946689981)
                  ·
                    refine ⟨1096010421884079355008743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922694458357544946689981 1096010421884079355008743)
                    ·
                      rfl

theorem cell22_3201709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_3201709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201709 prefixEnd_3201709 := by exact prefixLift 3201709
  have htrace : WordTrace (prefixWord ++ tailWord_3201709) baseStart_3201709 baseEnd_3201709 := by
    simpa [prefixWord, tailWord_3201709, baseEnd_3201709] using wordTrace_append hprefix tailTrace_3201709
  have hstable : (prefixWord ++ tailWord_3201709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201709).length < 2 ^ (prefixWord ++ tailWord_3201709).sum := by decide
  have hdescent : baseEnd_3201709 < baseStart_3201709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201754 : List Nat := [3, 1, 1, 2, 2, 2, 1, 6, 1, 3]
def baseStart_3201754 : Nat := 118140960795 + 3201754 * 2 ^ 59
def prefixEnd_3201754 : Nat := 4983230072969 + 3 ^ 40 * 3201754 * 2
def baseEnd_3201754 : Nat := 1096025826303714237633605

theorem tailTrace_3201754 : CollatzResearch.WordTrace tailWord_3201754 prefixEnd_3201754 1096025826303714237633605 := by
  unfold tailWord_3201754
  simp only [CollatzResearch.WordTrace]
  refine ⟨29194390510649887223515079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77851708028399699262706877 29194390510649887223515079)
  ·
    refine ⟨43791585765974830835272619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29194390510649887223515079 43791585765974830835272619)
    ·
      refine ⟨65687378648962246252908929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43791585765974830835272619 65687378648962246252908929)
      ·
        refine ⟨49265533986721684689681697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65687378648962246252908929 49265533986721684689681697)
        ·
          refine ⟨36949150490041263517261273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49265533986721684689681697 36949150490041263517261273)
          ·
            refine ⟨27711862867530947637945955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36949150490041263517261273 27711862867530947637945955)
            ·
              refine ⟨41567794301296421456918933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27711862867530947637945955 41567794301296421456918933)
              ·
                refine ⟨1948490357873269755793075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41567794301296421456918933 1948490357873269755793075)
                ·
                  refine ⟨2922735536809904633689613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948490357873269755793075 2922735536809904633689613)
                  ·
                    refine ⟨1096025826303714237633605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922735536809904633689613 1096025826303714237633605)
                    ·
                      rfl

theorem cell22_3201754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_3201754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201754 prefixEnd_3201754 := by exact prefixLift 3201754
  have htrace : WordTrace (prefixWord ++ tailWord_3201754) baseStart_3201754 baseEnd_3201754 := by
    simpa [prefixWord, tailWord_3201754, baseEnd_3201754] using wordTrace_append hprefix tailTrace_3201754
  have hstable : (prefixWord ++ tailWord_3201754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201754).length < 2 ^ (prefixWord ++ tailWord_3201754).sum := by decide
  have hdescent : baseEnd_3201754 < baseStart_3201754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201857 : List Nat := [1, 2, 5, 3, 11]
def baseStart_3201857 : Nat := 118140960795 + 3201857 * 2 ^ 59
def prefixEnd_3201857 : Nat := 4983230072969 + 3 ^ 40 * 3201857 * 2
def baseEnd_3201857 : Nat := 4510539445714634988923

theorem tailTrace_3201857 : CollatzResearch.WordTrace tailWord_3201857 prefixEnd_3201857 4510539445714634988923 := by
  unfold tailWord_3201857
  simp only [CollatzResearch.WordTrace]
  refine ⟨116781318761226397485059825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77854212507484264990039883 116781318761226397485059825)
  ·
    refine ⟨87585989070919798113794869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116781318761226397485059825 87585989070919798113794869)
    ·
      refine ⟨8211186475398731073168269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87585989070919798113794869 8211186475398731073168269)
      ·
        refine ⟨3079194928274524152438101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8211186475398731073168269 3079194928274524152438101)
        ·
          refine ⟨4510539445714634988923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3079194928274524152438101 4510539445714634988923)
          ·
            rfl

theorem cell22_3201857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 11].length) (baseStart_3201857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201857 prefixEnd_3201857 := by exact prefixLift 3201857
  have htrace : WordTrace (prefixWord ++ tailWord_3201857) baseStart_3201857 baseEnd_3201857 := by
    simpa [prefixWord, tailWord_3201857, baseEnd_3201857] using wordTrace_append hprefix tailTrace_3201857
  have hstable : (prefixWord ++ tailWord_3201857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201857).length < 2 ^ (prefixWord ++ tailWord_3201857).sum := by decide
  have hdescent : baseEnd_3201857 < baseStart_3201857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201906 : List Nat := [3, 2, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_3201906 : Nat := 118140960795 + 3201906 * 2 ^ 59
def prefixEnd_3201906 : Nat := 4983230072969 + 3 ^ 40 * 3201906 * 2
def baseEnd_3201906 : Nat := 1096077859010036507833139

theorem tailTrace_3201906 : CollatzResearch.WordTrace tailWord_3201906 prefixEnd_3201906 1096077859010036507833139 := by
  unfold tailWord_3201906
  simp only [CollatzResearch.WordTrace]
  refine ⟨29195776484512219713398393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77855403958699252569062381 29195776484512219713398393)
  ·
    refine ⟨21896832363384164785048795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29195776484512219713398393 21896832363384164785048795)
    ·
      refine ⟨32845248545076247177573193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21896832363384164785048795 32845248545076247177573193)
      ·
        refine ⟨24633936408807185383179895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32845248545076247177573193 24633936408807185383179895)
        ·
          refine ⟨36950904613210778074769843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24633936408807185383179895 36950904613210778074769843)
          ·
            refine ⟨55426356919816167112154765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36950904613210778074769843 55426356919816167112154765)
            ·
              refine ⟨20784883844931062667058037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55426356919816167112154765 20784883844931062667058037)
              ·
                refine ⟨1948582860462287125036691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20784883844931062667058037 1948582860462287125036691)
                ·
                  refine ⟨2922874290693430687555037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948582860462287125036691 2922874290693430687555037)
                  ·
                    refine ⟨1096077859010036507833139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922874290693430687555037 1096077859010036507833139)
                    ·
                      rfl

theorem cell22_3201906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_3201906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201906 prefixEnd_3201906 := by exact prefixLift 3201906
  have htrace : WordTrace (prefixWord ++ tailWord_3201906) baseStart_3201906 baseEnd_3201906 := by
    simpa [prefixWord, tailWord_3201906, baseEnd_3201906] using wordTrace_append hprefix tailTrace_3201906
  have hstable : (prefixWord ++ tailWord_3201906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201906).length < 2 ^ (prefixWord ++ tailWord_3201906).sum := by decide
  have hdescent : baseEnd_3201906 < baseStart_3201906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201917 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_3201917 : Nat := 118140960795 + 3201917 * 2 ^ 59
def prefixEnd_3201917 : Nat := 4983230072969 + 3 ^ 40 * 3201917 * 2
def baseEnd_3201917 : Nat := 1096081624534836145808105

theorem tailTrace_3201917 : CollatzResearch.WordTrace tailWord_3201917 prefixEnd_3201917 1096081624534836145808105 := by
  unfold tailWord_3201917
  simp only [CollatzResearch.WordTrace]
  refine ⟨116783507141009027732244005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77855671427339351821496003 116783507141009027732244005)
  ·
    refine ⟨21896907588939192699795751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116783507141009027732244005 21896907588939192699795751)
    ·
      refine ⟨32845361383408789049693627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21896907588939192699795751 32845361383408789049693627)
      ·
        refine ⟨49268042075113183574540441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32845361383408789049693627 49268042075113183574540441)
        ·
          refine ⟨36951031556334887680905331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49268042075113183574540441 36951031556334887680905331)
          ·
            refine ⟨55426547334502331521357997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36951031556334887680905331 55426547334502331521357997)
            ·
              refine ⟨20784955250438374320509249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55426547334502331521357997 20784955250438374320509249)
              ·
                refine ⟨15588716437828780740381937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20784955250438374320509249 15588716437828780740381937)
                ·
                  refine ⟨11691537328371585555286453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15588716437828780740381937 11691537328371585555286453)
                  ·
                    refine ⟨1096081624534836145808105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11691537328371585555286453 1096081624534836145808105)
                    ·
                      rfl

theorem cell22_3201917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_3201917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201917 prefixEnd_3201917 := by exact prefixLift 3201917
  have htrace : WordTrace (prefixWord ++ tailWord_3201917) baseStart_3201917 baseEnd_3201917 := by
    simpa [prefixWord, tailWord_3201917, baseEnd_3201917] using wordTrace_append hprefix tailTrace_3201917
  have hstable : (prefixWord ++ tailWord_3201917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201917).length < 2 ^ (prefixWord ++ tailWord_3201917).sum := by decide
  have hdescent : baseEnd_3201917 < baseStart_3201917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201932 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_3201932 : Nat := 118140960795 + 3201932 * 2 ^ 59
def prefixEnd_3201932 : Nat := 4983230072969 + 3 ^ 40 * 3201932 * 2
def baseEnd_3201932 : Nat := 1096086759341381106683059

theorem tailTrace_3201932 : CollatzResearch.WordTrace tailWord_3201932 prefixEnd_3201932 1096086759341381106683059 := by
  unfold tailWord_3201932
  simp only [CollatzResearch.WordTrace]
  refine ⟨58392027117977342647020025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77856036157303123529360033 58392027117977342647020025)
  ·
    refine ⟨43794020338483006985265019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58392027117977342647020025 43794020338483006985265019)
    ·
      refine ⟨65691030507724510477897529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43794020338483006985265019 65691030507724510477897529)
      ·
        refine ⟨49268272880793382858423147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65691030507724510477897529 49268272880793382858423147)
        ·
          refine ⟨73902409321190074287634721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49268272880793382858423147 73902409321190074287634721)
          ·
            refine ⟨55426806990892555715726041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73902409321190074287634721 55426806990892555715726041)
            ·
              refine ⟨41570105243169416786794531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55426806990892555715726041 41570105243169416786794531)
              ·
                refine ⟨62355157864754125180191797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41570105243169416786794531 62355157864754125180191797)
                ·
                  refine ⟨5845796049820699235642981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62355157864754125180191797 5845796049820699235642981)
                  ·
                    refine ⟨1096086759341381106683059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5845796049820699235642981 1096086759341381106683059)
                    ·
                      rfl

theorem cell22_3201932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_3201932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201932 prefixEnd_3201932 := by exact prefixLift 3201932
  have htrace : WordTrace (prefixWord ++ tailWord_3201932) baseStart_3201932 baseEnd_3201932 := by
    simpa [prefixWord, tailWord_3201932, baseEnd_3201932] using wordTrace_append hprefix tailTrace_3201932
  have hstable : (prefixWord ++ tailWord_3201932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201932).length < 2 ^ (prefixWord ++ tailWord_3201932).sum := by decide
  have hdescent : baseEnd_3201932 < baseStart_3201932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201974 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3201974 : Nat := 118140960795 + 3201974 * 2 ^ 59
def prefixEnd_3201974 : Nat := 4983230072969 + 3 ^ 40 * 3201974 * 2
def baseEnd_3201974 : Nat := 1096101136799706997132931

theorem tailTrace_3201974 : CollatzResearch.WordTrace tailWord_3201974 prefixEnd_3201974 1096101136799706997132931 := by
  unfold tailWord_3201974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7299099131362657904191811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77857057401201684311379317 7299099131362657904191811)
  ·
    refine ⟨10948648697043986856287717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7299099131362657904191811 10948648697043986856287717)
    ·
      refine ⟨2052871630695747535553947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10948648697043986856287717 2052871630695747535553947)
      ·
        refine ⟨3079307446043621303330921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052871630695747535553947 3079307446043621303330921)
        ·
          refine ⟨2309480584532715977498191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3079307446043621303330921 2309480584532715977498191)
          ·
            refine ⟨3464220876799073966247287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309480584532715977498191 3464220876799073966247287)
            ·
              refine ⟨5196331315198610949370931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464220876799073966247287 5196331315198610949370931)
              ·
                refine ⟨7794496972797916424056397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5196331315198610949370931 7794496972797916424056397)
                ·
                  refine ⟨2922936364799218659021149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7794496972797916424056397 2922936364799218659021149)
                  ·
                    refine ⟨1096101136799706997132931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922936364799218659021149 1096101136799706997132931)
                    ·
                      rfl

theorem cell22_3201974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3201974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201974 prefixEnd_3201974 := by exact prefixLift 3201974
  have htrace : WordTrace (prefixWord ++ tailWord_3201974) baseStart_3201974 baseEnd_3201974 := by
    simpa [prefixWord, tailWord_3201974, baseEnd_3201974] using wordTrace_append hprefix tailTrace_3201974
  have hstable : (prefixWord ++ tailWord_3201974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201974).length < 2 ^ (prefixWord ++ tailWord_3201974).sum := by decide
  have hdescent : baseEnd_3201974 < baseStart_3201974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201981 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 6]
def baseStart_3201981 : Nat := 118140960795 + 3201981 * 2 ^ 59
def prefixEnd_3201981 : Nat := 4983230072969 + 3 ^ 40 * 3201981 * 2
def baseEnd_3201981 : Nat := 365367844347587104069303

theorem tailTrace_3201981 : CollatzResearch.WordTrace tailWord_3201981 prefixEnd_3201981 365367844347587104069303 := by
  unfold tailWord_3201981
  simp only [CollatzResearch.WordTrace]
  refine ⟨116785841412777166662573797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77857227608518111108382531 116785841412777166662573797)
  ·
    refine ⟨21897345264895718749232587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116785841412777166662573797 21897345264895718749232587)
    ·
      refine ⟨32846017897343578123848881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21897345264895718749232587 32846017897343578123848881)
      ·
        refine ⟨24634513423007683592886661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32846017897343578123848881 24634513423007683592886661)
        ·
          refine ⟨4618971266813940673666249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24634513423007683592886661 4618971266813940673666249)
          ·
            refine ⟨3464228450110455505249687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4618971266813940673666249 3464228450110455505249687)
            ·
              refine ⟨5196342675165683257874531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464228450110455505249687 5196342675165683257874531)
              ·
                refine ⟨7794514012748524886811797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5196342675165683257874531 7794514012748524886811797)
                ·
                  refine ⟨365367844347587104069303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7794514012748524886811797 365367844347587104069303)
                  ·
                    rfl

theorem cell22_3201981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_3201981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201981 prefixEnd_3201981 := by exact prefixLift 3201981
  have htrace : WordTrace (prefixWord ++ tailWord_3201981) baseStart_3201981 baseEnd_3201981 := by
    simpa [prefixWord, tailWord_3201981, baseEnd_3201981] using wordTrace_append hprefix tailTrace_3201981
  have hstable : (prefixWord ++ tailWord_3201981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201981).length < 2 ^ (prefixWord ++ tailWord_3201981).sum := by decide
  have hdescent : baseEnd_3201981 < baseStart_3201981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3201996 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 2, 3]
def baseStart_3201996 : Nat := 118140960795 + 3201996 * 2 ^ 59
def prefixEnd_3201996 : Nat := 4983230072969 + 3 ^ 40 * 3201996 * 2
def baseEnd_3201996 : Nat := 1096108667849306273082863

theorem tailTrace_3201996 : CollatzResearch.WordTrace tailWord_3201996 prefixEnd_3201996 1096108667849306273082863 := by
  unfold tailWord_3201996
  simp only [CollatzResearch.WordTrace]
  refine ⟨58393194253861412112184921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77857592338481882816246561 58393194253861412112184921)
  ·
    refine ⟨43794895690396059084138691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58393194253861412112184921 43794895690396059084138691)
    ·
      refine ⟨65692343535594088626208037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43794895690396059084138691 65692343535594088626208037)
      ·
        refine ⟨12317314412923891617414007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65692343535594088626208037 12317314412923891617414007)
        ·
          refine ⟨18475971619385837426121011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12317314412923891617414007 18475971619385837426121011)
          ·
            refine ⟨27713957429078756139181517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18475971619385837426121011 27713957429078756139181517)
            ·
              refine ⟨10392734035904533552193069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27713957429078756139181517 10392734035904533552193069)
              ·
                refine ⟨3897275263464200082072401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10392734035904533552193069 3897275263464200082072401)
                ·
                  refine ⟨2922956447598150061554301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3897275263464200082072401 2922956447598150061554301)
                  ·
                    refine ⟨1096108667849306273082863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922956447598150061554301 1096108667849306273082863)
                    ·
                      rfl

theorem cell22_3201996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_3201996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3201996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3201996 prefixEnd_3201996 := by exact prefixLift 3201996
  have htrace : WordTrace (prefixWord ++ tailWord_3201996) baseStart_3201996 baseEnd_3201996 := by
    simpa [prefixWord, tailWord_3201996, baseEnd_3201996] using wordTrace_append hprefix tailTrace_3201996
  have hstable : (prefixWord ++ tailWord_3201996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3201996).length < 2 ^ (prefixWord ++ tailWord_3201996).sum := by decide
  have hdescent : baseEnd_3201996 < baseStart_3201996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3201996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
