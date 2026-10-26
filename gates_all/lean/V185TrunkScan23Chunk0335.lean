import V185TrunkScan23Chunk0334

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1980091 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 3]
def baseStart_1980091 : Nat := 118140960795 + 1980091 * 2 ^ 59
def prefixEnd_1980091 : Nat := 4983230072969 + 3 ^ 40 * 1980091 * 2
def baseEnd_1980091 : Nat := 1016738422641917618556233

theorem tailTrace_1980091 : CollatzResearch.WordTrace tailWord_1980091 prefixEnd_1980091 1016738422641917618556233 := by
  unfold tailWord_1980091
  simp only [CollatzResearch.WordTrace]
  refine ⟨72219851869475954464612127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48146567912983969643074751 72219851869475954464612127)
  ·
    refine ⟨108329777804213931696918191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72219851869475954464612127 108329777804213931696918191)
    ·
      refine ⟨162494666706320897545377287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108329777804213931696918191 162494666706320897545377287)
      ·
        refine ⟨243742000059481346318065931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162494666706320897545377287 243742000059481346318065931)
        ·
          refine ⟨365613000089222019477098897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243742000059481346318065931 365613000089222019477098897)
          ·
            refine ⟨274209750066916514607824173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365613000089222019477098897 274209750066916514607824173)
            ·
              refine ⟨102828656275093692977934065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274209750066916514607824173 102828656275093692977934065)
              ·
                refine ⟨77121492206320269733450549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102828656275093692977934065 77121492206320269733450549)
                ·
                  refine ⟨7230139894342525287510989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77121492206320269733450549 7230139894342525287510989)
                  ·
                    refine ⟨2711302460378446982816621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7230139894342525287510989 2711302460378446982816621)
                    ·
                      refine ⟨1016738422641917618556233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2711302460378446982816621 1016738422641917618556233)
                      ·
                        rfl

theorem cell23_1980091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 3].length) (baseStart_1980091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980091 prefixEnd_1980091 := by exact prefixLift 1980091
  have htrace : WordTrace (prefixWord ++ tailWord_1980091) baseStart_1980091 baseEnd_1980091 := by
    simpa [prefixWord, tailWord_1980091, baseEnd_1980091] using wordTrace_append hprefix tailTrace_1980091
  have hstable : (prefixWord ++ tailWord_1980091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980091).length < 2 ^ (prefixWord ++ tailWord_1980091).sum := by decide
  have hdescent : baseEnd_1980091 < baseStart_1980091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980102 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1980102 : Nat := 118140960795 + 1980102 * 2 ^ 59
def prefixEnd_1980102 : Nat := 4983230072969 + 3 ^ 40 * 1980102 * 2
def baseEnd_1980102 : Nat := 338914690309705691839561

theorem tailTrace_1980102 : CollatzResearch.WordTrace tailWord_1980102 prefixEnd_1980102 338914690309705691839561 := by
  unfold tailWord_1980102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256882908513628229476955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48146835381624068895508373 2256882908513628229476955)
  ·
    refine ⟨3385324362770442344215433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2256882908513628229476955 3385324362770442344215433)
    ·
      refine ⟨2538993272077831758161575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3385324362770442344215433 2538993272077831758161575)
      ·
        refine ⟨3808489908116747637242363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538993272077831758161575 3808489908116747637242363)
        ·
          refine ⟨5712734862175121455863545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808489908116747637242363 5712734862175121455863545)
          ·
            refine ⟨4284551146631341091897659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5712734862175121455863545 4284551146631341091897659)
            ·
              refine ⟨6426826719947011637846489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284551146631341091897659 6426826719947011637846489)
              ·
                refine ⟨4820120039960258728384867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6426826719947011637846489 4820120039960258728384867)
                ·
                  refine ⟨7230180059940388092577301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820120039960258728384867 7230180059940388092577301)
                  ·
                    refine ⟨338914690309705691839561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7230180059940388092577301 338914690309705691839561)
                    ·
                      rfl

theorem cell23_1980102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1980102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980102 prefixEnd_1980102 := by exact prefixLift 1980102
  have htrace : WordTrace (prefixWord ++ tailWord_1980102) baseStart_1980102 baseEnd_1980102 := by
    simpa [prefixWord, tailWord_1980102, baseEnd_1980102] using wordTrace_append hprefix tailTrace_1980102
  have hstable : (prefixWord ++ tailWord_1980102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980102).length < 2 ^ (prefixWord ++ tailWord_1980102).sum := by decide
  have hdescent : baseEnd_1980102 < baseStart_1980102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980109 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_1980109 : Nat := 118140960795 + 1980109 * 2 ^ 59
def prefixEnd_1980109 : Nat := 4983230072969 + 3 ^ 40 * 1980109 * 2
def baseEnd_1980109 : Nat := 1016747665293698548131151

theorem tailTrace_1980109 : CollatzResearch.WordTrace tailWord_1980109 prefixEnd_1980109 1016747665293698548131151 := by
  unfold tailWord_1980109
  simp only [CollatzResearch.WordTrace]
  refine ⟨72220508383410743538767381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48147005588940495692511587 72220508383410743538767381)
  ·
    refine ⟨3385336330472378603379721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72220508383410743538767381 3385336330472378603379721)
    ·
      refine ⟨2539002247854283952534791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3385336330472378603379721 2539002247854283952534791)
      ·
        refine ⟨3808503371781425928802187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2539002247854283952534791 3808503371781425928802187)
        ·
          refine ⟨5712755057672138893203281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808503371781425928802187 5712755057672138893203281)
          ·
            refine ⟨4284566293254104169902461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5712755057672138893203281 4284566293254104169902461)
            ·
              refine ⟨1606712359970289063713423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4284566293254104169902461 1606712359970289063713423)
              ·
                refine ⟨2410068539955433595570135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606712359970289063713423 2410068539955433595570135)
                ·
                  refine ⟨3615102809933150393355203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410068539955433595570135 3615102809933150393355203)
                  ·
                    refine ⟨5422654214899725590032805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3615102809933150393355203 5422654214899725590032805)
                    ·
                      refine ⟨1016747665293698548131151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5422654214899725590032805 1016747665293698548131151)
                      ·
                        rfl

theorem cell23_1980109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_1980109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980109 prefixEnd_1980109 := by exact prefixLift 1980109
  have htrace : WordTrace (prefixWord ++ tailWord_1980109) baseStart_1980109 baseEnd_1980109 := by
    simpa [prefixWord, tailWord_1980109, baseEnd_1980109] using wordTrace_append hprefix tailTrace_1980109
  have hstable : (prefixWord ++ tailWord_1980109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980109).length < 2 ^ (prefixWord ++ tailWord_1980109).sum := by decide
  have hdescent : baseEnd_1980109 < baseStart_1980109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980151 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_1980151 : Nat := 118140960795 + 1980151 * 2 ^ 59
def prefixEnd_1980151 : Nat := 4983230072969 + 3 ^ 40 * 1980151 * 2
def baseEnd_1980151 : Nat := 1016769231481187383805957

theorem tailTrace_1980151 : CollatzResearch.WordTrace tailWord_1980151 prefixEnd_1980151 1016769231481187383805957 := by
  unfold tailWord_1980151
  simp only [CollatzResearch.WordTrace]
  refine ⟨72222040249258584711796307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48148026832839056474530871 72222040249258584711796307)
  ·
    refine ⟨108333060373887877067694461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72222040249258584711796307 108333060373887877067694461)
    ·
      refine ⟨40624897640207953900385423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108333060373887877067694461 40624897640207953900385423)
      ·
        refine ⟨60937346460311930850578135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40624897640207953900385423 60937346460311930850578135)
        ·
          refine ⟨91406019690467896275867203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60937346460311930850578135 91406019690467896275867203)
          ·
            refine ⟨137109029535701844413800805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91406019690467896275867203 137109029535701844413800805)
            ·
              refine ⟨25707943037944095827587651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137109029535701844413800805 25707943037944095827587651)
              ·
                refine ⟨38561914556916143741381477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25707943037944095827587651 38561914556916143741381477)
                ·
                  refine ⟨7230358979421776951509027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38561914556916143741381477 7230358979421776951509027)
                  ·
                    refine ⟨10845538469132665427263541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7230358979421776951509027 10845538469132665427263541)
                    ·
                      refine ⟨1016769231481187383805957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10845538469132665427263541 1016769231481187383805957)
                      ·
                        rfl

theorem cell23_1980151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_1980151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980151 prefixEnd_1980151 := by exact prefixLift 1980151
  have htrace : WordTrace (prefixWord ++ tailWord_1980151) baseStart_1980151 baseEnd_1980151 := by
    simpa [prefixWord, tailWord_1980151, baseEnd_1980151] using wordTrace_append hprefix tailTrace_1980151
  have hstable : (prefixWord ++ tailWord_1980151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980151).length < 2 ^ (prefixWord ++ tailWord_1980151).sum := by decide
  have hdescent : baseEnd_1980151 < baseStart_1980151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980188 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 7]
def baseStart_1980188 : Nat := 118140960795 + 1980188 * 2 ^ 59
def prefixEnd_1980188 : Nat := 4983230072969 + 3 ^ 40 * 1980188 * 2
def baseEnd_1980188 : Nat := 112976470029489304338143

theorem tailTrace_1980188 : CollatzResearch.WordTrace tailWord_1980188 prefixEnd_1980188 112976470029489304338143 := by
  unfold tailWord_1980188
  simp only [CollatzResearch.WordTrace]
  refine ⟨36111694875062270015446609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48148926500083026687262145 36111694875062270015446609)
  ·
    refine ⟨27083771156296702511584957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36111694875062270015446609 27083771156296702511584957)
    ·
      refine ⟨10156414183611263441844359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27083771156296702511584957 10156414183611263441844359)
      ·
        refine ⟨15234621275416895162766539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156414183611263441844359 15234621275416895162766539)
        ·
          refine ⟨22851931913125342744149809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15234621275416895162766539 22851931913125342744149809)
          ·
            refine ⟨17138948934844007058112357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22851931913125342744149809 17138948934844007058112357)
            ·
              refine ⟨3213552925283251323396067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17138948934844007058112357 3213552925283251323396067)
              ·
                refine ⟨4820329387924876985094101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3213552925283251323396067 4820329387924876985094101)
                ·
                  refine ⟨112976470029489304338143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4820329387924876985094101 112976470029489304338143)
                  ·
                    rfl

theorem cell23_1980188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_1980188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980188 prefixEnd_1980188 := by exact prefixLift 1980188
  have htrace : WordTrace (prefixWord ++ tailWord_1980188) baseStart_1980188 baseEnd_1980188 := by
    simpa [prefixWord, tailWord_1980188, baseEnd_1980188] using wordTrace_append hprefix tailTrace_1980188
  have hstable : (prefixWord ++ tailWord_1980188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980188).length < 2 ^ (prefixWord ++ tailWord_1980188).sum := by decide
  have hdescent : baseEnd_1980188 < baseStart_1980188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980218 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 1, 7]
def baseStart_1980218 : Nat := 118140960795 + 1980218 * 2 ^ 59
def prefixEnd_1980218 : Nat := 4983230072969 + 3 ^ 40 * 1980218 * 2
def baseEnd_1980218 : Nat := 338934544895012873889383

theorem tailTrace_1980218 : CollatzResearch.WordTrace tailWord_1980218 prefixEnd_1980218 338934544895012873889383 := by
  unfold tailWord_1980218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18056120985003963788621327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48149655960010570102990205 18056120985003963788621327)
  ·
    refine ⟨27084181477505945682931991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18056120985003963788621327 27084181477505945682931991)
    ·
      refine ⟨40626272216258918524397987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27084181477505945682931991 40626272216258918524397987)
      ·
        refine ⟨60939408324388377786596981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40626272216258918524397987 60939408324388377786596981)
        ·
          refine ⟨5713069530411410417493467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60939408324388377786596981 5713069530411410417493467)
          ·
            refine ⟨8569604295617115626240201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713069530411410417493467 8569604295617115626240201)
            ·
              refine ⟨6427203221712836719680151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8569604295617115626240201 6427203221712836719680151)
              ·
                refine ⟨9640804832569255079520227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6427203221712836719680151 9640804832569255079520227)
                ·
                  refine ⟨14461207248853882619280341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9640804832569255079520227 14461207248853882619280341)
                  ·
                    refine ⟨338934544895012873889383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14461207248853882619280341 338934544895012873889383)
                    ·
                      rfl

theorem cell23_1980218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_1980218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980218 prefixEnd_1980218 := by exact prefixLift 1980218
  have htrace : WordTrace (prefixWord ++ tailWord_1980218) baseStart_1980218 baseEnd_1980218 := by
    simpa [prefixWord, tailWord_1980218, baseEnd_1980218] using wordTrace_append hprefix tailTrace_1980218
  have hstable : (prefixWord ++ tailWord_1980218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980218).length < 2 ^ (prefixWord ++ tailWord_1980218).sum := by decide
  have hdescent : baseEnd_1980218 < baseStart_1980218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980222 : List Nat := [4, 2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_1980222 : Nat := 118140960795 + 1980222 * 2 ^ 59
def prefixEnd_1980222 : Nat := 4983230072969 + 3 ^ 40 * 1980222 * 2
def baseEnd_1980222 : Nat := 112978409845295178446459

theorem tailTrace_1980222 : CollatzResearch.WordTrace tailWord_1980222 prefixEnd_1980222 112978409845295178446459 := by
  unfold tailWord_1980222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9028078729000170479703865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48149753221334242558420613 9028078729000170479703865)
  ·
    refine ⟨6771059046750127859777899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9028078729000170479703865 6771059046750127859777899)
    ·
      refine ⟨10156588570125191789666849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6771059046750127859777899 10156588570125191789666849)
      ·
        refine ⟨7617441427593893842250137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10156588570125191789666849 7617441427593893842250137)
        ·
          refine ⟨5713081070695420381687603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7617441427593893842250137 5713081070695420381687603)
          ·
            refine ⟨8569621606043130572531405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5713081070695420381687603 8569621606043130572531405)
            ·
              refine ⟨3213608102266173964699277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8569621606043130572531405 3213608102266173964699277)
              ·
                refine ⟨1205103038349815236762229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3213608102266173964699277 1205103038349815236762229)
                ·
                  refine ⟨112978409845295178446459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1205103038349815236762229 112978409845295178446459)
                  ·
                    rfl

theorem cell23_1980222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_1980222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980222 prefixEnd_1980222 := by exact prefixLift 1980222
  have htrace : WordTrace (prefixWord ++ tailWord_1980222) baseStart_1980222 baseEnd_1980222 := by
    simpa [prefixWord, tailWord_1980222, baseEnd_1980222] using wordTrace_append hprefix tailTrace_1980222
  have hstable : (prefixWord ++ tailWord_1980222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980222).length < 2 ^ (prefixWord ++ tailWord_1980222).sum := by decide
  have hdescent : baseEnd_1980222 < baseStart_1980222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980339 : List Nat := [1, 1, 1, 2, 3, 1, 6, 3, 1, 1, 3]
def baseStart_1980339 : Nat := 118140960795 + 1980339 * 2 ^ 59
def prefixEnd_1980339 : Nat := 4983230072969 + 3 ^ 40 * 1980339 * 2
def baseEnd_1980339 : Nat := 1016865765844232648255093

theorem tailTrace_1980339 : CollatzResearch.WordTrace tailWord_1980339 prefixEnd_1980339 1016865765844232648255093 := by
  unfold tailWord_1980339
  simp only [CollatzResearch.WordTrace]
  refine ⟨72228897172577492819640071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48152598115051661879760047 72228897172577492819640071)
  ·
    refine ⟨108343345758866239229460107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72228897172577492819640071 108343345758866239229460107)
    ·
      refine ⟨162515018638299358844190161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108343345758866239229460107 162515018638299358844190161)
      ·
        refine ⟨121886263978724519133142621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162515018638299358844190161 121886263978724519133142621)
        ·
          refine ⟨45707348992021694674928483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121886263978724519133142621 45707348992021694674928483)
          ·
            refine ⟨68561023488032542012392725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45707348992021694674928483 68561023488032542012392725)
            ·
              refine ⟨3213797976001525406830909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68561023488032542012392725 3213797976001525406830909)
              ·
                refine ⟨1205174241000572027561591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3213797976001525406830909 1205174241000572027561591)
                ·
                  refine ⟨1807761361500858041342387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205174241000572027561591 1807761361500858041342387)
                  ·
                    refine ⟨2711642042251287062013581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1807761361500858041342387 2711642042251287062013581)
                    ·
                      refine ⟨1016865765844232648255093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2711642042251287062013581 1016865765844232648255093)
                      ·
                        rfl

theorem cell23_1980339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 1, 1, 3].length) (baseStart_1980339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980339 prefixEnd_1980339 := by exact prefixLift 1980339
  have htrace : WordTrace (prefixWord ++ tailWord_1980339) baseStart_1980339 baseEnd_1980339 := by
    simpa [prefixWord, tailWord_1980339, baseEnd_1980339] using wordTrace_append hprefix tailTrace_1980339
  have hstable : (prefixWord ++ tailWord_1980339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980339).length < 2 ^ (prefixWord ++ tailWord_1980339).sum := by decide
  have hdescent : baseEnd_1980339 < baseStart_1980339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980385 : List Nat := [1, 2, 3, 1, 2, 1, 6, 7]
def baseStart_1980385 : Nat := 118140960795 + 1980385 * 2 ^ 59
def prefixEnd_1980385 : Nat := 4983230072969 + 3 ^ 40 * 1980385 * 2
def baseEnd_1980385 : Nat := 37662569850160721047403

theorem tailTrace_1980385 : CollatzResearch.WordTrace tailWord_1980385 prefixEnd_1980385 37662569850160721047403 := by
  unfold tailWord_1980385
  simp only [CollatzResearch.WordTrace]
  refine ⟨72230574930410842675814609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48153716620273895117209739 72230574930410842675814609)
  ·
    refine ⟨54172931197808132006860957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72230574930410842675814609 54172931197808132006860957)
    ·
      refine ⟨20314849199178049502572859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54172931197808132006860957 20314849199178049502572859)
      ·
        refine ⟨30472273798767074253859289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20314849199178049502572859 30472273798767074253859289)
        ·
          refine ⟨22854205349075305690394467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30472273798767074253859289 22854205349075305690394467)
          ·
            refine ⟨34281308023612958535591701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22854205349075305690394467 34281308023612958535591701)
            ·
              refine ⟨1606936313606857431355861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34281308023612958535591701 1606936313606857431355861)
              ·
                refine ⟨37662569850160721047403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1606936313606857431355861 37662569850160721047403)
                ·
                  rfl

theorem cell23_1980385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 7].length) (baseStart_1980385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980385 prefixEnd_1980385 := by exact prefixLift 1980385
  have htrace : WordTrace (prefixWord ++ tailWord_1980385) baseStart_1980385 baseEnd_1980385 := by
    simpa [prefixWord, tailWord_1980385, baseEnd_1980385] using wordTrace_append hprefix tailTrace_1980385
  have hstable : (prefixWord ++ tailWord_1980385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980385).length < 2 ^ (prefixWord ++ tailWord_1980385).sum := by decide
  have hdescent : baseEnd_1980385 < baseStart_1980385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980395 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 3]
def baseStart_1980395 : Nat := 118140960795 + 1980395 * 2 ^ 59
def prefixEnd_1980395 : Nat := 4983230072969 + 3 ^ 40 * 1980395 * 2
def baseEnd_1980395 : Nat := 1016894520760884429154835

theorem tailTrace_1980395 : CollatzResearch.WordTrace tailWord_1980395 prefixEnd_1980395 1016894520760884429154835 := by
  unfold tailWord_1980395
  simp only [CollatzResearch.WordTrace]
  refine ⟨72230939660374614383678639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48153959773583076255785759 72230939660374614383678639)
  ·
    refine ⟨108346409490561921575517959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72230939660374614383678639 108346409490561921575517959)
    ·
      refine ⟨162519614235842882363276939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108346409490561921575517959 162519614235842882363276939)
      ·
        refine ⟨243779421353764323544915409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162519614235842882363276939 243779421353764323544915409)
        ·
          refine ⟨182834566015323242658686557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243779421353764323544915409 182834566015323242658686557)
          ·
            refine ⟨68562962255746215997007459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182834566015323242658686557 68562962255746215997007459)
            ·
              refine ⟨102844443383619323995511189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68562962255746215997007459 102844443383619323995511189)
              ·
                refine ⟨4820833283607155812289587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 102844443383619323995511189 4820833283607155812289587)
                ·
                  refine ⟨7231249925410733718434381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4820833283607155812289587 7231249925410733718434381)
                  ·
                    refine ⟨2711718722029025144412893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7231249925410733718434381 2711718722029025144412893)
                    ·
                      refine ⟨1016894520760884429154835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2711718722029025144412893 1016894520760884429154835)
                      ·
                        rfl

theorem cell23_1980395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 3].length) (baseStart_1980395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980395 prefixEnd_1980395 := by exact prefixLift 1980395
  have htrace : WordTrace (prefixWord ++ tailWord_1980395) baseStart_1980395 baseEnd_1980395 := by
    simpa [prefixWord, tailWord_1980395, baseEnd_1980395] using wordTrace_append hprefix tailTrace_1980395
  have hstable : (prefixWord ++ tailWord_1980395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980395).length < 2 ^ (prefixWord ++ tailWord_1980395).sum := by decide
  have hdescent : baseEnd_1980395 < baseStart_1980395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980412 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_1980412 : Nat := 118140960795 + 1980412 * 2 ^ 59
def prefixEnd_1980412 : Nat := 4983230072969 + 3 ^ 40 * 1980412 * 2
def baseEnd_1980412 : Nat := 1016903249932010862642257

theorem tailTrace_1980412 : CollatzResearch.WordTrace tailWord_1980412 prefixEnd_1980412 1016903249932010862642257 := by
  unfold tailWord_1980412
  simp only [CollatzResearch.WordTrace]
  refine ⟨36115779850656513143523745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48154373134208684191364993 36115779850656513143523745)
  ·
    refine ⟨27086834887992384857642809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36115779850656513143523745 27086834887992384857642809)
    ·
      refine ⟨20315126165994288643232107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27086834887992384857642809 20315126165994288643232107)
      ·
        refine ⟨30472689248991432964848161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20315126165994288643232107 30472689248991432964848161)
        ·
          refine ⟨22854516936743574723636121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30472689248991432964848161 22854516936743574723636121)
          ·
            refine ⟨17140887702557681042727091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22854516936743574723636121 17140887702557681042727091)
            ·
              refine ⟨25711331553836521564090637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17140887702557681042727091 25711331553836521564090637)
              ·
                refine ⟨9641749332688695586533989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25711331553836521564090637 9641749332688695586533989)
                ·
                  refine ⟨1807827999879130422475123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9641749332688695586533989 1807827999879130422475123)
                  ·
                    refine ⟨2711741999818695633712685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1807827999879130422475123 2711741999818695633712685)
                    ·
                      refine ⟨1016903249932010862642257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2711741999818695633712685 1016903249932010862642257)
                      ·
                        rfl

theorem cell23_1980412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_1980412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980412 prefixEnd_1980412 := by exact prefixLift 1980412
  have htrace : WordTrace (prefixWord ++ tailWord_1980412) baseStart_1980412 baseEnd_1980412 := by
    simpa [prefixWord, tailWord_1980412, baseEnd_1980412] using wordTrace_append hprefix tailTrace_1980412
  have hstable : (prefixWord ++ tailWord_1980412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980412).length < 2 ^ (prefixWord ++ tailWord_1980412).sum := by decide
  have hdescent : baseEnd_1980412 < baseStart_1980412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980469 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_1980469 : Nat := 118140960795 + 1980469 * 2 ^ 59
def prefixEnd_1980469 : Nat := 4983230072969 + 3 ^ 40 * 1980469 * 2
def baseEnd_1980469 : Nat := 1016932518329317139629495

theorem tailTrace_1980469 : CollatzResearch.WordTrace tailWord_1980469 prefixEnd_1980469 1016932518329317139629495 := by
  unfold tailWord_1980469
  simp only [CollatzResearch.WordTrace]
  refine ⟨72233638662106525021872461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48155759108071016681248307 72233638662106525021872461)
  ·
    refine ⟨27087614498289946883202173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72233638662106525021872461 27087614498289946883202173)
    ·
      refine ⟨10157855436858730081200815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27087614498289946883202173 10157855436858730081200815)
      ·
        refine ⟨15236783155288095121801223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10157855436858730081200815 15236783155288095121801223)
        ·
          refine ⟨22855174732932142682701835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15236783155288095121801223 22855174732932142682701835)
          ·
            refine ⟨34282762099398214024052753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22855174732932142682701835 34282762099398214024052753)
            ·
              refine ⟨25712071574548660518039565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34282762099398214024052753 25712071574548660518039565)
              ·
                refine ⟨9642026840455747694264837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25712071574548660518039565 9642026840455747694264837)
                ·
                  refine ⟨1807880032585452692674657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9642026840455747694264837 1807880032585452692674657)
                  ·
                    refine ⟨1355910024439089519505993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1807880032585452692674657 1355910024439089519505993)
                    ·
                      refine ⟨1016932518329317139629495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1355910024439089519505993 1016932518329317139629495)
                      ·
                        rfl

theorem cell23_1980469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_1980469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980469 prefixEnd_1980469 := by exact prefixLift 1980469
  have htrace : WordTrace (prefixWord ++ tailWord_1980469) baseStart_1980469 baseEnd_1980469 := by
    simpa [prefixWord, tailWord_1980469, baseEnd_1980469] using wordTrace_append hprefix tailTrace_1980469
  have hstable : (prefixWord ++ tailWord_1980469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980469).length < 2 ^ (prefixWord ++ tailWord_1980469).sum := by decide
  have hdescent : baseEnd_1980469 < baseStart_1980469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980505 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 1, 7]
def baseStart_1980505 : Nat := 118140960795 + 1980505 * 2 ^ 59
def prefixEnd_1980505 : Nat := 4983230072969 + 3 ^ 40 * 1980505 * 2
def baseEnd_1980505 : Nat := 338983667877626332926443

theorem tailTrace_1980505 : CollatzResearch.WordTrace tailWord_1980505 prefixEnd_1980505 338983667877626332926443 := by
  unfold tailWord_1980505
  simp only [CollatzResearch.WordTrace]
  refine ⟨72234951689976103170182969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48156634459984068780121979 72234951689976103170182969)
  ·
    refine ⟨54176213767482077377637227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72234951689976103170182969 54176213767482077377637227)
    ·
      refine ⟨81264320651223116066455841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54176213767482077377637227 81264320651223116066455841)
      ·
        refine ⟨60948240488417337049841881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81264320651223116066455841 60948240488417337049841881)
        ·
          refine ⟨45711180366313002787381411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60948240488417337049841881 45711180366313002787381411)
          ·
            refine ⟨68566770549469504181072117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45711180366313002787381411 68566770549469504181072117)
            ·
              refine ⟨6428134739012766016975511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68566770549469504181072117 6428134739012766016975511)
              ·
                refine ⟨9642202108519149025463267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6428134739012766016975511 9642202108519149025463267)
                ·
                  refine ⟨14463303162778723538194901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9642202108519149025463267 14463303162778723538194901)
                  ·
                    refine ⟨338983667877626332926443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14463303162778723538194901 338983667877626332926443)
                    ·
                      rfl

theorem cell23_1980505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_1980505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980505 prefixEnd_1980505 := by exact prefixLift 1980505
  have htrace : WordTrace (prefixWord ++ tailWord_1980505) baseStart_1980505 baseEnd_1980505 := by
    simpa [prefixWord, tailWord_1980505, baseEnd_1980505] using wordTrace_append hprefix tailTrace_1980505
  have hstable : (prefixWord ++ tailWord_1980505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980505).length < 2 ^ (prefixWord ++ tailWord_1980505).sum := by decide
  have hdescent : baseEnd_1980505 < baseStart_1980505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980515 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1980515 : Nat := 118140960795 + 1980515 * 2 ^ 59
def prefixEnd_1980515 : Nat := 4983230072969 + 3 ^ 40 * 1980515 * 2
def baseEnd_1980515 : Nat := 1016956138439423959654283

theorem tailTrace_1980515 : CollatzResearch.WordTrace tailWord_1980515 prefixEnd_1980515 1016956138439423959654283 := by
  unfold tailWord_1980515
  simp only [CollatzResearch.WordTrace]
  refine ⟨72235316419939874878046999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48156877613293249918697999 72235316419939874878046999)
  ·
    refine ⟨108352974629909812317070499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72235316419939874878046999 108352974629909812317070499)
    ·
      refine ⟨162529461944864718475605749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108352974629909812317070499 162529461944864718475605749)
      ·
        refine ⟨15237137057331067357088039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162529461944864718475605749 15237137057331067357088039)
        ·
          refine ⟨22855705585996601035632059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15237137057331067357088039 22855705585996601035632059)
          ·
            refine ⟨34283558378994901553448089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22855705585996601035632059 34283558378994901553448089)
            ·
              refine ⟨25712668784246176165086067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34283558378994901553448089 25712668784246176165086067)
              ·
                refine ⟨38569003176369264247629101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25712668784246176165086067 38569003176369264247629101)
                ·
                  refine ⟨14463376191138474092860913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38569003176369264247629101 14463376191138474092860913)
                  ·
                    refine ⟨10847532143353855569645685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14463376191138474092860913 10847532143353855569645685)
                    ·
                      refine ⟨1016956138439423959654283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10847532143353855569645685 1016956138439423959654283)
                      ·
                        rfl

theorem cell23_1980515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1980515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980515 prefixEnd_1980515 := by exact prefixLift 1980515
  have htrace : WordTrace (prefixWord ++ tailWord_1980515) baseStart_1980515 baseEnd_1980515 := by
    simpa [prefixWord, tailWord_1980515, baseEnd_1980515] using wordTrace_append hprefix tailTrace_1980515
  have hstable : (prefixWord ++ tailWord_1980515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980515).length < 2 ^ (prefixWord ++ tailWord_1980515).sum := by decide
  have hdescent : baseEnd_1980515 < baseStart_1980515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980565 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 10]
def baseStart_1980565 : Nat := 118140960795 + 1980565 * 2 ^ 59
def prefixEnd_1980565 : Nat := 4983230072969 + 3 ^ 40 * 1980565 * 2
def baseEnd_1980565 : Nat := 112997979163572084892117

theorem tailTrace_1980565 : CollatzResearch.WordTrace tailWord_1980565 prefixEnd_1980565 112997979163572084892117 := by
  unfold tailWord_1980565
  simp only [CollatzResearch.WordTrace]
  refine ⟨72237140069758733417367149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48158093379839155611578099 72237140069758733417367149)
  ·
    refine ⟨27088927526159525031512681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72237140069758733417367149 27088927526159525031512681)
    ·
      refine ⟨20316695644619643773634511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27088927526159525031512681 20316695644619643773634511)
      ·
        refine ⟨30475043466929465660451767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20316695644619643773634511 30475043466929465660451767)
        ·
          refine ⟨45712565200394198490677651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30475043466929465660451767 45712565200394198490677651)
          ·
            refine ⟨68568847800591297736016477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45712565200394198490677651 68568847800591297736016477)
            ·
              refine ⟨25713317925221736651006179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68568847800591297736016477 25713317925221736651006179)
              ·
                refine ⟨38569976887832604976509269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25713317925221736651006179 38569976887832604976509269)
                ·
                  refine ⟨112997979163572084892117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 38569976887832604976509269 112997979163572084892117)
                  ·
                    rfl

theorem cell23_1980565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_1980565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980565 prefixEnd_1980565 := by exact prefixLift 1980565
  have htrace : WordTrace (prefixWord ++ tailWord_1980565) baseStart_1980565 baseEnd_1980565 := by
    simpa [prefixWord, tailWord_1980565, baseEnd_1980565] using wordTrace_append hprefix tailTrace_1980565
  have hstable : (prefixWord ++ tailWord_1980565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980565).length < 2 ^ (prefixWord ++ tailWord_1980565).sum := by decide
  have hdescent : baseEnd_1980565 < baseStart_1980565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980595 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 2, 9]
def baseStart_1980595 : Nat := 118140960795 + 1980595 * 2 ^ 59
def prefixEnd_1980595 : Nat := 4983230072969 + 3 ^ 40 * 1980595 * 2
def baseEnd_1980595 : Nat := 338999072297261215551305

theorem tailTrace_1980595 : CollatzResearch.WordTrace tailWord_1980595 prefixEnd_1980595 338999072297261215551305 := by
  unfold tailWord_1980595
  simp only [CollatzResearch.WordTrace]
  refine ⟨72238234259650048540959239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48158822839766699027306159 72238234259650048540959239)
  ·
    refine ⟨108357351389475072811438859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72238234259650048540959239 108357351389475072811438859)
    ·
      refine ⟨162536027084212609217158289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108357351389475072811438859 162536027084212609217158289)
      ·
        refine ⟨121902020313159456912868717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162536027084212609217158289 121902020313159456912868717)
        ·
          refine ⟨45713257617434796342325769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121902020313159456912868717 45713257617434796342325769)
          ·
            refine ⟨34284943213076097256744327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45713257617434796342325769 34284943213076097256744327)
            ·
              refine ⟨51427414819614145885116491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34284943213076097256744327 51427414819614145885116491)
              ·
                refine ⟨77141122229421218827674737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51427414819614145885116491 77141122229421218827674737)
                ·
                  refine ⟨57855841672065914120756053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77141122229421218827674737 57855841672065914120756053)
                  ·
                    refine ⟨338999072297261215551305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 57855841672065914120756053 338999072297261215551305)
                    ·
                      rfl

theorem cell23_1980595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 9].length) (baseStart_1980595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980595 prefixEnd_1980595 := by exact prefixLift 1980595
  have htrace : WordTrace (prefixWord ++ tailWord_1980595) baseStart_1980595 baseEnd_1980595 := by
    simpa [prefixWord, tailWord_1980595, baseEnd_1980595] using wordTrace_append hprefix tailTrace_1980595
  have hstable : (prefixWord ++ tailWord_1980595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980595).length < 2 ^ (prefixWord ++ tailWord_1980595).sum := by decide
  have hdescent : baseEnd_1980595 < baseStart_1980595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980599 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 6]
def baseStart_1980599 : Nat := 118140960795 + 1980599 * 2 ^ 59
def prefixEnd_1980599 : Nat := 4983230072969 + 3 ^ 40 * 1980599 * 2
def baseEnd_1980599 : Nat := 112999918979377959000433

theorem tailTrace_1980599 : CollatzResearch.WordTrace tailWord_1980599 prefixEnd_1980599 112999918979377959000433 := by
  unfold tailWord_1980599
  simp only [CollatzResearch.WordTrace]
  refine ⟨72238380151635557224104851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48158920101090371482736567 72238380151635557224104851)
  ·
    refine ⟨108357570227453335836157277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72238380151635557224104851 108357570227453335836157277)
    ·
      refine ⟨40634088835295000938558979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108357570227453335836157277 40634088835295000938558979)
      ·
        refine ⟨60951133252942501407838469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40634088835295000938558979 60951133252942501407838469)
        ·
          refine ⟨11428337484926719013969713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60951133252942501407838469 11428337484926719013969713)
          ·
            refine ⟨8571253113695039260477285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11428337484926719013969713 8571253113695039260477285)
            ·
              refine ⟨1607109958817819861339491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8571253113695039260477285 1607109958817819861339491)
              ·
                refine ⟨2410664938226729792009237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607109958817819861339491 2410664938226729792009237)
                ·
                  refine ⟨112999918979377959000433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2410664938226729792009237 112999918979377959000433)
                  ·
                    rfl

theorem cell23_1980599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 6].length) (baseStart_1980599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980599 prefixEnd_1980599 := by exact prefixLift 1980599
  have htrace : WordTrace (prefixWord ++ tailWord_1980599) baseStart_1980599 baseEnd_1980599 := by
    simpa [prefixWord, tailWord_1980599, baseEnd_1980599] using wordTrace_append hprefix tailTrace_1980599
  have hstable : (prefixWord ++ tailWord_1980599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980599).length < 2 ^ (prefixWord ++ tailWord_1980599).sum := by decide
  have hdescent : baseEnd_1980599 < baseStart_1980599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980652 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_1980652 : Nat := 118140960795 + 1980652 * 2 ^ 59
def prefixEnd_1980652 : Nat := 4983230072969 + 3 ^ 40 * 1980652 * 2
def baseEnd_1980652 : Nat := 1017026485289089923641153

theorem tailTrace_1980652 : CollatzResearch.WordTrace tailWord_1980652 prefixEnd_1980652 1017026485289089923641153 := by
  unfold tailWord_1980652
  simp only [CollatzResearch.WordTrace]
  refine ⟨36120156610221773637892105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48160208813629031517189473 36120156610221773637892105)
  ·
    refine ⟨27090117457666330228419079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36120156610221773637892105 27090117457666330228419079)
    ·
      refine ⟨40635176186499495342628619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27090117457666330228419079 40635176186499495342628619)
      ·
        refine ⟨60952764279749243013942929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40635176186499495342628619 60952764279749243013942929)
        ·
          refine ⟨45714573209811932260457197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60952764279749243013942929 45714573209811932260457197)
          ·
            refine ⟨17142964953679474597671449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45714573209811932260457197 17142964953679474597671449)
            ·
              refine ⟨12857223715259605948253587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17142964953679474597671449 12857223715259605948253587)
              ·
                refine ⟨19285835572889408922380381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12857223715259605948253587 19285835572889408922380381)
                ·
                  refine ⟨7232188339833528345892643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19285835572889408922380381 7232188339833528345892643)
                  ·
                    refine ⟨10848282509750292518838965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7232188339833528345892643 10848282509750292518838965)
                    ·
                      refine ⟨1017026485289089923641153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10848282509750292518838965 1017026485289089923641153)
                      ·
                        rfl

theorem cell23_1980652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_1980652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980652 prefixEnd_1980652 := by exact prefixLift 1980652
  have htrace : WordTrace (prefixWord ++ tailWord_1980652) baseStart_1980652 baseEnd_1980652 := by
    simpa [prefixWord, tailWord_1980652, baseEnd_1980652] using wordTrace_append hprefix tailTrace_1980652
  have hstable : (prefixWord ++ tailWord_1980652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980652).length < 2 ^ (prefixWord ++ tailWord_1980652).sum := by decide
  have hdescent : baseEnd_1980652 < baseStart_1980652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980659 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 2, 4]
def baseStart_1980659 : Nat := 118140960795 + 1980659 * 2 ^ 59
def prefixEnd_1980659 : Nat := 4983230072969 + 3 ^ 40 * 1980659 * 2
def baseEnd_1980659 : Nat := 339010026551223798751207

theorem tailTrace_1980659 : CollatzResearch.WordTrace tailWord_1980659 prefixEnd_1980659 339010026551223798751207 := by
  unfold tailWord_1980659
  simp only [CollatzResearch.WordTrace]
  refine ⟨72240568531418187471289031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48160379020945458314192687 72240568531418187471289031)
  ·
    refine ⟨108360852797127281206933547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72240568531418187471289031 108360852797127281206933547)
    ·
      refine ⟨162541279195690921810400321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108360852797127281206933547 162541279195690921810400321)
      ·
        refine ⟨121905959396768191357800241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162541279195690921810400321 121905959396768191357800241)
        ·
          refine ⟨91429469547576143518350181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121905959396768191357800241 91429469547576143518350181)
          ·
            refine ⟨17143025540170526909690659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91429469547576143518350181 17143025540170526909690659)
            ·
              refine ⟨25714538310255790364535989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17143025540170526909690659 25714538310255790364535989)
              ·
                refine ⟨2410737966586480346675249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25714538310255790364535989 2410737966586480346675249)
                ·
                  refine ⟨1808053474939860260006437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2410737966586480346675249 1808053474939860260006437)
                  ·
                    refine ⟨339010026551223798751207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1808053474939860260006437 339010026551223798751207)
                    ·
                      rfl

theorem cell23_1980659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 4].length) (baseStart_1980659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980659 prefixEnd_1980659 := by exact prefixLift 1980659
  have htrace : WordTrace (prefixWord ++ tailWord_1980659) baseStart_1980659 baseEnd_1980659 := by
    simpa [prefixWord, tailWord_1980659, baseEnd_1980659] using wordTrace_append hprefix tailTrace_1980659
  have hstable : (prefixWord ++ tailWord_1980659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980659).length < 2 ^ (prefixWord ++ tailWord_1980659).sum := by decide
  have hdescent : baseEnd_1980659 < baseStart_1980659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980666 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2]
def baseStart_1980666 : Nat := 118140960795 + 1980666 * 2 ^ 59
def prefixEnd_1980666 : Nat := 4983230072969 + 3 ^ 40 * 1980666 * 2
def baseEnd_1980666 : Nat := 1017033674018252868866089

theorem tailTrace_1980666 : CollatzResearch.WordTrace tailWord_1980666 prefixEnd_1980666 1017033674018252868866089 := by
  unfold tailWord_1980666
  simp only [CollatzResearch.WordTrace]
  refine ⟨18060205960598206916698463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48160549228261885111195901 18060205960598206916698463)
  ·
    refine ⟨27090308940897310375047695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18060205960598206916698463 27090308940897310375047695)
    ·
      refine ⟨40635463411345965562571543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27090308940897310375047695 40635463411345965562571543)
      ·
        refine ⟨60953195117018948343857315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40635463411345965562571543 60953195117018948343857315)
        ·
          refine ⟨91429792675528422515785973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60953195117018948343857315 91429792675528422515785973)
          ·
            refine ⟨8571543063330789610854935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91429792675528422515785973 8571543063330789610854935)
            ·
              refine ⟨12857314594996184416282403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8571543063330789610854935 12857314594996184416282403)
              ·
                refine ⟨19285971892494276624423605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12857314594996184416282403 19285971892494276624423605)
                ·
                  refine ⟨1808059864921338433539713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19285971892494276624423605 1808059864921338433539713)
                  ·
                    refine ⟨1356044898691003825154785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1808059864921338433539713 1356044898691003825154785)
                    ·
                      refine ⟨1017033674018252868866089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356044898691003825154785 1017033674018252868866089)
                      ·
                        rfl

theorem cell23_1980666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 5, 2, 2].length) (baseStart_1980666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980666 prefixEnd_1980666 := by exact prefixLift 1980666
  have htrace : WordTrace (prefixWord ++ tailWord_1980666) baseStart_1980666 baseEnd_1980666 := by
    simpa [prefixWord, tailWord_1980666, baseEnd_1980666] using wordTrace_append hprefix tailTrace_1980666
  have hstable : (prefixWord ++ tailWord_1980666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980666).length < 2 ^ (prefixWord ++ tailWord_1980666).sum := by decide
  have hdescent : baseEnd_1980666 < baseStart_1980666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980686 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1980686 : Nat := 118140960795 + 1980686 * 2 ^ 59
def prefixEnd_1980686 : Nat := 4983230072969 + 3 ^ 40 * 1980686 * 2
def baseEnd_1980686 : Nat := 1017043943631342790615997

theorem tailTrace_1980686 : CollatzResearch.WordTrace tailWord_1980686 prefixEnd_1980686 1017043943631342790615997 := by
  unfold tailWord_1980686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030194162790046385315239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48161035534880247388347941 9030194162790046385315239)
  ·
    refine ⟨13545291244185069577972859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9030194162790046385315239 13545291244185069577972859)
    ·
      refine ⟨20317936866277604366959289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13545291244185069577972859 20317936866277604366959289)
      ·
        refine ⟨15238452649708203275219467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20317936866277604366959289 15238452649708203275219467)
        ·
          refine ⟨22857678974562304912829201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15238452649708203275219467 22857678974562304912829201)
          ·
            refine ⟨17143259230921728684621901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22857678974562304912829201 17143259230921728684621901)
            ·
              refine ⟨6428722211595648256733213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17143259230921728684621901 6428722211595648256733213)
              ·
                refine ⟨2410770829348368096274955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6428722211595648256733213 2410770829348368096274955)
                ·
                  refine ⟨3616156244022552144412433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410770829348368096274955 3616156244022552144412433)
                  ·
                    refine ⟨2712117183016914108309325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3616156244022552144412433 2712117183016914108309325)
                    ·
                      refine ⟨1017043943631342790615997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2712117183016914108309325 1017043943631342790615997)
                      ·
                        rfl

theorem cell23_1980686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1980686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980686 prefixEnd_1980686 := by exact prefixLift 1980686
  have htrace : WordTrace (prefixWord ++ tailWord_1980686) baseStart_1980686 baseEnd_1980686 := by
    simpa [prefixWord, tailWord_1980686, baseEnd_1980686] using wordTrace_append hprefix tailTrace_1980686
  have hstable : (prefixWord ++ tailWord_1980686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980686).length < 2 ^ (prefixWord ++ tailWord_1980686).sum := by decide
  have hdescent : baseEnd_1980686 < baseStart_1980686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980716 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 3]
def baseStart_1980716 : Nat := 118140960795 + 1980716 * 2 ^ 59
def prefixEnd_1980716 : Nat := 4983230072969 + 3 ^ 40 * 1980716 * 2
def baseEnd_1980716 : Nat := 1017059348050977673240859

theorem tailTrace_1980716 : CollatzResearch.WordTrace tailWord_1980716 prefixEnd_1980716 1017059348050977673240859 := by
  unfold tailWord_1980716
  simp only [CollatzResearch.WordTrace]
  refine ⟨36121323746105843103057001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48161764994807790804076001 36121323746105843103057001)
  ·
    refine ⟨27090992809579382327292751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36121323746105843103057001 27090992809579382327292751)
    ·
      refine ⟨40636489214369073490939127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27090992809579382327292751 40636489214369073490939127)
      ·
        refine ⟨60954733821553610236408691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40636489214369073490939127 60954733821553610236408691)
        ·
          refine ⟨91432100732330415354613037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60954733821553610236408691 91432100732330415354613037)
          ·
            refine ⟨34287037774623905757979889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91432100732330415354613037 34287037774623905757979889)
            ·
              refine ⟨25715278330967929318484917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34287037774623905757979889 25715278330967929318484917)
              ·
                refine ⟨2410807343528243373607961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25715278330967929318484917 2410807343528243373607961)
                ·
                  refine ⟨1808105507646182530205971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2410807343528243373607961 1808105507646182530205971)
                  ·
                    refine ⟨2712158261469273795308957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1808105507646182530205971 2712158261469273795308957)
                    ·
                      refine ⟨1017059348050977673240859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2712158261469273795308957 1017059348050977673240859)
                      ·
                        rfl

theorem cell23_1980716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_1980716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980716 prefixEnd_1980716 := by exact prefixLift 1980716
  have htrace : WordTrace (prefixWord ++ tailWord_1980716) baseStart_1980716 baseEnd_1980716 := by
    simpa [prefixWord, tailWord_1980716, baseEnd_1980716] using wordTrace_append hprefix tailTrace_1980716
  have hstable : (prefixWord ++ tailWord_1980716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980716).length < 2 ^ (prefixWord ++ tailWord_1980716).sum := by decide
  have hdescent : baseEnd_1980716 < baseStart_1980716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980729 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1980729 : Nat := 118140960795 + 1980729 * 2 ^ 59
def prefixEnd_1980729 : Nat := 4983230072969 + 3 ^ 40 * 1980729 * 2
def baseEnd_1980729 : Nat := 1017066023299486122378299

theorem tailTrace_1980729 : CollatzResearch.WordTrace tailWord_1980729 prefixEnd_1980729 1017066023299486122378299 := by
  unfold tailWord_1980729
  simp only [CollatzResearch.WordTrace]
  refine ⟨72243121641164589426337241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48162081094109726284224827 72243121641164589426337241)
  ·
    refine ⟨54182341230873442069752931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72243121641164589426337241 54182341230873442069752931)
    ·
      refine ⟨81273511846310163104629397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54182341230873442069752931 81273511846310163104629397)
      ·
        refine ⟨3809695867795788895529503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81273511846310163104629397 3809695867795788895529503)
        ·
          refine ⟨5714543801693683343294255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3809695867795788895529503 5714543801693683343294255)
          ·
            refine ⟨8571815702540525014941383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5714543801693683343294255 8571815702540525014941383)
            ·
              refine ⟨12857723553810787522412075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8571815702540525014941383 12857723553810787522412075)
              ·
                refine ⟨19286585330716181283618113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12857723553810787522412075 19286585330716181283618113)
                ·
                  refine ⟨14464938998037135962713585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19286585330716181283618113 14464938998037135962713585)
                  ·
                    refine ⟨10848704248527851972035189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14464938998037135962713585 10848704248527851972035189)
                    ·
                      refine ⟨1017066023299486122378299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10848704248527851972035189 1017066023299486122378299)
                      ·
                        rfl

theorem cell23_1980729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1980729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980729 prefixEnd_1980729 := by exact prefixLift 1980729
  have htrace : WordTrace (prefixWord ++ tailWord_1980729) baseStart_1980729 baseEnd_1980729 := by
    simpa [prefixWord, tailWord_1980729, baseEnd_1980729] using wordTrace_append hprefix tailTrace_1980729
  have hstable : (prefixWord ++ tailWord_1980729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980729).length < 2 ^ (prefixWord ++ tailWord_1980729).sum := by decide
  have hdescent : baseEnd_1980729 < baseStart_1980729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980759 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 3]
def baseStart_1980759 : Nat := 118140960795 + 1980759 * 2 ^ 59
def prefixEnd_1980759 : Nat := 4983230072969 + 3 ^ 40 * 1980759 * 2
def baseEnd_1980759 : Nat := 1017081427719121005003161

theorem tailTrace_1980759 : CollatzResearch.WordTrace tailWord_1980759 prefixEnd_1980759 1017081427719121005003161 := by
  unfold tailWord_1980759
  simp only [CollatzResearch.WordTrace]
  refine ⟨72244215831055904549929331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48162810554037269699952887 72244215831055904549929331)
  ·
    refine ⟨108366323746583856824893997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72244215831055904549929331 108366323746583856824893997)
    ·
      refine ⟨40637371404968946309335249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108366323746583856824893997 40637371404968946309335249)
      ·
        refine ⟨30478028553726709732001437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40637371404968946309335249 30478028553726709732001437)
        ·
          refine ⟨11429260707647516149500539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30478028553726709732001437 11429260707647516149500539)
          ·
            refine ⟨17143891061471274224250809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11429260707647516149500539 17143891061471274224250809)
            ·
              refine ⟨12857918296103455668188107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17143891061471274224250809 12857918296103455668188107)
              ·
                refine ⟨19286877444155183502282161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12857918296103455668188107 19286877444155183502282161)
                ·
                  refine ⟨14465158083116387626711621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19286877444155183502282161 14465158083116387626711621)
                  ·
                    refine ⟨2712217140584322680008429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14465158083116387626711621 2712217140584322680008429)
                    ·
                      refine ⟨1017081427719121005003161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2712217140584322680008429 1017081427719121005003161)
                      ·
                        rfl

theorem cell23_1980759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_1980759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980759 prefixEnd_1980759 := by exact prefixLift 1980759
  have htrace : WordTrace (prefixWord ++ tailWord_1980759) baseStart_1980759 baseEnd_1980759 := by
    simpa [prefixWord, tailWord_1980759, baseEnd_1980759] using wordTrace_append hprefix tailTrace_1980759
  have hstable : (prefixWord ++ tailWord_1980759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980759).length < 2 ^ (prefixWord ++ tailWord_1980759).sum := by decide
  have hdescent : baseEnd_1980759 < baseStart_1980759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980873 : List Nat := [1, 2, 1, 1, 2, 1, 6, 4, 1, 4]
def baseStart_1980873 : Nat := 118140960795 + 1980873 * 2 ^ 59
def prefixEnd_1980873 : Nat := 4983230072969 + 3 ^ 40 * 1980873 * 2
def baseEnd_1980873 : Nat := 339046654837911186325879

theorem tailTrace_1980873 : CollatzResearch.WordTrace tailWord_1980873 prefixEnd_1980873 339046654837911186325879 := by
  unfold tailWord_1980873
  simp only [CollatzResearch.WordTrace]
  refine ⟨72248373752642902019579273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48165582501761934679719515 72248373752642902019579273)
  ·
    refine ⟨54186280314482176514684455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72248373752642902019579273 54186280314482176514684455)
    ·
      refine ⟨81279420471723264772026683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54186280314482176514684455 81279420471723264772026683)
      ·
        refine ⟨121919130707584897158040025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81279420471723264772026683 121919130707584897158040025)
        ·
          refine ⟨91439348030688672868530019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121919130707584897158040025 91439348030688672868530019)
          ·
            refine ⟨137159022046033009302795029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91439348030688672868530019 137159022046033009302795029)
            ·
              refine ⟨6429329158407797311068517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137159022046033009302795029 6429329158407797311068517)
              ·
                refine ⟨1205499217201461995825347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6429329158407797311068517 1205499217201461995825347)
                ·
                  refine ⟨1808248825802192993738021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205499217201461995825347 1808248825802192993738021)
                  ·
                    refine ⟨339046654837911186325879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1808248825802192993738021 339046654837911186325879)
                    ·
                      rfl

theorem cell23_1980873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 1, 4].length) (baseStart_1980873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980873 prefixEnd_1980873 := by exact prefixLift 1980873
  have htrace : WordTrace (prefixWord ++ tailWord_1980873) baseStart_1980873 baseEnd_1980873 := by
    simpa [prefixWord, tailWord_1980873, baseEnd_1980873] using wordTrace_append hprefix tailTrace_1980873
  have hstable : (prefixWord ++ tailWord_1980873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980873).length < 2 ^ (prefixWord ++ tailWord_1980873).sum := by decide
  have hdescent : baseEnd_1980873 < baseStart_1980873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980889 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_1980889 : Nat := 118140960795 + 1980889 * 2 ^ 59
def prefixEnd_1980889 : Nat := 4983230072969 + 3 ^ 40 * 1980889 * 2
def baseEnd_1980889 : Nat := 1017148180204205496377563

theorem tailTrace_1980889 : CollatzResearch.WordTrace tailWord_1980889 prefixEnd_1980889 1017148180204205496377563 := by
  unfold tailWord_1980889
  simp only [CollatzResearch.WordTrace]
  refine ⟨72248957320584936752161721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48165971547056624501441147 72248957320584936752161721)
  ·
    refine ⟨54186717990438702564121291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72248957320584936752161721 54186717990438702564121291)
    ·
      refine ⟨81280076985658053846181937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54186717990438702564121291 81280076985658053846181937)
      ·
        refine ⟨60960057739243540384636453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81280076985658053846181937 60960057739243540384636453)
        ·
          refine ⟨11430010826108163822119335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60960057739243540384636453 11430010826108163822119335)
          ·
            refine ⟨17145016239162245733179003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11430010826108163822119335 17145016239162245733179003)
            ·
              refine ⟨25717524358743368599768505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17145016239162245733179003 25717524358743368599768505)
              ·
                refine ⟨19288143269057526449826379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25717524358743368599768505 19288143269057526449826379)
                ·
                  refine ⟨28932214903586289674739569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19288143269057526449826379 28932214903586289674739569)
                  ·
                    refine ⟨21699161177689717256054677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28932214903586289674739569 21699161177689717256054677)
                    ·
                      refine ⟨1017148180204205496377563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21699161177689717256054677 1017148180204205496377563)
                      ·
                        rfl

theorem cell23_1980889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_1980889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980889 prefixEnd_1980889 := by exact prefixLift 1980889
  have htrace : WordTrace (prefixWord ++ tailWord_1980889) baseStart_1980889 baseEnd_1980889 := by
    simpa [prefixWord, tailWord_1980889, baseEnd_1980889] using wordTrace_append hprefix tailTrace_1980889
  have hstable : (prefixWord ++ tailWord_1980889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980889).length < 2 ^ (prefixWord ++ tailWord_1980889).sum := by decide
  have hdescent : baseEnd_1980889 < baseStart_1980889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980919 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_1980919 : Nat := 118140960795 + 1980919 * 2 ^ 59
def prefixEnd_1980919 : Nat := 4983230072969 + 3 ^ 40 * 1980919 * 2
def baseEnd_1980919 : Nat := 1017163584623840379002425

theorem tailTrace_1980919 : CollatzResearch.WordTrace tailWord_1980919 prefixEnd_1980919 1017163584623840379002425 := by
  unfold tailWord_1980919
  simp only [CollatzResearch.WordTrace]
  refine ⟨72250051510476251875753811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48166701006984167917169207 72250051510476251875753811)
  ·
    refine ⟨108375077265714377813630717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72250051510476251875753811 108375077265714377813630717)
    ·
      refine ⟨40640653974642891680111519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108375077265714377813630717 40640653974642891680111519)
      ·
        refine ⟨60960980961964337520167279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40640653974642891680111519 60960980961964337520167279)
        ·
          refine ⟨91441471442946506280250919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60960980961964337520167279 91441471442946506280250919)
          ·
            refine ⟨137162207164419759420376379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91441471442946506280250919 137162207164419759420376379)
            ·
              refine ⟨205743310746629639130564569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137162207164419759420376379 205743310746629639130564569)
              ·
                refine ⟨154307483059972229347923427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205743310746629639130564569 154307483059972229347923427)
                ·
                  refine ⟨231461224589958344021885141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154307483059972229347923427 231461224589958344021885141)
                  ·
                    refine ⟨5424872451327148688012933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 231461224589958344021885141 5424872451327148688012933)
                    ·
                      refine ⟨1017163584623840379002425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5424872451327148688012933 1017163584623840379002425)
                      ·
                        rfl

theorem cell23_1980919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_1980919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980919 prefixEnd_1980919 := by exact prefixLift 1980919
  have htrace : WordTrace (prefixWord ++ tailWord_1980919) baseStart_1980919 baseEnd_1980919 := by
    simpa [prefixWord, tailWord_1980919, baseEnd_1980919] using wordTrace_append hprefix tailTrace_1980919
  have hstable : (prefixWord ++ tailWord_1980919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980919).length < 2 ^ (prefixWord ++ tailWord_1980919).sum := by decide
  have hdescent : baseEnd_1980919 < baseStart_1980919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980936 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_1980936 : Nat := 118140960795 + 1980936 * 2 ^ 59
def prefixEnd_1980936 : Nat := 4983230072969 + 3 ^ 40 * 1980936 * 2
def baseEnd_1980936 : Nat := 1017172313794966812489847

theorem tailTrace_1980936 : CollatzResearch.WordTrace tailWord_1980936 prefixEnd_1980936 1017172313794966812489847 := by
  unfold tailWord_1980936
  simp only [CollatzResearch.WordTrace]
  refine ⟨36125335775707331889561331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48167114367609775852748441 36125335775707331889561331)
  ·
    refine ⟨54188003663560997834341997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36125335775707331889561331 54188003663560997834341997)
    ·
      refine ⟨20320501373835374187878249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54188003663560997834341997 20320501373835374187878249)
      ·
        refine ⟨15240376030376530640908687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20320501373835374187878249 15240376030376530640908687)
        ·
          refine ⟨22860564045564795961363031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15240376030376530640908687 22860564045564795961363031)
          ·
            refine ⟨34290846068347193942044547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22860564045564795961363031 34290846068347193942044547)
            ·
              refine ⟨51436269102520790913066821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34290846068347193942044547 51436269102520790913066821)
              ·
                refine ⟨9644300456722648296200029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51436269102520790913066821 9644300456722648296200029)
                ·
                  refine ⟨3616612671270993111075011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9644300456722648296200029 3616612671270993111075011)
                  ·
                    refine ⟨5424919006906489666612517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3616612671270993111075011 5424919006906489666612517)
                    ·
                      refine ⟨1017172313794966812489847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5424919006906489666612517 1017172313794966812489847)
                      ·
                        rfl

theorem cell23_1980936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_1980936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980936 prefixEnd_1980936 := by exact prefixLift 1980936
  have htrace : WordTrace (prefixWord ++ tailWord_1980936) baseStart_1980936 baseEnd_1980936 := by
    simpa [prefixWord, tailWord_1980936, baseEnd_1980936] using wordTrace_append hprefix tailTrace_1980936
  have hstable : (prefixWord ++ tailWord_1980936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980936).length < 2 ^ (prefixWord ++ tailWord_1980936).sum := by decide
  have hdescent : baseEnd_1980936 < baseStart_1980936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980993 : List Nat := [1, 2, 5, 1, 1, 4, 1, 8]
def baseStart_1980993 : Nat := 118140960795 + 1980993 * 2 ^ 59
def prefixEnd_1980993 : Nat := 4983230072969 + 3 ^ 40 * 1980993 * 2
def baseEnd_1980993 : Nat := 37674132673787892202855

theorem tailTrace_1980993 : CollatzResearch.WordTrace tailWord_1980993 prefixEnd_1980993 37674132673787892202855 := by
  unfold tailWord_1980993
  simp only [CollatzResearch.WordTrace]
  refine ⟨72252750512208162513947633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48168500341472108342631755 72252750512208162513947633)
  ·
    refine ⟨54189562884156121885460725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72252750512208162513947633 54189562884156121885460725)
    ·
      refine ⟨5080271520389636426761943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54189562884156121885460725 5080271520389636426761943)
      ·
        refine ⟨7620407280584454640142915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5080271520389636426761943 7620407280584454640142915)
        ·
          refine ⟨11430610920876681960214373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7620407280584454640142915 11430610920876681960214373)
          ·
            refine ⟨2143239547664377867540195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11430610920876681960214373 2143239547664377867540195)
            ·
              refine ⟨3214859321496566801310293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143239547664377867540195 3214859321496566801310293)
              ·
                refine ⟨37674132673787892202855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3214859321496566801310293 37674132673787892202855)
                ·
                  rfl

theorem cell23_1980993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 8].length) (baseStart_1980993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1980993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1980993 prefixEnd_1980993 := by exact prefixLift 1980993
  have htrace : WordTrace (prefixWord ++ tailWord_1980993) baseStart_1980993 baseEnd_1980993 := by
    simpa [prefixWord, tailWord_1980993, baseEnd_1980993] using wordTrace_append hprefix tailTrace_1980993
  have hstable : (prefixWord ++ tailWord_1980993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980993).length < 2 ^ (prefixWord ++ tailWord_1980993).sum := by decide
  have hdescent : baseEnd_1980993 < baseStart_1980993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981036 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_1981036 : Nat := 118140960795 + 1981036 * 2 ^ 59
def prefixEnd_1981036 : Nat := 4983230072969 + 3 ^ 40 * 1981036 * 2
def baseEnd_1981036 : Nat := 339074553953472140413129

theorem tailTrace_1981036 : CollatzResearch.WordTrace tailWord_1981036 prefixEnd_1981036 339074553953472140413129 := by
  unfold tailWord_1981036
  simp only [CollatzResearch.WordTrace]
  refine ⟨36127159425526190428881481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48169545900701587238508641 36127159425526190428881481)
  ·
    refine ⟨27095369569144642821661111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36127159425526190428881481 27095369569144642821661111)
    ·
      refine ⟨40643054353716964232491667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27095369569144642821661111 40643054353716964232491667)
      ·
        refine ⟨60964581530575446348737501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40643054353716964232491667 60964581530575446348737501)
        ·
          refine ⟨22861718073965792380776563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60964581530575446348737501 22861718073965792380776563)
          ·
            refine ⟨34292577110948688571164845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22861718073965792380776563 34292577110948688571164845)
            ·
              refine ⟨12859716416605758214186817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34292577110948688571164845 12859716416605758214186817)
              ·
                refine ⟨9644787312454318660640113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12859716416605758214186817 9644787312454318660640113)
                ·
                  refine ⟨7233590484340738995480085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9644787312454318660640113 7233590484340738995480085)
                  ·
                    refine ⟨339074553953472140413129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7233590484340738995480085 339074553953472140413129)
                    ·
                      rfl

theorem cell23_1981036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_1981036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981036 prefixEnd_1981036 := by exact prefixLift 1981036
  have htrace : WordTrace (prefixWord ++ tailWord_1981036) baseStart_1981036 baseEnd_1981036 := by
    simpa [prefixWord, tailWord_1981036, baseEnd_1981036] using wordTrace_append hprefix tailTrace_1981036
  have hstable : (prefixWord ++ tailWord_1981036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981036).length < 2 ^ (prefixWord ++ tailWord_1981036).sum := by decide
  have hdescent : baseEnd_1981036 < baseStart_1981036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981037 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_1981037 : Nat := 118140960795 + 1981037 * 2 ^ 59
def prefixEnd_1981037 : Nat := 4983230072969 + 3 ^ 40 * 1981037 * 2
def baseEnd_1981037 : Nat := 1017224175341070917326883

theorem tailTrace_1981037 : CollatzResearch.WordTrace tailWord_1981037 prefixEnd_1981037 1017224175341070917326883 := by
  unfold tailWord_1981037
  simp only [CollatzResearch.WordTrace]
  refine ⟨72254355324048758028549365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48169570216032505352366243 72254355324048758028549365)
  ·
    refine ⟨6773845811629571065176503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72254355324048758028549365 6773845811629571065176503)
    ·
      refine ⟨10160768717444356597764755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6773845811629571065176503 10160768717444356597764755)
      ·
        refine ⟨15241153076166534896647133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10160768717444356597764755 15241153076166534896647133)
        ·
          refine ⟨5715432403562450586242675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15241153076166534896647133 5715432403562450586242675)
          ·
            refine ⟨8573148605343675879364013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5715432403562450586242675 8573148605343675879364013)
            ·
              refine ⟨3214930727003878454761505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8573148605343675879364013 3214930727003878454761505)
              ·
                refine ⟨2411198045252908841071129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3214930727003878454761505 2411198045252908841071129)
                ·
                  refine ⟨1808398533939681630803347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2411198045252908841071129 1808398533939681630803347)
                  ·
                    refine ⟨2712597800909522446205021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1808398533939681630803347 2712597800909522446205021)
                    ·
                      refine ⟨1017224175341070917326883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2712597800909522446205021 1017224175341070917326883)
                      ·
                        rfl

theorem cell23_1981037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_1981037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981037 prefixEnd_1981037 := by exact prefixLift 1981037
  have htrace : WordTrace (prefixWord ++ tailWord_1981037) baseStart_1981037 baseEnd_1981037 := by
    simpa [prefixWord, tailWord_1981037, baseEnd_1981037] using wordTrace_append hprefix tailTrace_1981037
  have hstable : (prefixWord ++ tailWord_1981037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981037).length < 2 ^ (prefixWord ++ tailWord_1981037).sum := by decide
  have hdescent : baseEnd_1981037 < baseStart_1981037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981111 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 2, 2, 2]
def baseStart_1981111 : Nat := 118140960795 + 1981111 * 2 ^ 59
def prefixEnd_1981111 : Nat := 4983230072969 + 3 ^ 40 * 1981111 * 2
def baseEnd_1981111 : Nat := 1017262172909503627801543

theorem tailTrace_1981111 : CollatzResearch.WordTrace tailWord_1981111 prefixEnd_1981111 1017262172909503627801543 := by
  unfold tailWord_1981111
  simp only [CollatzResearch.WordTrace]
  refine ⟨72257054325780668666743187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48171369550520445777828791 72257054325780668666743187)
  ·
    refine ⟨108385581488671003000114781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72257054325780668666743187 108385581488671003000114781)
    ·
      refine ⟨40644593058251626125043043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108385581488671003000114781 40644593058251626125043043)
      ·
        refine ⟨60966889587377439187564565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40644593058251626125043043 60966889587377439187564565)
        ·
          refine ⟨2857822949408317461917089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60966889587377439187564565 2857822949408317461917089)
          ·
            refine ⟨2143367212056238096437817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2857822949408317461917089 2143367212056238096437817)
            ·
              refine ⟨1607525409042178572328363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2143367212056238096437817 1607525409042178572328363)
              ·
                refine ⟨2411288113563267858492545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607525409042178572328363 2411288113563267858492545)
                ·
                  refine ⟨1808466085172450893869409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2411288113563267858492545 1808466085172450893869409)
                  ·
                    refine ⟨1356349563879338170402057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1808466085172450893869409 1356349563879338170402057)
                    ·
                      refine ⟨1017262172909503627801543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356349563879338170402057 1017262172909503627801543)
                      ·
                        rfl

theorem cell23_1981111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 2, 2, 2].length) (baseStart_1981111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981111 prefixEnd_1981111 := by exact prefixLift 1981111
  have htrace : WordTrace (prefixWord ++ tailWord_1981111) baseStart_1981111 baseEnd_1981111 := by
    simpa [prefixWord, tailWord_1981111, baseEnd_1981111] using wordTrace_append hprefix tailTrace_1981111
  have hstable : (prefixWord ++ tailWord_1981111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981111).length < 2 ^ (prefixWord ++ tailWord_1981111).sum := by decide
  have hdescent : baseEnd_1981111 < baseStart_1981111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981130 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 2, 5]
def baseStart_1981130 : Nat := 118140960795 + 1981130 * 2 ^ 59
def prefixEnd_1981130 : Nat := 4983230072969 + 3 ^ 40 * 1981130 * 2
def baseEnd_1981130 : Nat := 339090643013979684487985

theorem tailTrace_1981130 : CollatzResearch.WordTrace tailWord_1981130 prefixEnd_1981130 339090643013979684487985 := by
  unfold tailWord_1981130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18064436828177958727921211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48171831541807889941123229 18064436828177958727921211)
  ·
    refine ⟨27096655242266938091881817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18064436828177958727921211 27096655242266938091881817)
    ·
      refine ⟨20322491431700203568911363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27096655242266938091881817 20322491431700203568911363)
      ·
        refine ⟨30483737147550305353367045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20322491431700203568911363 30483737147550305353367045)
        ·
          refine ⟨5715700715165682253756321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30483737147550305353367045 5715700715165682253756321)
          ·
            refine ⟨4286775536374261690317241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5715700715165682253756321 4286775536374261690317241)
            ·
              refine ⟨3215081652280696267737931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4286775536374261690317241 3215081652280696267737931)
              ·
                refine ⟨4822622478421044401606897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215081652280696267737931 4822622478421044401606897)
                ·
                  refine ⟨3616966858815783301205173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4822622478421044401606897 3616966858815783301205173)
                  ·
                    refine ⟨339090643013979684487985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3616966858815783301205173 339090643013979684487985)
                    ·
                      rfl

theorem cell23_1981130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_1981130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981130 prefixEnd_1981130 := by exact prefixLift 1981130
  have htrace : WordTrace (prefixWord ++ tailWord_1981130) baseStart_1981130 baseEnd_1981130 := by
    simpa [prefixWord, tailWord_1981130, baseEnd_1981130] using wordTrace_append hprefix tailTrace_1981130
  have hstable : (prefixWord ++ tailWord_1981130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981130).length < 2 ^ (prefixWord ++ tailWord_1981130).sum := by decide
  have hdescent : baseEnd_1981130 < baseStart_1981130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981207 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 6]
def baseStart_1981207 : Nat := 118140960795 + 1981207 * 2 ^ 59
def prefixEnd_1981207 : Nat := 4983230072969 + 3 ^ 40 * 1981207 * 2
def baseEnd_1981207 : Nat := 113034607450259472466789

theorem tailTrace_1981207 : CollatzResearch.WordTrace tailWord_1981207 prefixEnd_1981207 113034607450259472466789 := by
  unfold tailWord_1981207
  simp only [CollatzResearch.WordTrace]
  refine ⟨72260555733432877062237875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48173703822288584708158583 72260555733432877062237875)
  ·
    refine ⟨108390833600149315593356813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72260555733432877062237875 108390833600149315593356813)
    ·
      refine ⟨40646562600055993347508805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108390833600149315593356813 40646562600055993347508805)
      ·
        refine ⟨7621230487510498752657901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40646562600055993347508805 7621230487510498752657901)
        ·
          refine ⟨2857961432816437032246713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7621230487510498752657901 2857961432816437032246713)
          ·
            refine ⟨2143471074612327774185035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2857961432816437032246713 2143471074612327774185035)
            ·
              refine ⟨3215206611918491661277553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143471074612327774185035 3215206611918491661277553)
              ·
                refine ⟨2411404958938868745958165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3215206611918491661277553 2411404958938868745958165)
                ·
                  refine ⟨113034607450259472466789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2411404958938868745958165 113034607450259472466789)
                  ·
                    rfl

theorem cell23_1981207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 6].length) (baseStart_1981207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981207 prefixEnd_1981207 := by exact prefixLift 1981207
  have htrace : WordTrace (prefixWord ++ tailWord_1981207) baseStart_1981207 baseEnd_1981207 := by
    simpa [prefixWord, tailWord_1981207, baseEnd_1981207] using wordTrace_append hprefix tailTrace_1981207
  have hstable : (prefixWord ++ tailWord_1981207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981207).length < 2 ^ (prefixWord ++ tailWord_1981207).sum := by decide
  have hdescent : baseEnd_1981207 < baseStart_1981207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981217 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_1981217 : Nat := 118140960795 + 1981217 * 2 ^ 59
def prefixEnd_1981217 : Nat := 4983230072969 + 3 ^ 40 * 1981217 * 2
def baseEnd_1981217 : Nat := 1017316601858880213076055

theorem tailTrace_1981217 : CollatzResearch.WordTrace tailWord_1981217 prefixEnd_1981217 1017316601858880213076055 := by
  unfold tailWord_1981217
  simp only [CollatzResearch.WordTrace]
  refine ⟨72260920463396648770101905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48173946975597765846734603 72260920463396648770101905)
  ·
    refine ⟨54195690347547486577576429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72260920463396648770101905 54195690347547486577576429)
    ·
      refine ⟨20323383880330307466591161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54195690347547486577576429 20323383880330307466591161)
      ·
        refine ⟨15242537910247730599943371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20323383880330307466591161 15242537910247730599943371)
        ·
          refine ⟨22863806865371595899915057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15242537910247730599943371 22863806865371595899915057)
          ·
            refine ⟨17147855149028696924936293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22863806865371595899915057 17147855149028696924936293)
            ·
              refine ⟨3215222840442880673425555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17147855149028696924936293 3215222840442880673425555)
              ·
                refine ⟨4822834260664321010138333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215222840442880673425555 4822834260664321010138333)
                ·
                  refine ⟨1808562847749120378801875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4822834260664321010138333 1808562847749120378801875)
                  ·
                    refine ⟨2712844271623680568202813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1808562847749120378801875 2712844271623680568202813)
                    ·
                      refine ⟨1017316601858880213076055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2712844271623680568202813 1017316601858880213076055)
                      ·
                        rfl

theorem cell23_1981217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_1981217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981217 prefixEnd_1981217 := by exact prefixLift 1981217
  have htrace : WordTrace (prefixWord ++ tailWord_1981217) baseStart_1981217 baseEnd_1981217 := by
    simpa [prefixWord, tailWord_1981217, baseEnd_1981217] using wordTrace_append hprefix tailTrace_1981217
  have hstable : (prefixWord ++ tailWord_1981217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981217).length < 2 ^ (prefixWord ++ tailWord_1981217).sum := by decide
  have hdescent : baseEnd_1981217 < baseStart_1981217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981237 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1981237 : Nat := 118140960795 + 1981237 * 2 ^ 59
def prefixEnd_1981237 : Nat := 4983230072969 + 3 ^ 40 * 1981237 * 2
def baseEnd_1981237 : Nat := 339108957157323378275321

theorem tailTrace_1981237 : CollatzResearch.WordTrace tailWord_1981237 prefixEnd_1981237 339108957157323378275321 := by
  unfold tailWord_1981237
  simp only [CollatzResearch.WordTrace]
  refine ⟨72261649923324192185829965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48174433282216128123886643 72261649923324192185829965)
  ·
    refine ⟨27098118721246572069686237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72261649923324192185829965 27098118721246572069686237)
    ·
      refine ⟨10161794520467464526132339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27098118721246572069686237 10161794520467464526132339)
      ·
        refine ⟨15242691780701196789198509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10161794520467464526132339 15242691780701196789198509)
        ·
          refine ⟨5716009417762948795949441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15242691780701196789198509 5716009417762948795949441)
          ·
            refine ⟨4287007063322211596962081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5716009417762948795949441 4287007063322211596962081)
            ·
              refine ⟨3215255297491658697721561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4287007063322211596962081 3215255297491658697721561)
              ·
                refine ⟨2411441473118744023291171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3215255297491658697721561 2411441473118744023291171)
                ·
                  refine ⟨3617162209678116034936757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411441473118744023291171 3617162209678116034936757)
                  ·
                    refine ⟨339108957157323378275321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3617162209678116034936757 339108957157323378275321)
                    ·
                      rfl

theorem cell23_1981237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1981237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981237 prefixEnd_1981237 := by exact prefixLift 1981237
  have htrace : WordTrace (prefixWord ++ tailWord_1981237) baseStart_1981237 baseEnd_1981237 := by
    simpa [prefixWord, tailWord_1981237, baseEnd_1981237] using wordTrace_append hprefix tailTrace_1981237
  have hstable : (prefixWord ++ tailWord_1981237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981237).length < 2 ^ (prefixWord ++ tailWord_1981237).sum := by decide
  have hdescent : baseEnd_1981237 < baseStart_1981237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981240 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 2, 6, 2]
def baseStart_1981240 : Nat := 118140960795 + 1981240 * 2 ^ 59
def prefixEnd_1981240 : Nat := 4983230072969 + 3 ^ 40 * 1981240 * 2
def baseEnd_1981240 : Nat := 1017328411913933623088449

theorem tailTrace_1981240 : CollatzResearch.WordTrace tailWord_1981240 prefixEnd_1981240 1017328411913933623088449 := by
  unfold tailWord_1981240
  simp only [CollatzResearch.WordTrace]
  refine ⟨36130879671156661849094587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48174506228208882465459449 36130879671156661849094587)
  ·
    refine ⟨54196319506734992773641881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36130879671156661849094587 54196319506734992773641881)
    ·
      refine ⟨40647239630051244580231411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54196319506734992773641881 40647239630051244580231411)
      ·
        refine ⟨60970859445076866870347117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40647239630051244580231411 60970859445076866870347117)
        ·
          refine ⟨22864072291903825076380169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60970859445076866870347117 22864072291903825076380169)
          ·
            refine ⟨17148054218927868807285127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22864072291903825076380169 17148054218927868807285127)
            ·
              refine ⟨25722081328391803210927691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17148054218927868807285127 25722081328391803210927691)
              ·
                refine ⟨38583121992587704816391537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25722081328391803210927691 38583121992587704816391537)
                ·
                  refine ⟨28937341494440778612293653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38583121992587704816391537 28937341494440778612293653)
                  ·
                    refine ⟨1356437882551911497451265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28937341494440778612293653 1356437882551911497451265)
                    ·
                      refine ⟨1017328411913933623088449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356437882551911497451265 1017328411913933623088449)
                      ·
                        rfl

theorem cell23_1981240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 6, 2].length) (baseStart_1981240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981240 prefixEnd_1981240 := by exact prefixLift 1981240
  have htrace : WordTrace (prefixWord ++ tailWord_1981240) baseStart_1981240 baseEnd_1981240 := by
    simpa [prefixWord, tailWord_1981240, baseEnd_1981240] using wordTrace_append hprefix tailTrace_1981240
  have hstable : (prefixWord ++ tailWord_1981240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981240).length < 2 ^ (prefixWord ++ tailWord_1981240).sum := by decide
  have hdescent : baseEnd_1981240 < baseStart_1981240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981260 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1981260 : Nat := 118140960795 + 1981260 * 2 ^ 59
def prefixEnd_1981260 : Nat := 4983230072969 + 3 ^ 40 * 1981260 * 2
def baseEnd_1981260 : Nat := 1017338681527023544838357

theorem tailTrace_1981260 : CollatzResearch.WordTrace tailWord_1981260 prefixEnd_1981260 1017338681527023544838357 := by
  unfold tailWord_1981260
  simp only [CollatzResearch.WordTrace]
  refine ⟨36131244401120433556958617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48174992534827244742611489 36131244401120433556958617)
  ·
    refine ⟨27098433300840325167718963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36131244401120433556958617 27098433300840325167718963)
    ·
      refine ⟨40647649951260487751578445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27098433300840325167718963 40647649951260487751578445)
      ·
        refine ⟨15242868731722682906841917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40647649951260487751578445 15242868731722682906841917)
        ·
          refine ⟨5716075774396006090065719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15242868731722682906841917 5716075774396006090065719)
          ·
            refine ⟨8574113661594009135098579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5716075774396006090065719 8574113661594009135098579)
            ·
              refine ⟨12861170492391013702647869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8574113661594009135098579 12861170492391013702647869)
              ·
                refine ⟨4822938934646630138492951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12861170492391013702647869 4822938934646630138492951)
                ·
                  refine ⟨7234408401969945207739427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4822938934646630138492951 7234408401969945207739427)
                  ·
                    refine ⟨10851612602954917811609141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7234408401969945207739427 10851612602954917811609141)
                    ·
                      refine ⟨1017338681527023544838357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10851612602954917811609141 1017338681527023544838357)
                      ·
                        rfl

theorem cell23_1981260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1981260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981260 prefixEnd_1981260 := by exact prefixLift 1981260
  have htrace : WordTrace (prefixWord ++ tailWord_1981260) baseStart_1981260 baseEnd_1981260 := by
    simpa [prefixWord, tailWord_1981260, baseEnd_1981260] using wordTrace_append hprefix tailTrace_1981260
  have hstable : (prefixWord ++ tailWord_1981260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981260).length < 2 ^ (prefixWord ++ tailWord_1981260).sum := by decide
  have hdescent : baseEnd_1981260 < baseStart_1981260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981261 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_1981261 : Nat := 118140960795 + 1981261 * 2 ^ 59
def prefixEnd_1981261 : Nat := 4983230072969 + 3 ^ 40 * 1981261 * 2
def baseEnd_1981261 : Nat := 1017339195007678040925853

theorem tailTrace_1981261 : CollatzResearch.WordTrace tailWord_1981261 prefixEnd_1981261 1017339195007678040925853 := by
  unfold tailWord_1981261
  simp only [CollatzResearch.WordTrace]
  refine ⟨72262525275237244284703637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48175016850158162856469091 72262525275237244284703637)
  ·
    refine ⟨3387305872276745825845483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72262525275237244284703637 3387305872276745825845483)
    ·
      refine ⟨5080958808415118738768225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3387305872276745825845483 5080958808415118738768225)
      ·
        refine ⟨3810719106311339054076169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5080958808415118738768225 3810719106311339054076169)
        ·
          refine ⟨2858039329733504290557127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3810719106311339054076169 2858039329733504290557127)
          ·
            refine ⟨4287058994600256435835691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858039329733504290557127 4287058994600256435835691)
            ·
              refine ⟨6430588491900384653753537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287058994600256435835691 6430588491900384653753537)
              ·
                refine ⟨4822941368925288490315153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6430588491900384653753537 4822941368925288490315153)
                ·
                  refine ⟨3617206026693966367736365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4822941368925288490315153 3617206026693966367736365)
                  ·
                    refine ⟨1356452260010237387901137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617206026693966367736365 1356452260010237387901137)
                    ·
                      refine ⟨1017339195007678040925853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356452260010237387901137 1017339195007678040925853)
                      ·
                        rfl

theorem cell23_1981261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_1981261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981261 prefixEnd_1981261 := by exact prefixLift 1981261
  have htrace : WordTrace (prefixWord ++ tailWord_1981261) baseStart_1981261 baseEnd_1981261 := by
    simpa [prefixWord, tailWord_1981261, baseEnd_1981261] using wordTrace_append hprefix tailTrace_1981261
  have hstable : (prefixWord ++ tailWord_1981261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981261).length < 2 ^ (prefixWord ++ tailWord_1981261).sum := by decide
  have hdescent : baseEnd_1981261 < baseStart_1981261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981268 : List Nat := [2, 4, 1, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_1981268 : Nat := 118140960795 + 1981268 * 2 ^ 59
def prefixEnd_1981268 : Nat := 4983230072969 + 3 ^ 40 * 1981268 * 2
def baseEnd_1981268 : Nat := 1017342789372259513538321

theorem tailTrace_1981268 : CollatzResearch.WordTrace tailWord_1981268 prefixEnd_1981268 1017342789372259513538321 := by
  unfold tailWord_1981268
  simp only [CollatzResearch.WordTrace]
  refine ⟨36131390293105942240104229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48175187057474589653472305 36131390293105942240104229)
  ·
    refine ⟨6774635679957364170019543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36131390293105942240104229 6774635679957364170019543)
    ·
      refine ⟨10161953519936046255029315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6774635679957364170019543 10161953519936046255029315)
      ·
        refine ⟨15242930279904069382543973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10161953519936046255029315 15242930279904069382543973)
        ·
          refine ⟨2858049427482013009226995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15242930279904069382543973 2858049427482013009226995)
          ·
            refine ⟨4287074141223019513840493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858049427482013009226995 4287074141223019513840493)
            ·
              refine ⟨1607652802958632317690185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4287074141223019513840493 1607652802958632317690185)
              ·
                refine ⟨1205739602218974238267639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607652802958632317690185 1205739602218974238267639)
                ·
                  refine ⟨1808609403328461357401459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205739602218974238267639 1808609403328461357401459)
                  ·
                    refine ⟨2712914104992692036102189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1808609403328461357401459 2712914104992692036102189)
                    ·
                      refine ⟨1017342789372259513538321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2712914104992692036102189 1017342789372259513538321)
                      ·
                        rfl

theorem cell23_1981268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_1981268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981268 prefixEnd_1981268 := by exact prefixLift 1981268
  have htrace : WordTrace (prefixWord ++ tailWord_1981268) baseStart_1981268 baseEnd_1981268 := by
    simpa [prefixWord, tailWord_1981268, baseEnd_1981268] using wordTrace_append hprefix tailTrace_1981268
  have hstable : (prefixWord ++ tailWord_1981268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981268).length < 2 ^ (prefixWord ++ tailWord_1981268).sum := by decide
  have hdescent : baseEnd_1981268 < baseStart_1981268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981274 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2]
def baseStart_1981274 : Nat := 118140960795 + 1981274 * 2 ^ 59
def prefixEnd_1981274 : Nat := 4983230072969 + 3 ^ 40 * 1981274 * 2
def baseEnd_1981274 : Nat := 1017345870256186490063293

theorem tailTrace_1981274 : CollatzResearch.WordTrace tailWord_1981274 prefixEnd_1981274 1017345870256186490063293 := by
  unfold tailWord_1981274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18065749856047536876231719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48175332949460098336617917 18065749856047536876231719)
  ·
    refine ⟨27098624784071305314347579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18065749856047536876231719 27098624784071305314347579)
    ·
      refine ⟨40647937176106957971521369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27098624784071305314347579 40647937176106957971521369)
      ·
        refine ⟨30485952882080218478641027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40647937176106957971521369 30485952882080218478641027)
        ·
          refine ⟨45728929323120327717961541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30485952882080218478641027 45728929323120327717961541)
          ·
            refine ⟨8574174248085061447117789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45728929323120327717961541 8574174248085061447117789)
            ·
              refine ⟨3215315343031898042669171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8574174248085061447117789 3215315343031898042669171)
              ·
                refine ⟨4822973014547847064003757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215315343031898042669171 4822973014547847064003757)
                ·
                  refine ⟨1808614880455442649001409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4822973014547847064003757 1808614880455442649001409)
                  ·
                    refine ⟨1356461160341581986751057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1808614880455442649001409 1356461160341581986751057)
                    ·
                      refine ⟨1017345870256186490063293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356461160341581986751057 1017345870256186490063293)
                      ·
                        rfl

theorem cell23_1981274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_1981274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981274 prefixEnd_1981274 := by exact prefixLift 1981274
  have htrace : WordTrace (prefixWord ++ tailWord_1981274) baseStart_1981274 baseEnd_1981274 := by
    simpa [prefixWord, tailWord_1981274, baseEnd_1981274] using wordTrace_append hprefix tailTrace_1981274
  have hstable : (prefixWord ++ tailWord_1981274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981274).length < 2 ^ (prefixWord ++ tailWord_1981274).sum := by decide
  have hdescent : baseEnd_1981274 < baseStart_1981274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981284 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_1981284 : Nat := 118140960795 + 1981284 * 2 ^ 59
def prefixEnd_1981284 : Nat := 4983230072969 + 3 ^ 40 * 1981284 * 2
def baseEnd_1981284 : Nat := 339117001687577150312749

theorem tailTrace_1981284 : CollatzResearch.WordTrace tailWord_1981284 prefixEnd_1981284 339117001687577150312749 := by
  unfold tailWord_1981284
  simp only [CollatzResearch.WordTrace]
  refine ⟨36131682077076959606395453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48175576102769279475193937 36131682077076959606395453)
  ·
    refine ⟨13549380778903859852398295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36131682077076959606395453 13549380778903859852398295)
    ·
      refine ⟨20324071168355789778597443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13549380778903859852398295 20324071168355789778597443)
      ·
        refine ⟨30486106752533684667896165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20324071168355789778597443 30486106752533684667896165)
        ·
          refine ⟨5716145016100065875230531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30486106752533684667896165 5716145016100065875230531)
          ·
            refine ⟨8574217524150098812845797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5716145016100065875230531 8574217524150098812845797)
            ·
              refine ⟨1607665785778143527408587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8574217524150098812845797 1607665785778143527408587)
              ·
                refine ⟨2411498678667215291112881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607665785778143527408587 2411498678667215291112881)
                ·
                  refine ⟨1808624009000411468334661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2411498678667215291112881 1808624009000411468334661)
                  ·
                    refine ⟨339117001687577150312749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1808624009000411468334661 339117001687577150312749)
                    ·
                      rfl

theorem cell23_1981284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_1981284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981284 prefixEnd_1981284 := by exact prefixLift 1981284
  have htrace : WordTrace (prefixWord ++ tailWord_1981284) baseStart_1981284 baseEnd_1981284 := by
    simpa [prefixWord, tailWord_1981284, baseEnd_1981284] using wordTrace_append hprefix tailTrace_1981284
  have hstable : (prefixWord ++ tailWord_1981284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981284).length < 2 ^ (prefixWord ++ tailWord_1981284).sum := by decide
  have hdescent : baseEnd_1981284 < baseStart_1981284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981294 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1981294 : Nat := 118140960795 + 1981294 * 2 ^ 59
def prefixEnd_1981294 : Nat := 4983230072969 + 3 ^ 40 * 1981294 * 2
def baseEnd_1981294 : Nat := 1017356139869276411813201

theorem tailTrace_1981294 : CollatzResearch.WordTrace tailWord_1981294 prefixEnd_1981294 1017356139869276411813201 := by
  unfold tailWord_1981294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9032966110514711365081867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48175819256078460613769957 9032966110514711365081867)
  ·
    refine ⟨13549449165772067047622801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9032966110514711365081867 13549449165772067047622801)
    ·
      refine ⟨10162086874329050285717101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13549449165772067047622801 10162086874329050285717101)
      ·
        refine ⟨3810782577873393857143913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10162086874329050285717101 3810782577873393857143913)
        ·
          refine ⟨2858086933405045392857935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3810782577873393857143913 2858086933405045392857935)
          ·
            refine ⟨4287130400107568089286903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858086933405045392857935 4287130400107568089286903)
            ·
              refine ⟨6430695600161352133930355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287130400107568089286903 6430695600161352133930355)
              ·
                refine ⟨9646043400242028200895533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6430695600161352133930355 9646043400242028200895533)
                ·
                  refine ⟨3617266275090760575335825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9646043400242028200895533 3617266275090760575335825)
                  ·
                    refine ⟨2712949706318070431501869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3617266275090760575335825 2712949706318070431501869)
                    ·
                      refine ⟨1017356139869276411813201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2712949706318070431501869 1017356139869276411813201)
                      ·
                        rfl

theorem cell23_1981294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1981294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981294 prefixEnd_1981294 := by exact prefixLift 1981294
  have htrace : WordTrace (prefixWord ++ tailWord_1981294) baseStart_1981294 baseEnd_1981294 := by
    simpa [prefixWord, tailWord_1981294, baseEnd_1981294] using wordTrace_append hprefix tailTrace_1981294
  have hstable : (prefixWord ++ tailWord_1981294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981294).length < 2 ^ (prefixWord ++ tailWord_1981294).sum := by decide
  have hdescent : baseEnd_1981294 < baseStart_1981294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981303 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_1981303 : Nat := 118140960795 + 1981303 * 2 ^ 59
def prefixEnd_1981303 : Nat := 4983230072969 + 3 ^ 40 * 1981303 * 2
def baseEnd_1981303 : Nat := 1017360761195166876600659

theorem tailTrace_1981303 : CollatzResearch.WordTrace tailWord_1981303 prefixEnd_1981303 1017360761195166876600659 := by
  unfold tailWord_1981303
  simp only [CollatzResearch.WordTrace]
  refine ⟨72264057141085085457732563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48176038094056723638488375 72264057141085085457732563)
  ·
    refine ⟨108396085711627628186598845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72264057141085085457732563 108396085711627628186598845)
    ·
      refine ⟨40648532141860360569974567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108396085711627628186598845 40648532141860360569974567)
      ·
        refine ⟨60972798212790540854961851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40648532141860360569974567 60972798212790540854961851)
        ·
          refine ⟨91459197319185811282442777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60972798212790540854961851 91459197319185811282442777)
          ·
            refine ⟨68594397989389358461832083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91459197319185811282442777 68594397989389358461832083)
            ·
              refine ⟨102891596984084037692748125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68594397989389358461832083 102891596984084037692748125)
              ·
                refine ⟨38584348869031514134780547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102891596984084037692748125 38584348869031514134780547)
                ·
                  refine ⟨57876523303547271202170821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38584348869031514134780547 57876523303547271202170821)
                  ·
                    refine ⟨10851848119415113350407029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57876523303547271202170821 10851848119415113350407029)
                    ·
                      refine ⟨1017360761195166876600659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10851848119415113350407029 1017360761195166876600659)
                      ·
                        rfl

theorem cell23_1981303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_1981303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981303 prefixEnd_1981303 := by exact prefixLift 1981303
  have htrace : WordTrace (prefixWord ++ tailWord_1981303) baseStart_1981303 baseEnd_1981303 := by
    simpa [prefixWord, tailWord_1981303, baseEnd_1981303] using wordTrace_append hprefix tailTrace_1981303
  have hstable : (prefixWord ++ tailWord_1981303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981303).length < 2 ^ (prefixWord ++ tailWord_1981303).sum := by decide
  have hdescent : baseEnd_1981303 < baseStart_1981303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981314 : List Nat := [3, 4, 2, 2, 2, 10]
def baseStart_1981314 : Nat := 118140960795 + 1981314 * 2 ^ 59
def prefixEnd_1981314 : Nat := 4983230072969 + 3 ^ 40 * 1981314 * 2
def baseEnd_1981314 : Nat := 4186693043137310014663

theorem tailTrace_1981314 : CollatzResearch.WordTrace tailWord_1981314 prefixEnd_1981314 4186693043137310014663 := by
  unfold tailWord_1981314
  simp only [CollatzResearch.WordTrace]
  refine ⟨18066114586011308584095749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48176305562696822890921997 18066114586011308584095749)
  ·
    refine ⟨3387396484877120359517953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18066114586011308584095749 3387396484877120359517953)
    ·
      refine ⟨2540547363657840269638465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3387396484877120359517953 2540547363657840269638465)
      ·
        refine ⟨1905410522743380202228849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2540547363657840269638465 1905410522743380202228849)
        ·
          refine ⟨1429057892057535151671637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1905410522743380202228849 1429057892057535151671637)
          ·
            refine ⟨4186693043137310014663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1429057892057535151671637 4186693043137310014663)
            ·
              rfl

theorem cell23_1981314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 10].length) (baseStart_1981314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981314 prefixEnd_1981314 := by exact prefixLift 1981314
  have htrace : WordTrace (prefixWord ++ tailWord_1981314) baseStart_1981314 baseEnd_1981314 := by
    simpa [prefixWord, tailWord_1981314, baseEnd_1981314] using wordTrace_append hprefix tailTrace_1981314
  have hstable : (prefixWord ++ tailWord_1981314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981314).length < 2 ^ (prefixWord ++ tailWord_1981314).sum := by decide
  have hdescent : baseEnd_1981314 < baseStart_1981314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981347 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 1, 4, 2]
def baseStart_1981347 : Nat := 118140960795 + 1981347 * 2 ^ 59
def prefixEnd_1981347 : Nat := 4983230072969 + 3 ^ 40 * 1981347 * 2
def baseEnd_1981347 : Nat := 1017383354343964704450457

theorem tailTrace_1981347 : CollatzResearch.WordTrace tailWord_1981347 prefixEnd_1981347 1017383354343964704450457 := by
  unfold tailWord_1981347
  simp only [CollatzResearch.WordTrace]
  refine ⟨72265661952925680972334295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48177107968617120648222863 72265661952925680972334295)
  ·
    refine ⟨108398492929388521458501443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72265661952925680972334295 108398492929388521458501443)
    ·
      refine ⟨162597739394082782187752165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108398492929388521458501443 162597739394082782187752165)
      ·
        refine ⟨30487076136390521660203531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162597739394082782187752165 30487076136390521660203531)
        ·
          refine ⟨45730614204585782490305297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30487076136390521660203531 45730614204585782490305297)
          ·
            refine ⟨34297960653439336867728973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45730614204585782490305297 34297960653439336867728973)
            ·
              refine ⟨12861735245039751325398365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34297960653439336867728973 12861735245039751325398365)
              ·
                refine ⟨4823150716889906747024387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12861735245039751325398365 4823150716889906747024387)
                ·
                  refine ⟨7234726075334860120536581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4823150716889906747024387 7234726075334860120536581)
                  ·
                    refine ⟨1356511139125286272600609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7234726075334860120536581 1356511139125286272600609)
                    ·
                      refine ⟨1017383354343964704450457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356511139125286272600609 1017383354343964704450457)
                      ·
                        rfl

theorem cell23_1981347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_1981347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981347 prefixEnd_1981347 := by exact prefixLift 1981347
  have htrace : WordTrace (prefixWord ++ tailWord_1981347) baseStart_1981347 baseEnd_1981347 := by
    simpa [prefixWord, tailWord_1981347, baseEnd_1981347] using wordTrace_append hprefix tailTrace_1981347
  have hstable : (prefixWord ++ tailWord_1981347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981347).length < 2 ^ (prefixWord ++ tailWord_1981347).sum := by decide
  have hdescent : baseEnd_1981347 < baseStart_1981347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981387 : List Nat := [1, 1, 1, 1, 3, 5, 2, 4, 5]
def baseStart_1981387 : Nat := 118140960795 + 1981387 * 2 ^ 59
def prefixEnd_1981387 : Nat := 4983230072969 + 3 ^ 40 * 1981387 * 2
def baseEnd_1981387 : Nat := 113044877063349394216697

theorem tailTrace_1981387 : CollatzResearch.WordTrace tailWord_1981387 prefixEnd_1981387 113044877063349394216697 := by
  unfold tailWord_1981387
  simp only [CollatzResearch.WordTrace]
  refine ⟨72267120872780767803790415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48178080581853845202526943 72267120872780767803790415)
  ·
    refine ⟨108400681309171151705685623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72267120872780767803790415 108400681309171151705685623)
    ·
      refine ⟨162601021963756727558528435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108400681309171151705685623 162601021963756727558528435)
      ·
        refine ⟨243901532945635091337792653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162601021963756727558528435 243901532945635091337792653)
        ·
          refine ⟨91463074854613159251672245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 243901532945635091337792653 91463074854613159251672245)
          ·
            refine ⟨8574663267619983679844273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91463074854613159251672245 8574663267619983679844273)
            ·
              refine ⟨6430997450714987759883205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8574663267619983679844273 6430997450714987759883205)
              ·
                refine ⟨1205812022009060204978101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6430997450714987759883205 1205812022009060204978101)
                ·
                  refine ⟨113044877063349394216697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1205812022009060204978101 113044877063349394216697)
                  ·
                    rfl

theorem cell23_1981387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 5].length) (baseStart_1981387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981387 prefixEnd_1981387 := by exact prefixLift 1981387
  have htrace : WordTrace (prefixWord ++ tailWord_1981387) baseStart_1981387 baseEnd_1981387 := by
    simpa [prefixWord, tailWord_1981387, baseEnd_1981387] using wordTrace_append hprefix tailTrace_1981387
  have hstable : (prefixWord ++ tailWord_1981387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981387).length < 2 ^ (prefixWord ++ tailWord_1981387).sum := by decide
  have hdescent : baseEnd_1981387 < baseStart_1981387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981398 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_1981398 : Nat := 118140960795 + 1981398 * 2 ^ 59
def prefixEnd_1981398 : Nat := 4983230072969 + 3 ^ 40 * 1981398 * 2
def baseEnd_1981398 : Nat := 1017409541857344004912723

theorem tailTrace_1981398 : CollatzResearch.WordTrace tailWord_1981398 prefixEnd_1981398 1017409541857344004912723 := by
  unfold tailWord_1981398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4516720129733807292652553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48178348050493944454960565 4516720129733807292652553)
  ·
    refine ⟨3387540097300355469489415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4516720129733807292652553 3387540097300355469489415)
    ·
      refine ⟨5081310145950533204234123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3387540097300355469489415 5081310145950533204234123)
      ·
        refine ⟨7621965218925799806351185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081310145950533204234123 7621965218925799806351185)
        ·
          refine ⟨5716473914194349854763389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7621965218925799806351185 5716473914194349854763389)
          ·
            refine ⟨2143677717822881195536271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5716473914194349854763389 2143677717822881195536271)
            ·
              refine ⟨3215516576734321793304407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143677717822881195536271 3215516576734321793304407)
              ·
                refine ⟨4823274865101482689956611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215516576734321793304407 4823274865101482689956611)
                ·
                  refine ⟨7234912297652224034934917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4823274865101482689956611 7234912297652224034934917)
                  ·
                    refine ⟨1356546055809792006550297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7234912297652224034934917 1356546055809792006550297)
                    ·
                      refine ⟨1017409541857344004912723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356546055809792006550297 1017409541857344004912723)
                      ·
                        rfl

theorem cell23_1981398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_1981398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981398 prefixEnd_1981398 := by exact prefixLift 1981398
  have htrace : WordTrace (prefixWord ++ tailWord_1981398) baseStart_1981398 baseEnd_1981398 := by
    simpa [prefixWord, tailWord_1981398, baseEnd_1981398] using wordTrace_append hprefix tailTrace_1981398
  have hstable : (prefixWord ++ tailWord_1981398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981398).length < 2 ^ (prefixWord ++ tailWord_1981398).sum := by decide
  have hdescent : baseEnd_1981398 < baseStart_1981398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981400 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 1, 7]
def baseStart_1981400 : Nat := 118140960795 + 1981400 * 2 ^ 59
def prefixEnd_1981400 : Nat := 4983230072969 + 3 ^ 40 * 1981400 * 2
def baseEnd_1981400 : Nat := 339136856272884332362571

theorem tailTrace_1981400 : CollatzResearch.WordTrace tailWord_1981400 prefixEnd_1981400 339136856272884332362571 := by
  unfold tailWord_1981400
  simp only [CollatzResearch.WordTrace]
  refine ⟨36133797510866835512006827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48178396681155780682675769 36133797510866835512006827)
  ·
    refine ⟨54200696266300253268010241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36133797510866835512006827 54200696266300253268010241)
    ·
      refine ⟨40650522199725189951007681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54200696266300253268010241 40650522199725189951007681)
      ·
        refine ⟨30487891649793892463255761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40650522199725189951007681 30487891649793892463255761)
        ·
          refine ⟨22865918737345419347441821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30487891649793892463255761 22865918737345419347441821)
          ·
            refine ⟨8574719526504532255290683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22865918737345419347441821 8574719526504532255290683)
            ·
              refine ⟨12862079289756798382936025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8574719526504532255290683 12862079289756798382936025)
              ·
                refine ⟨9646559467317598787202019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12862079289756798382936025 9646559467317598787202019)
                ·
                  refine ⟨14469839200976398180803029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9646559467317598787202019 14469839200976398180803029)
                  ·
                    refine ⟨339136856272884332362571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14469839200976398180803029 339136856272884332362571)
                    ·
                      rfl

theorem cell23_1981400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_1981400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981400 prefixEnd_1981400 := by exact prefixLift 1981400
  have htrace : WordTrace (prefixWord ++ tailWord_1981400) baseStart_1981400 baseEnd_1981400 := by
    simpa [prefixWord, tailWord_1981400, baseEnd_1981400] using wordTrace_append hprefix tailTrace_1981400
  have hstable : (prefixWord ++ tailWord_1981400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981400).length < 2 ^ (prefixWord ++ tailWord_1981400).sum := by decide
  have hdescent : baseEnd_1981400 < baseStart_1981400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981438 : List Nat := [4, 2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_1981438 : Nat := 118140960795 + 1981438 * 2 ^ 59
def prefixEnd_1981438 : Nat := 4983230072969 + 3 ^ 40 * 1981438 * 2
def baseEnd_1981438 : Nat := 113047786787058205379171

theorem tailTrace_1981438 : CollatzResearch.WordTrace tailWord_1981438 prefixEnd_1981438 113047786787058205379171 := by
  unfold tailWord_1981438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9033622624449500439237121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48179320663730669009264645 9033622624449500439237121)
  ·
    refine ⟨6775216968337125329427841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9033622624449500439237121 6775216968337125329427841)
    ·
      refine ⟨5081412726252843997070881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6775216968337125329427841 5081412726252843997070881)
      ·
        refine ⟨3811059544689632997803161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5081412726252843997070881 3811059544689632997803161)
        ·
          refine ⟨2858294658517224748352371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3811059544689632997803161 2858294658517224748352371)
          ·
            refine ⟨4287441987775837122528557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858294658517224748352371 4287441987775837122528557)
            ·
              refine ⟨1607790745415938920948209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4287441987775837122528557 1607790745415938920948209)
              ·
                refine ⟨1205843059061954190711157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607790745415938920948209 1205843059061954190711157)
                ·
                  refine ⟨113047786787058205379171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1205843059061954190711157 113047786787058205379171)
                  ·
                    rfl

theorem cell23_1981438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_1981438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981438 prefixEnd_1981438 := by exact prefixLift 1981438
  have htrace : WordTrace (prefixWord ++ tailWord_1981438) baseStart_1981438 baseEnd_1981438 := by
    simpa [prefixWord, tailWord_1981438, baseEnd_1981438] using wordTrace_append hprefix tailTrace_1981438
  have hstable : (prefixWord ++ tailWord_1981438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981438).length < 2 ^ (prefixWord ++ tailWord_1981438).sum := by decide
  have hdescent : baseEnd_1981438 < baseStart_1981438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981474 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_1981474 : Nat := 118140960795 + 1981474 * 2 ^ 59
def prefixEnd_1981474 : Nat := 4983230072969 + 3 ^ 40 * 1981474 * 2
def baseEnd_1981474 : Nat := 1017448566387085707562373

theorem tailTrace_1981474 : CollatzResearch.WordTrace tailWord_1981474 prefixEnd_1981474 1017448566387085707562373 := by
  unfold tailWord_1981474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18067573505866395415551869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48180196015643721108138317 18067573505866395415551869)
  ·
    refine ⟨6775340064699898280831951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18067573505866395415551869 6775340064699898280831951)
    ·
      refine ⟨10163010097049847421247927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6775340064699898280831951 10163010097049847421247927)
      ·
        refine ⟨15244515145574771131871891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10163010097049847421247927 15244515145574771131871891)
        ·
          refine ⟨22866772718362156697807837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15244515145574771131871891 22866772718362156697807837)
          ·
            refine ⟨8575039769385808761677939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22866772718362156697807837 8575039769385808761677939)
            ·
              refine ⟨12862559654078713142516909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575039769385808761677939 12862559654078713142516909)
              ·
                refine ⟨4823459870279517428443841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12862559654078713142516909 4823459870279517428443841)
                ·
                  refine ⟨3617594902709638071332881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4823459870279517428443841 3617594902709638071332881)
                  ·
                    refine ⟨2713196177032228553499661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3617594902709638071332881 2713196177032228553499661)
                    ·
                      refine ⟨1017448566387085707562373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2713196177032228553499661 1017448566387085707562373)
                      ·
                        rfl

theorem cell23_1981474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_1981474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981474 prefixEnd_1981474 := by exact prefixLift 1981474
  have htrace : WordTrace (prefixWord ++ tailWord_1981474) baseStart_1981474 baseEnd_1981474 := by
    simpa [prefixWord, tailWord_1981474, baseEnd_1981474] using wordTrace_append hprefix tailTrace_1981474
  have hstable : (prefixWord ++ tailWord_1981474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981474).length < 2 ^ (prefixWord ++ tailWord_1981474).sum := by decide
  have hdescent : baseEnd_1981474 < baseStart_1981474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981494 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_1981494 : Nat := 118140960795 + 1981494 * 2 ^ 59
def prefixEnd_1981494 : Nat := 4983230072969 + 3 ^ 40 * 1981494 * 2
def baseEnd_1981494 : Nat := 113050981777797292145809

theorem tailTrace_1981494 : CollatzResearch.WordTrace tailWord_1981494 prefixEnd_1981494 113050981777797292145809 := by
  unfold tailWord_1981494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4516938967712070317370971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48180682322262083385290357 4516938967712070317370971)
  ·
    refine ⟨6775408451568105476056457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4516938967712070317370971 6775408451568105476056457)
    ·
      refine ⟨5081556338676079107042343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6775408451568105476056457 5081556338676079107042343)
      ·
        refine ⟨7622334508014118660563515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081556338676079107042343 7622334508014118660563515)
        ·
          refine ⟨11433501762021177990845273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622334508014118660563515 11433501762021177990845273)
          ·
            refine ⟨8575126321515883493133955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11433501762021177990845273 8575126321515883493133955)
            ·
              refine ⟨12862689482273825239700933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8575126321515883493133955 12862689482273825239700933)
              ·
                refine ⟨2411754277926342232443925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12862689482273825239700933 2411754277926342232443925)
                ·
                  refine ⟨113050981777797292145809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2411754277926342232443925 113050981777797292145809)
                  ·
                    rfl

theorem cell23_1981494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_1981494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981494 prefixEnd_1981494 := by exact prefixLift 1981494
  have htrace : WordTrace (prefixWord ++ tailWord_1981494) baseStart_1981494 baseEnd_1981494 := by
    simpa [prefixWord, tailWord_1981494, baseEnd_1981494] using wordTrace_append hprefix tailTrace_1981494
  have hstable : (prefixWord ++ tailWord_1981494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981494).length < 2 ^ (prefixWord ++ tailWord_1981494).sum := by decide
  have hdescent : baseEnd_1981494 < baseStart_1981494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981504 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 3, 1, 3]
def baseStart_1981504 : Nat := 118140960795 + 1981504 * 2 ^ 59
def prefixEnd_1981504 : Nat := 4983230072969 + 3 ^ 40 * 1981504 * 2
def baseEnd_1981504 : Nat := 1017463970806720590187235

theorem tailTrace_1981504 : CollatzResearch.WordTrace tailWord_1981504 prefixEnd_1981504 1017463970806720590187235 := by
  unfold tailWord_1981504
  simp only [CollatzResearch.WordTrace]
  refine ⟨36135694106678448392899783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48180925475571264523866377 36135694106678448392899783)
  ·
    refine ⟨54203541160017672589349675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36135694106678448392899783 54203541160017672589349675)
    ·
      refine ⟨81305311740026508884024513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54203541160017672589349675 81305311740026508884024513)
      ·
        refine ⟨60978983805019881663018385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81305311740026508884024513 60978983805019881663018385)
        ·
          refine ⟨45734237853764911247263789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60978983805019881663018385 45734237853764911247263789)
          ·
            refine ⟨17150339195161841717723921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45734237853764911247263789 17150339195161841717723921)
            ·
              refine ⟨12862754396371381288292941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17150339195161841717723921 12862754396371381288292941)
              ·
                refine ⟨4823532898639267983109853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12862754396371381288292941 4823532898639267983109853)
                ·
                  refine ⟨1808824836989725493666195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4823532898639267983109853 1808824836989725493666195)
                  ·
                    refine ⟨2713237255484588240499293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1808824836989725493666195 2713237255484588240499293)
                    ·
                      refine ⟨1017463970806720590187235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2713237255484588240499293 1017463970806720590187235)
                      ·
                        rfl

theorem cell23_1981504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_1981504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981504 prefixEnd_1981504 := by exact prefixLift 1981504
  have htrace : WordTrace (prefixWord ++ tailWord_1981504) baseStart_1981504 baseEnd_1981504 := by
    simpa [prefixWord, tailWord_1981504, baseEnd_1981504] using wordTrace_append hprefix tailTrace_1981504
  have hstable : (prefixWord ++ tailWord_1981504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981504).length < 2 ^ (prefixWord ++ tailWord_1981504).sum := by decide
  have hdescent : baseEnd_1981504 < baseStart_1981504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981514 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2]
def baseStart_1981514 : Nat := 118140960795 + 1981514 * 2 ^ 59
def prefixEnd_1981514 : Nat := 4983230072969 + 3 ^ 40 * 1981514 * 2
def baseEnd_1981514 : Nat := 1017469105613265551062189

theorem tailTrace_1981514 : CollatzResearch.WordTrace tailWord_1981514 prefixEnd_1981514 1017469105613265551062189 := by
  unfold tailWord_1981514
  simp only [CollatzResearch.WordTrace]
  refine ⟨18067938235830167123415899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48181168628880445662442397 18067938235830167123415899)
  ·
    refine ⟨27101907353745250685123849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18067938235830167123415899 27101907353745250685123849)
    ·
      refine ⟨20326430515308938013842887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27101907353745250685123849 20326430515308938013842887)
      ·
        refine ⟨30489645772963407020764331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20326430515308938013842887 30489645772963407020764331)
        ·
          refine ⟨45734468659445110531146497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30489645772963407020764331 45734468659445110531146497)
          ·
            refine ⟨34300851494583832898359873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45734468659445110531146497 34300851494583832898359873)
            ·
              refine ⟨25725638620937874673769905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34300851494583832898359873 25725638620937874673769905)
              ·
                refine ⟨19294228965703406005327429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25725638620937874673769905 19294228965703406005327429)
                ·
                  refine ⟨3617667931069388625998893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19294228965703406005327429 3617667931069388625998893)
                  ·
                    refine ⟨1356625474151020734749585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3617667931069388625998893 1356625474151020734749585)
                    ·
                      refine ⟨1017469105613265551062189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356625474151020734749585 1017469105613265551062189)
                      ·
                        rfl

theorem cell23_1981514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_1981514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981514 prefixEnd_1981514 := by exact prefixLift 1981514
  have htrace : WordTrace (prefixWord ++ tailWord_1981514) baseStart_1981514 baseEnd_1981514 := by
    simpa [prefixWord, tailWord_1981514, baseEnd_1981514] using wordTrace_append hprefix tailTrace_1981514
  have hstable : (prefixWord ++ tailWord_1981514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981514).length < 2 ^ (prefixWord ++ tailWord_1981514).sum := by decide
  have hdescent : baseEnd_1981514 < baseStart_1981514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981537 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 1, 6]
def baseStart_1981537 : Nat := 118140960795 + 1981537 * 2 ^ 59
def prefixEnd_1981537 : Nat := 4983230072969 + 3 ^ 40 * 1981537 * 2
def baseEnd_1981537 : Nat := 339160305222772987024861

theorem tailTrace_1981537 : CollatzResearch.WordTrace tailWord_1981537 prefixEnd_1981537 339160305222772987024861 := by
  unfold tailWord_1981537
  simp only [CollatzResearch.WordTrace]
  refine ⟨72272591822237343421750865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48181727881491562281167243 72272591822237343421750865)
  ·
    refine ⟨54204443866678007566313149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72272591822237343421750865 54204443866678007566313149)
    ·
      refine ⟨20326666450004252837367431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54204443866678007566313149 20326666450004252837367431)
      ·
        refine ⟨30489999675006379256051147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20326666450004252837367431 30489999675006379256051147)
        ·
          refine ⟨45734999512509568884076721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30489999675006379256051147 45734999512509568884076721)
          ·
            refine ⟨34301249634382176663057541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45734999512509568884076721 34301249634382176663057541)
            ·
              refine ⟨6431484306446658124323289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34301249634382176663057541 6431484306446658124323289)
              ·
                refine ⟨4823613229834993593242467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6431484306446658124323289 4823613229834993593242467)
                ·
                  refine ⟨7235419844752490389863701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4823613229834993593242467 7235419844752490389863701)
                  ·
                    refine ⟨339160305222772987024861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7235419844752490389863701 339160305222772987024861)
                    ·
                      rfl

theorem cell23_1981537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_1981537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981537 prefixEnd_1981537 := by exact prefixLift 1981537
  have htrace : WordTrace (prefixWord ++ tailWord_1981537) baseStart_1981537 baseEnd_1981537 := by
    simpa [prefixWord, tailWord_1981537, baseEnd_1981537] using wordTrace_append hprefix tailTrace_1981537
  have hstable : (prefixWord ++ tailWord_1981537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981537).length < 2 ^ (prefixWord ++ tailWord_1981537).sum := by decide
  have hdescent : baseEnd_1981537 < baseStart_1981537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981554 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_1981554 : Nat := 118140960795 + 1981554 * 2 ^ 59
def prefixEnd_1981554 : Nat := 4983230072969 + 3 ^ 40 * 1981554 * 2
def baseEnd_1981554 : Nat := 339163214946481798187335

theorem tailTrace_1981554 : CollatzResearch.WordTrace tailWord_1981554 prefixEnd_1981554 339163214946481798187335 := by
  unfold tailWord_1981554
  simp only [CollatzResearch.WordTrace]
  refine ⟨18068302965793938831279929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48182141242117170216746477 18068302965793938831279929)
  ·
    refine ⟨13551227224345454123459947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18068302965793938831279929 13551227224345454123459947)
    ·
      refine ⟨20326840836518181185189921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13551227224345454123459947 20326840836518181185189921)
      ·
        refine ⟨15245130627388635888892441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20326840836518181185189921 15245130627388635888892441)
        ·
          refine ⟨11433847970541476916669331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15245130627388635888892441 11433847970541476916669331)
          ·
            refine ⟨17150771955812215375003997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11433847970541476916669331 17150771955812215375003997)
            ·
              refine ⟨6431539483429580765626499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17150771955812215375003997 6431539483429580765626499)
              ·
                refine ⟨9647309225144371148439749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6431539483429580765626499 9647309225144371148439749)
                ·
                  refine ⟨1808870479714569590332453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9647309225144371148439749 1808870479714569590332453)
                  ·
                    refine ⟨339163214946481798187335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1808870479714569590332453 339163214946481798187335)
                    ·
                      rfl

theorem cell23_1981554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_1981554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981554 prefixEnd_1981554 := by exact prefixLift 1981554
  have htrace : WordTrace (prefixWord ++ tailWord_1981554) baseStart_1981554 baseEnd_1981554 := by
    simpa [prefixWord, tailWord_1981554, baseEnd_1981554] using wordTrace_append hprefix tailTrace_1981554
  have hstable : (prefixWord ++ tailWord_1981554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981554).length < 2 ^ (prefixWord ++ tailWord_1981554).sum := by decide
  have hdescent : baseEnd_1981554 < baseStart_1981554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981571 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 2, 4]
def baseStart_1981571 : Nat := 118140960795 + 1981571 * 2 ^ 59
def prefixEnd_1981571 : Nat := 4983230072969 + 3 ^ 40 * 1981571 * 2
def baseEnd_1981571 : Nat := 339166124670190609349809

theorem tailTrace_1981571 : CollatzResearch.WordTrace tailWord_1981571 prefixEnd_1981571 339166124670190609349809 := by
  unfold tailWord_1981571
  simp only [CollatzResearch.WordTrace]
  refine ⟨72273831904114167228488567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48182554602742778152325711 72273831904114167228488567)
  ·
    refine ⟨108410747856171250842732851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72273831904114167228488567 108410747856171250842732851)
    ·
      refine ⟨162616121784256876264099277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108410747856171250842732851 162616121784256876264099277)
      ·
        refine ⟨60981045669096328599037229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162616121784256876264099277 60981045669096328599037229)
        ·
          refine ⟨22867892125911123224638961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60981045669096328599037229 22867892125911123224638961)
          ·
            refine ⟨17150919094433342418479221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22867892125911123224638961 17150919094433342418479221)
            ·
              refine ⟨1607898665103125851732427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17150919094433342418479221 1607898665103125851732427)
              ·
                refine ⟨2411847997654688777598641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607898665103125851732427 2411847997654688777598641)
                ·
                  refine ⟨1808885998241016583198981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2411847997654688777598641 1808885998241016583198981)
                  ·
                    refine ⟨339166124670190609349809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1808885998241016583198981 339166124670190609349809)
                    ·
                      rfl

theorem cell23_1981571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 2, 4].length) (baseStart_1981571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981571 prefixEnd_1981571 := by exact prefixLift 1981571
  have htrace : WordTrace (prefixWord ++ tailWord_1981571) baseStart_1981571 baseEnd_1981571 := by
    simpa [prefixWord, tailWord_1981571, baseEnd_1981571] using wordTrace_append hprefix tailTrace_1981571
  have hstable : (prefixWord ++ tailWord_1981571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981571).length < 2 ^ (prefixWord ++ tailWord_1981571).sum := by decide
  have hdescent : baseEnd_1981571 < baseStart_1981571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981598 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_1981598 : Nat := 118140960795 + 1981598 * 2 ^ 59
def prefixEnd_1981598 : Nat := 4983230072969 + 3 ^ 40 * 1981598 * 2
def baseEnd_1981598 : Nat := 1017512237988243222411803

theorem tailTrace_1981598 : CollatzResearch.WordTrace tailWord_1981598 prefixEnd_1981598 1017512237988243222411803 := by
  unfold tailWord_1981598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9034352084377043854965181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48183211116677567226480965 9034352084377043854965181)
  ·
    refine ⟨3387882031641391445611943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9034352084377043854965181 3387882031641391445611943)
    ·
      refine ⟨5081823047462087168417915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3387882031641391445611943 5081823047462087168417915)
      ·
        refine ⟨7622734571193130752626873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081823047462087168417915 7622734571193130752626873)
        ·
          refine ⟨5717050928394848064470155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7622734571193130752626873 5717050928394848064470155)
          ·
            refine ⟨8575576392592272096705233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5717050928394848064470155 8575576392592272096705233)
            ·
              refine ⟨6431682294444204072528925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8575576392592272096705233 6431682294444204072528925)
              ·
                refine ⟨2411880860416576527198347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6431682294444204072528925 2411880860416576527198347)
                ·
                  refine ⟨3617821290624864790797521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411880860416576527198347 3617821290624864790797521)
                  ·
                    refine ⟨2713365967968648593098141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3617821290624864790797521 2713365967968648593098141)
                    ·
                      refine ⟨1017512237988243222411803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2713365967968648593098141 1017512237988243222411803)
                      ·
                        rfl

theorem cell23_1981598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_1981598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981598 prefixEnd_1981598 := by exact prefixLift 1981598
  have htrace : WordTrace (prefixWord ++ tailWord_1981598) baseStart_1981598 baseEnd_1981598 := by
    simpa [prefixWord, tailWord_1981598, baseEnd_1981598] using wordTrace_append hprefix tailTrace_1981598
  have hstable : (prefixWord ++ tailWord_1981598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981598).length < 2 ^ (prefixWord ++ tailWord_1981598).sum := by decide
  have hdescent : baseEnd_1981598 < baseStart_1981598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981628 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1981628 : Nat := 118140960795 + 1981628 * 2 ^ 59
def prefixEnd_1981628 : Nat := 4983230072969 + 3 ^ 40 * 1981628 * 2
def baseEnd_1981628 : Nat := 1017527642407878105036665

theorem tailTrace_1981628 : CollatzResearch.WordTrace tailWord_1981628 prefixEnd_1981628 1017527642407878105036665 := by
  unfold tailWord_1981628
  simp only [CollatzResearch.WordTrace]
  refine ⟨36137955432453832981656769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48183940576605110642209025 36137955432453832981656769)
  ·
    refine ⟨27103466574340374736242577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36137955432453832981656769 27103466574340374736242577)
    ·
      refine ⟨20327599930755281052181933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27103466574340374736242577 20327599930755281052181933)
      ·
        refine ⟨7622849974033230394568225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20327599930755281052181933 7622849974033230394568225)
        ·
          refine ⟨5717137480524922795926169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7622849974033230394568225 5717137480524922795926169)
          ·
            refine ⟨4287853110393692096944627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5717137480524922795926169 4287853110393692096944627)
            ·
              refine ⟨6431779665590538145416941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287853110393692096944627 6431779665590538145416941)
              ·
                refine ⟨2411917374596451804531353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6431779665590538145416941 2411917374596451804531353)
                ·
                  refine ⟨1808938030947338853398515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2411917374596451804531353 1808938030947338853398515)
                  ·
                    refine ⟨2713407046421008280097773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1808938030947338853398515 2713407046421008280097773)
                    ·
                      refine ⟨1017527642407878105036665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2713407046421008280097773 1017527642407878105036665)
                      ·
                        rfl

theorem cell23_1981628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1981628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981628 prefixEnd_1981628 := by exact prefixLift 1981628
  have htrace : WordTrace (prefixWord ++ tailWord_1981628) baseStart_1981628 baseEnd_1981628 := by
    simpa [prefixWord, tailWord_1981628, baseEnd_1981628] using wordTrace_append hprefix tailTrace_1981628
  have hstable : (prefixWord ++ tailWord_1981628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981628).length < 2 ^ (prefixWord ++ tailWord_1981628).sum := by decide
  have hdescent : baseEnd_1981628 < baseStart_1981628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981645 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1981645 : Nat := 118140960795 + 1981645 * 2 ^ 59
def prefixEnd_1981645 : Nat := 4983230072969 + 3 ^ 40 * 1981645 * 2
def baseEnd_1981645 : Nat := 1017536371579004538524087

theorem tailTrace_1981645 : CollatzResearch.WordTrace tailWord_1981645 prefixEnd_1981645 1017536371579004538524087 := by
  unfold tailWord_1981645
  simp only [CollatzResearch.WordTrace]
  refine ⟨72276530905846077866682389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48184353937230718577788259 72276530905846077866682389)
  ·
    refine ⟨3387962386211534900000737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72276530905846077866682389 3387962386211534900000737)
    ·
      refine ⟨2540971789658651175000553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3387962386211534900000737 2540971789658651175000553)
      ·
        refine ⟨1905728842243988381250415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2540971789658651175000553 1905728842243988381250415)
        ·
          refine ⟨2858593263365982571875623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1905728842243988381250415 2858593263365982571875623)
          ·
            refine ⟨4287889895048973857813435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858593263365982571875623 4287889895048973857813435)
            ·
              refine ⟨6431834842573460786720153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287889895048973857813435 6431834842573460786720153)
              ·
                refine ⟨4823876131930095590040115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6431834842573460786720153 4823876131930095590040115)
                ·
                  refine ⟨7235814197895143385060173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4823876131930095590040115 7235814197895143385060173)
                  ·
                    refine ⟨2713430324210678769397565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7235814197895143385060173 2713430324210678769397565)
                    ·
                      refine ⟨1017536371579004538524087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2713430324210678769397565 1017536371579004538524087)
                      ·
                        rfl

theorem cell23_1981645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1981645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981645 prefixEnd_1981645 := by exact prefixLift 1981645
  have htrace : WordTrace (prefixWord ++ tailWord_1981645) baseStart_1981645 baseEnd_1981645 := by
    simpa [prefixWord, tailWord_1981645, baseEnd_1981645] using wordTrace_append hprefix tailTrace_1981645
  have hstable : (prefixWord ++ tailWord_1981645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981645).length < 2 ^ (prefixWord ++ tailWord_1981645).sum := by decide
  have hdescent : baseEnd_1981645 < baseStart_1981645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981647 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 4]
def baseStart_1981647 : Nat := 118140960795 + 1981647 * 2 ^ 59
def prefixEnd_1981647 : Nat := 4983230072969 + 3 ^ 40 * 1981647 * 2
def baseEnd_1981647 : Nat := 1017537398540313530699077

theorem tailTrace_1981647 : CollatzResearch.WordTrace tailWord_1981647 prefixEnd_1981647 1017537398540313530699077 := by
  unfold tailWord_1981647
  simp only [CollatzResearch.WordTrace]
  refine ⟨72276603851838832208255195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48184402567892554805503463 72276603851838832208255195)
  ·
    refine ⟨108414905777758248312382793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72276603851838832208255195 108414905777758248312382793)
    ·
      refine ⟨81311179333318686234287095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108414905777758248312382793 81311179333318686234287095)
      ·
        refine ⟨121966768999978029351430643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81311179333318686234287095 121966768999978029351430643)
        ·
          refine ⟨182950153499967044027145965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121966768999978029351430643 182950153499967044027145965)
          ·
            refine ⟨68606307562487641510179737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182950153499967044027145965 68606307562487641510179737)
            ·
              refine ⟨51454730671865731132634803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68606307562487641510179737 51454730671865731132634803)
              ·
                refine ⟨77182096007798596698952205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51454730671865731132634803 77182096007798596698952205)
                ·
                  refine ⟨28943286002924473762107077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77182096007798596698952205 28943286002924473762107077)
                  ·
                    refine ⟨5426866125548338830395077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28943286002924473762107077 5426866125548338830395077)
                    ·
                      refine ⟨1017537398540313530699077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5426866125548338830395077 1017537398540313530699077)
                      ·
                        rfl

theorem cell23_1981647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_1981647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981647 prefixEnd_1981647 := by exact prefixLift 1981647
  have htrace : WordTrace (prefixWord ++ tailWord_1981647) baseStart_1981647 baseEnd_1981647 := by
    simpa [prefixWord, tailWord_1981647, baseEnd_1981647] using wordTrace_append hprefix tailTrace_1981647
  have hstable : (prefixWord ++ tailWord_1981647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981647).length < 2 ^ (prefixWord ++ tailWord_1981647).sum := by decide
  have hdescent : baseEnd_1981647 < baseStart_1981647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981668 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 2, 2, 2]
def baseStart_1981668 : Nat := 118140960795 + 1981668 * 2 ^ 59
def prefixEnd_1981668 : Nat := 4983230072969 + 3 ^ 40 * 1981668 * 2
def baseEnd_1981668 : Nat := 1017548181634057948536481

theorem tailTrace_1981668 : CollatzResearch.WordTrace tailWord_1981668 prefixEnd_1981668 1017548181634057948536481 := by
  unfold tailWord_1981668
  simp only [CollatzResearch.WordTrace]
  refine ⟨36138684892381376397384829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48184913189841835196513105 36138684892381376397384829)
  ·
    refine ⟨13552006834643016149019311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36138684892381376397384829 13552006834643016149019311)
    ·
      refine ⟨20328010251964524223528967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13552006834643016149019311 20328010251964524223528967)
      ·
        refine ⟨30492015377946786335293451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20328010251964524223528967 30492015377946786335293451)
        ·
          refine ⟨45738023066920179502940177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30492015377946786335293451 45738023066920179502940177)
          ·
            refine ⟨34303517300190134627205133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45738023066920179502940177 34303517300190134627205133)
            ·
              refine ⟨12863818987571300485201925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34303517300190134627205133 12863818987571300485201925)
              ·
                refine ⟨2411966060169618840975361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12863818987571300485201925 2411966060169618840975361)
                ·
                  refine ⟨1808974545127214130731521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2411966060169618840975361 1808974545127214130731521)
                  ·
                    refine ⟨1356730908845410598048641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1808974545127214130731521 1356730908845410598048641)
                    ·
                      refine ⟨1017548181634057948536481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356730908845410598048641 1017548181634057948536481)
                      ·
                        rfl

theorem cell23_1981668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_1981668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981668 prefixEnd_1981668 := by exact prefixLift 1981668
  have htrace : WordTrace (prefixWord ++ tailWord_1981668) baseStart_1981668 baseEnd_1981668 := by
    simpa [prefixWord, tailWord_1981668, baseEnd_1981668] using wordTrace_append hprefix tailTrace_1981668
  have hstable : (prefixWord ++ tailWord_1981668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981668).length < 2 ^ (prefixWord ++ tailWord_1981668).sum := by decide
  have hdescent : baseEnd_1981668 < baseStart_1981668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981687 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 3, 7]
def baseStart_1981687 : Nat := 118140960795 + 1981687 * 2 ^ 59
def prefixEnd_1981687 : Nat := 4983230072969 + 3 ^ 40 * 1981687 * 2
def baseEnd_1981687 : Nat := 339185979255497791399631

theorem tailTrace_1981687 : CollatzResearch.WordTrace tailWord_1981687 prefixEnd_1981687 339185979255497791399631 := by
  unfold tailWord_1981687
  simp only [CollatzResearch.WordTrace]
  refine ⟨72278062771693919039711315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48185375181129279359807543 72278062771693919039711315)
  ·
    refine ⟨108417094157540878559566973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72278062771693919039711315 108417094157540878559566973)
    ·
      refine ⟨40656410309077829459837615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108417094157540878559566973 40656410309077829459837615)
      ·
        refine ⟨60984615463616744189756423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40656410309077829459837615 60984615463616744189756423)
        ·
          refine ⟨91476923195425116284634635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60984615463616744189756423 91476923195425116284634635)
          ·
            refine ⟨137215384793137674426951953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91476923195425116284634635 137215384793137674426951953)
            ·
              refine ⟨102911538594853255820213965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137215384793137674426951953 102911538594853255820213965)
              ·
                refine ⟨38591826973069970932580237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102911538594853255820213965 38591826973069970932580237)
                ·
                  refine ⟨14471935114901239099717589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38591826973069970932580237 14471935114901239099717589)
                  ·
                    refine ⟨339185979255497791399631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14471935114901239099717589 339185979255497791399631)
                    ·
                      rfl

theorem cell23_1981687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_1981687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981687 prefixEnd_1981687 := by exact prefixLift 1981687
  have htrace : WordTrace (prefixWord ++ tailWord_1981687) baseStart_1981687 baseEnd_1981687 := by
    simpa [prefixWord, tailWord_1981687, baseEnd_1981687] using wordTrace_append hprefix tailTrace_1981687
  have hstable : (prefixWord ++ tailWord_1981687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981687).length < 2 ^ (prefixWord ++ tailWord_1981687).sum := by decide
  have hdescent : baseEnd_1981687 < baseStart_1981687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981744 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 3]
def baseStart_1981744 : Nat := 118140960795 + 1981744 * 2 ^ 59
def prefixEnd_1981744 : Nat := 4983230072969 + 3 ^ 40 * 1981744 * 2
def baseEnd_1981744 : Nat := 1017587206163799651186131

theorem tailTrace_1981744 : CollatzResearch.WordTrace tailWord_1981744 prefixEnd_1981744 1017587206163799651186131 := by
  unfold tailWord_1981744
  simp only [CollatzResearch.WordTrace]
  refine ⟨36140070866243708887268143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48186761154991611849690857 36140070866243708887268143)
  ·
    refine ⟨54210106299365563330902215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36140070866243708887268143 54210106299365563330902215)
    ·
      refine ⟨81315159449048344996353323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54210106299365563330902215 81315159449048344996353323)
      ·
        refine ⟨121972739173572517494529985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81315159449048344996353323 121972739173572517494529985)
        ·
          refine ⟨91479554380179388120897489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121972739173572517494529985 91479554380179388120897489)
          ·
            refine ⟨68609665785134541090673117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91479554380179388120897489 68609665785134541090673117)
            ·
              refine ⟨25728624669425452909002419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68609665785134541090673117 25728624669425452909002419)
              ·
                refine ⟨38592937004138179363503629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25728624669425452909002419 38592937004138179363503629)
                ·
                  refine ⟨14472351376551817261313861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38592937004138179363503629 14472351376551817261313861)
                  ·
                    refine ⟨2713565883103465736496349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14472351376551817261313861 2713565883103465736496349)
                    ·
                      refine ⟨1017587206163799651186131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2713565883103465736496349 1017587206163799651186131)
                      ·
                        rfl

theorem cell23_1981744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 3].length) (baseStart_1981744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981744 prefixEnd_1981744 := by exact prefixLift 1981744
  have htrace : WordTrace (prefixWord ++ tailWord_1981744) baseStart_1981744 baseEnd_1981744 := by
    simpa [prefixWord, tailWord_1981744, baseEnd_1981744] using wordTrace_append hprefix tailTrace_1981744
  have hstable : (prefixWord ++ tailWord_1981744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981744).length < 2 ^ (prefixWord ++ tailWord_1981744).sum := by decide
  have hdescent : baseEnd_1981744 < baseStart_1981744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981754 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_1981754 : Nat := 118140960795 + 1981754 * 2 ^ 59
def prefixEnd_1981754 : Nat := 4983230072969 + 3 ^ 40 * 1981754 * 2
def baseEnd_1981754 : Nat := 1017592340970344612061085

theorem tailTrace_1981754 : CollatzResearch.WordTrace tailWord_1981754 prefixEnd_1981754 1017592340970344612061085 := by
  unfold tailWord_1981754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18070126615612797370600079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48187004308300792988266877 18070126615612797370600079)
  ·
    refine ⟨27105189923419196055900119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18070126615612797370600079 27105189923419196055900119)
    ·
      refine ⟨40657784885128794083850179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27105189923419196055900119 40657784885128794083850179)
      ·
        refine ⟨60986677327693191125775269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40657784885128794083850179 60986677327693191125775269)
        ·
          refine ⟨11435001998942473336082863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60986677327693191125775269 11435001998942473336082863)
          ·
            refine ⟨17152502998413710004124295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11435001998942473336082863 17152502998413710004124295)
            ·
              refine ⟨25728754497620565006186443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17152502998413710004124295 25728754497620565006186443)
              ·
                refine ⟨38593131746430847509279665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25728754497620565006186443 38593131746430847509279665)
                ·
                  refine ⟨28944848809823135631959749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38593131746430847509279665 28944848809823135631959749)
                  ·
                    refine ⟨5427159151841837930992453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28944848809823135631959749 5427159151841837930992453)
                    ·
                      refine ⟨1017592340970344612061085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5427159151841837930992453 1017592340970344612061085)
                      ·
                        rfl

theorem cell23_1981754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_1981754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981754 prefixEnd_1981754 := by exact prefixLift 1981754
  have htrace : WordTrace (prefixWord ++ tailWord_1981754) baseStart_1981754 baseEnd_1981754 := by
    simpa [prefixWord, tailWord_1981754, baseEnd_1981754] using wordTrace_append hprefix tailTrace_1981754
  have hstable : (prefixWord ++ tailWord_1981754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981754).length < 2 ^ (prefixWord ++ tailWord_1981754).sum := by decide
  have hdescent : baseEnd_1981754 < baseStart_1981754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981782 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1981782 : Nat := 118140960795 + 1981782 * 2 ^ 59
def prefixEnd_1981782 : Nat := 4983230072969 + 3 ^ 40 * 1981782 * 2
def baseEnd_1981782 : Nat := 1017606718428670502510957

theorem tailTrace_1981782 : CollatzResearch.WordTrace tailWord_1981782 prefixEnd_1981782 1017606718428670502510957 := by
  unfold tailWord_1981782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4517595481646859391526225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48187685137566500176279733 4517595481646859391526225)
  ·
    refine ⟨3388196611235144543644669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4517595481646859391526225 3388196611235144543644669)
    ·
      refine ⟨1270573729213179203866751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3388196611235144543644669 1270573729213179203866751)
      ·
        refine ⟨1905860593819768805800127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1270573729213179203866751 1905860593819768805800127)
        ·
          refine ⟨2858790890729653208700191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1905860593819768805800127 2858790890729653208700191)
          ·
            refine ⟨4288186336094479813050287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858790890729653208700191 4288186336094479813050287)
            ·
              refine ⟨6432279504141719719575431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288186336094479813050287 6432279504141719719575431)
              ·
                refine ⟨9648419256212579579363147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6432279504141719719575431 9648419256212579579363147)
                ·
                  refine ⟨14472628884318869369044721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9648419256212579579363147 14472628884318869369044721)
                  ·
                    refine ⟨10854471663239152026783541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14472628884318869369044721 10854471663239152026783541)
                    ·
                      refine ⟨1017606718428670502510957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10854471663239152026783541 1017606718428670502510957)
                      ·
                        rfl

theorem cell23_1981782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1981782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981782 prefixEnd_1981782 := by exact prefixLift 1981782
  have htrace : WordTrace (prefixWord ++ tailWord_1981782) baseStart_1981782 baseEnd_1981782 := by
    simpa [prefixWord, tailWord_1981782, baseEnd_1981782] using wordTrace_append hprefix tailTrace_1981782
  have hstable : (prefixWord ++ tailWord_1981782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981782).length < 2 ^ (prefixWord ++ tailWord_1981782).sum := by decide
  have hdescent : baseEnd_1981782 < baseStart_1981782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981801 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 1, 5, 2]
def baseStart_1981801 : Nat := 118140960795 + 1981801 * 2 ^ 59
def prefixEnd_1981801 : Nat := 4983230072969 + 3 ^ 40 * 1981801 * 2
def baseEnd_1981801 : Nat := 1017616474561105928173369

theorem tailTrace_1981801 : CollatzResearch.WordTrace tailWord_1981801 prefixEnd_1981801 1017616474561105928173369 := by
  unfold tailWord_1981801
  simp only [CollatzResearch.WordTrace]
  refine ⟨72282220693280916509361257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48188147128853944339574171 72282220693280916509361257)
  ·
    refine ⟨54211665519960687382020943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72282220693280916509361257 54211665519960687382020943)
    ·
      refine ⟨81317498279941031073031415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54211665519960687382020943 81317498279941031073031415)
      ·
        refine ⟨121976247419911546609547123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81317498279941031073031415 121976247419911546609547123)
        ·
          refine ⟨182964371129867319914320685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121976247419911546609547123 182964371129867319914320685)
          ·
            refine ⟨68611639173700244967870257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182964371129867319914320685 68611639173700244967870257)
            ·
              refine ⟨51458729380275183725902693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68611639173700244967870257 51458729380275183725902693)
              ·
                refine ⟨9648511758801596948606755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51458729380275183725902693 9648511758801596948606755)
                ·
                  refine ⟨14472767638202395422910133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9648511758801596948606755 14472767638202395422910133)
                  ·
                    refine ⟨1356821966081474570897825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14472767638202395422910133 1356821966081474570897825)
                    ·
                      refine ⟨1017616474561105928173369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356821966081474570897825 1017616474561105928173369)
                      ·
                        rfl

theorem cell23_1981801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 5, 2].length) (baseStart_1981801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981801 prefixEnd_1981801 := by exact prefixLift 1981801
  have htrace : WordTrace (prefixWord ++ tailWord_1981801) baseStart_1981801 baseEnd_1981801 := by
    simpa [prefixWord, tailWord_1981801, baseEnd_1981801] using wordTrace_append hprefix tailTrace_1981801
  have hstable : (prefixWord ++ tailWord_1981801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981801).length < 2 ^ (prefixWord ++ tailWord_1981801).sum := by decide
  have hdescent : baseEnd_1981801 < baseStart_1981801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981858 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_1981858 : Nat := 118140960795 + 1981858 * 2 ^ 59
def prefixEnd_1981858 : Nat := 4983230072969 + 3 ^ 40 * 1981858 * 2
def baseEnd_1981858 : Nat := 339215247652804068386869

theorem tailTrace_1981858 : CollatzResearch.WordTrace tailWord_1981858 prefixEnd_1981858 339215247652804068386869 := by
  unfold tailWord_1981858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18071074913518603811046557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48189533102716276829457485 18071074913518603811046557)
  ·
    refine ⟨6776653092569476429142459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18071074913518603811046557 6776653092569476429142459)
    ·
      refine ⟨10164979638854214643713689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6776653092569476429142459 10164979638854214643713689)
      ·
        refine ⟨7623734729140660982785267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10164979638854214643713689 7623734729140660982785267)
        ·
          refine ⟨11435602093710991474177901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7623734729140660982785267 11435602093710991474177901)
          ·
            refine ⟨4288350785141621802816713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11435602093710991474177901 4288350785141621802816713)
            ·
              refine ⟨3216263088856216352112535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4288350785141621802816713 3216263088856216352112535)
              ·
                refine ⟨4824394633284324528168803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216263088856216352112535 4824394633284324528168803)
                ·
                  refine ⟨7236591949926486792253205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4824394633284324528168803 7236591949926486792253205)
                  ·
                    refine ⟨339215247652804068386869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7236591949926486792253205 339215247652804068386869)
                    ·
                      rfl

theorem cell23_1981858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_1981858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981858 prefixEnd_1981858 := by exact prefixLift 1981858
  have htrace : WordTrace (prefixWord ++ tailWord_1981858) baseStart_1981858 baseEnd_1981858 := by
    simpa [prefixWord, tailWord_1981858, baseEnd_1981858] using wordTrace_append hprefix tailTrace_1981858
  have hstable : (prefixWord ++ tailWord_1981858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981858).length < 2 ^ (prefixWord ++ tailWord_1981858).sum := by decide
  have hdescent : baseEnd_1981858 < baseStart_1981858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981892 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1981892 : Nat := 118140960795 + 1981892 * 2 ^ 59
def prefixEnd_1981892 : Nat := 4983230072969 + 3 ^ 40 * 1981892 * 2
def baseEnd_1981892 : Nat := 339221067100221690711817

theorem tailTrace_1981892 : CollatzResearch.WordTrace tailWord_1981892 prefixEnd_1981892 339221067100221690711817 := by
  unfold tailWord_1981892
  simp only [CollatzResearch.WordTrace]
  refine ⟨36142769867975619525461965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48190359823967492700615953 36142769867975619525461965)
  ·
    refine ⟨13553538700490857322048237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36142769867975619525461965 13553538700490857322048237)
    ·
      refine ⟨5082577012684071495768089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13553538700490857322048237 5082577012684071495768089)
      ·
        refine ⟨3811932759513053621826067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5082577012684071495768089 3811932759513053621826067)
        ·
          refine ⟨5717899139269580432739101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3811932759513053621826067 5717899139269580432739101)
          ·
            refine ⟨2144212177226092662277163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5717899139269580432739101 2144212177226092662277163)
            ·
              refine ⟨3216318265839138993415745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144212177226092662277163 3216318265839138993415745)
              ·
                refine ⟨2412238699379354245061809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3216318265839138993415745 2412238699379354245061809)
                ·
                  refine ⟨1809179024534515683796357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2412238699379354245061809 1809179024534515683796357)
                  ·
                    refine ⟨339221067100221690711817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1809179024534515683796357 339221067100221690711817)
                    ·
                      rfl

theorem cell23_1981892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1981892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981892 prefixEnd_1981892 := by exact prefixLift 1981892
  have htrace : WordTrace (prefixWord ++ tailWord_1981892) baseStart_1981892 baseEnd_1981892 := by
    simpa [prefixWord, tailWord_1981892, baseEnd_1981892] using wordTrace_append hprefix tailTrace_1981892
  have hstable : (prefixWord ++ tailWord_1981892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981892).length < 2 ^ (prefixWord ++ tailWord_1981892).sum := by decide
  have hdescent : baseEnd_1981892 < baseStart_1981892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981933 : List Nat := [1, 5, 1, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_1981933 : Nat := 118140960795 + 1981933 * 2 ^ 59
def prefixEnd_1981933 : Nat := 4983230072969 + 3 ^ 40 * 1981933 * 2
def baseEnd_1981933 : Nat := 1017684254007499411722763

theorem tailTrace_1981933 : CollatzResearch.WordTrace tailWord_1981933 prefixEnd_1981933 1017684254007499411722763 := by
  unfold tailWord_1981933
  simp only [CollatzResearch.WordTrace]
  refine ⟨72287035128802703053166453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48191356752535135368777635 72287035128802703053166453)
  ·
    refine ⟨6776909543325253411234355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72287035128802703053166453 6776909543325253411234355)
    ·
      refine ⟨10165364314987880116851533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6776909543325253411234355 10165364314987880116851533)
      ·
        refine ⟨3812011618120455043819325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10165364314987880116851533 3812011618120455043819325)
        ·
          refine ⟨1429504356795170641432247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3812011618120455043819325 1429504356795170641432247)
          ·
            refine ⟨2144256535192755962148371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429504356795170641432247 2144256535192755962148371)
            ·
              refine ⟨3216384802789133943222557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144256535192755962148371 3216384802789133943222557)
              ·
                refine ⟨1206144301045925228708459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3216384802789133943222557 1206144301045925228708459)
                ·
                  refine ⟨1809216451568887843062689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1206144301045925228708459 1809216451568887843062689)
                  ·
                    refine ⟨1356912338676665882297017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1809216451568887843062689 1356912338676665882297017)
                    ·
                      refine ⟨1017684254007499411722763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356912338676665882297017 1017684254007499411722763)
                      ·
                        rfl

theorem cell23_1981933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_1981933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981933 prefixEnd_1981933 := by exact prefixLift 1981933
  have htrace : WordTrace (prefixWord ++ tailWord_1981933) baseStart_1981933 baseEnd_1981933 := by
    simpa [prefixWord, tailWord_1981933, baseEnd_1981933] using wordTrace_append hprefix tailTrace_1981933
  have hstable : (prefixWord ++ tailWord_1981933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981933).length < 2 ^ (prefixWord ++ tailWord_1981933).sum := by decide
  have hdescent : baseEnd_1981933 < baseStart_1981933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981942 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_1981942 : Nat := 118140960795 + 1981942 * 2 ^ 59
def prefixEnd_1981942 : Nat := 4983230072969 + 3 ^ 40 * 1981942 * 2
def baseEnd_1981942 : Nat := 1017688875333389876510221

theorem tailTrace_1981942 : CollatzResearch.WordTrace tailWord_1981942 prefixEnd_1981942 1017688875333389876510221 := by
  unfold tailWord_1981942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4517960211610631099390255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48191575590513398393496053 4517960211610631099390255)
  ·
    refine ⟨6776940317415946649085383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4517960211610631099390255 6776940317415946649085383)
    ·
      refine ⟨10165410476123919973628075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6776940317415946649085383 10165410476123919973628075)
      ·
        refine ⟨15248115714185879960442113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10165410476123919973628075 15248115714185879960442113)
        ·
          refine ⟨11436086785639409970331585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15248115714185879960442113 11436086785639409970331585)
          ·
            refine ⟨8577065089229557477748689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11436086785639409970331585 8577065089229557477748689)
            ·
              refine ⟨6432798816922168108311517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8577065089229557477748689 6432798816922168108311517)
              ·
                refine ⟨2412299556345813040616819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6432798816922168108311517 2412299556345813040616819)
                ·
                  refine ⟨3618449334518719560925229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412299556345813040616819 3618449334518719560925229)
                  ·
                    refine ⟨1356918500444519835346961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3618449334518719560925229 1356918500444519835346961)
                    ·
                      refine ⟨1017688875333389876510221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356918500444519835346961 1017688875333389876510221)
                      ·
                        rfl

theorem cell23_1981942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_1981942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981942 prefixEnd_1981942 := by exact prefixLift 1981942
  have htrace : WordTrace (prefixWord ++ tailWord_1981942) baseStart_1981942 baseEnd_1981942 := by
    simpa [prefixWord, tailWord_1981942, baseEnd_1981942] using wordTrace_append hprefix tailTrace_1981942
  have hstable : (prefixWord ++ tailWord_1981942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981942).length < 2 ^ (prefixWord ++ tailWord_1981942).sum := by decide
  have hdescent : baseEnd_1981942 < baseStart_1981942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981951 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 4]
def baseStart_1981951 : Nat := 118140960795 + 1981951 * 2 ^ 59
def prefixEnd_1981951 : Nat := 4983230072969 + 3 ^ 40 * 1981951 * 2
def baseEnd_1981951 : Nat := 1017693496659280341297679

theorem tailTrace_1981951 : CollatzResearch.WordTrace tailWord_1981951 prefixEnd_1981951 1017693496659280341297679 := by
  unfold tailWord_1981951
  simp only [CollatzResearch.WordTrace]
  refine ⟨72287691642737492127321707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48191794428491661418214471 72287691642737492127321707)
  ·
    refine ⟨108431537464106238190982561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72287691642737492127321707 108431537464106238190982561)
    ·
      refine ⟨81323653098079678643236921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108431537464106238190982561 81323653098079678643236921)
      ·
        refine ⟨60992739823559758982427691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81323653098079678643236921 60992739823559758982427691)
        ·
          refine ⟨91489109735339638473641537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60992739823559758982427691 91489109735339638473641537)
          ·
            refine ⟨68616832301504728855231153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91489109735339638473641537 68616832301504728855231153)
            ·
              refine ⟨51462624226128546641423365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68616832301504728855231153 51462624226128546641423365)
              ·
                refine ⟨9649242042399102495266881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51462624226128546641423365 9649242042399102495266881)
                ·
                  refine ⟨7236931531799326871450161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9649242042399102495266881 7236931531799326871450161)
                  ·
                    refine ⟨5427698648849495153587621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7236931531799326871450161 5427698648849495153587621)
                    ·
                      refine ⟨1017693496659280341297679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5427698648849495153587621 1017693496659280341297679)
                      ·
                        rfl

theorem cell23_1981951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_1981951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981951 prefixEnd_1981951 := by exact prefixLift 1981951
  have htrace : WordTrace (prefixWord ++ tailWord_1981951) baseStart_1981951 baseEnd_1981951 := by
    simpa [prefixWord, tailWord_1981951, baseEnd_1981951] using wordTrace_append hprefix tailTrace_1981951
  have hstable : (prefixWord ++ tailWord_1981951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981951).length < 2 ^ (prefixWord ++ tailWord_1981951).sum := by decide
  have hdescent : baseEnd_1981951 < baseStart_1981951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981966 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3]
def baseStart_1981966 : Nat := 118140960795 + 1981966 * 2 ^ 59
def prefixEnd_1981966 : Nat := 4983230072969 + 3 ^ 40 * 1981966 * 2
def baseEnd_1981966 : Nat := 1017701198869097782610111

theorem tailTrace_1981966 : CollatzResearch.WordTrace tailWord_1981966 prefixEnd_1981966 1017701198869097782610111 := by
  unfold tailWord_1981966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036029842210393711139719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48192159158455433126078501 9036029842210393711139719)
  ·
    refine ⟨13554044763315590566709579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9036029842210393711139719 13554044763315590566709579)
    ·
      refine ⟨20331067144973385850064369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13554044763315590566709579 20331067144973385850064369)
      ·
        refine ⟨15248300358730039387548277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20331067144973385850064369 15248300358730039387548277)
        ·
          refine ⟨1429528158630941192582651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15248300358730039387548277 1429528158630941192582651)
          ·
            refine ⟨2144292237946411788873977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429528158630941192582651 2144292237946411788873977)
            ·
              refine ⟨1608219178459808841655483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2144292237946411788873977 1608219178459808841655483)
              ·
                refine ⟨2412328767689713262483225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608219178459808841655483 2412328767689713262483225)
                ·
                  refine ⟨1809246575767284946862419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2412328767689713262483225 1809246575767284946862419)
                  ·
                    refine ⟨2713869863650927420293629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1809246575767284946862419 2713869863650927420293629)
                    ·
                      refine ⟨1017701198869097782610111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2713869863650927420293629 1017701198869097782610111)
                      ·
                        rfl

theorem cell23_1981966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_1981966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1981966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1981966 prefixEnd_1981966 := by exact prefixLift 1981966
  have htrace : WordTrace (prefixWord ++ tailWord_1981966) baseStart_1981966 baseEnd_1981966 := by
    simpa [prefixWord, tailWord_1981966, baseEnd_1981966] using wordTrace_append hprefix tailTrace_1981966
  have hstable : (prefixWord ++ tailWord_1981966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981966).length < 2 ^ (prefixWord ++ tailWord_1981966).sum := by decide
  have hdescent : baseEnd_1981966 < baseStart_1981966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982006 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_1982006 : Nat := 118140960795 + 1982006 * 2 ^ 59
def prefixEnd_1982006 : Nat := 4983230072969 + 3 ^ 40 * 1982006 * 2
def baseEnd_1982006 : Nat := 1017721738095277626109927

theorem tailTrace_1982006 : CollatzResearch.WordTrace tailWord_1982006 prefixEnd_1982006 1017721738095277626109927 := by
  unfold tailWord_1982006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4518106103596139782535867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48193131771692157680382581 4518106103596139782535867)
  ·
    refine ⟨6777159155394209673803801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4518106103596139782535867 6777159155394209673803801)
    ·
      refine ⟨5082869366545657255352851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6777159155394209673803801 5082869366545657255352851)
      ·
        refine ⟨7624304049818485883029277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5082869366545657255352851 7624304049818485883029277)
        ·
          refine ⟨2859114018681932206135979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7624304049818485883029277 2859114018681932206135979)
          ·
            refine ⟨4288671028022898309203969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2859114018681932206135979 4288671028022898309203969)
            ·
              refine ⟨3216503271017173731902977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4288671028022898309203969 3216503271017173731902977)
              ·
                refine ⟨2412377453262880298927233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3216503271017173731902977 2412377453262880298927233)
                ·
                  refine ⟨1809283089947160224195425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2412377453262880298927233 1809283089947160224195425)
                  ·
                    refine ⟨1356962317460370168146569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1809283089947160224195425 1356962317460370168146569)
                    ·
                      refine ⟨1017721738095277626109927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1356962317460370168146569 1017721738095277626109927)
                      ·
                        rfl

theorem cell23_1982006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_1982006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982006 prefixEnd_1982006 := by exact prefixLift 1982006
  have htrace : WordTrace (prefixWord ++ tailWord_1982006) baseStart_1982006 baseEnd_1982006 := by
    simpa [prefixWord, tailWord_1982006, baseEnd_1982006] using wordTrace_append hprefix tailTrace_1982006
  have hstable : (prefixWord ++ tailWord_1982006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982006).length < 2 ^ (prefixWord ++ tailWord_1982006).sum := by decide
  have hdescent : baseEnd_1982006 < baseStart_1982006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982008 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 2, 5]
def baseStart_1982008 : Nat := 118140960795 + 1982008 * 2 ^ 59
def prefixEnd_1982008 : Nat := 4983230072969 + 3 ^ 40 * 1982008 * 2
def baseEnd_1982008 : Nat := 339240921685528872761639

theorem tailTrace_1982008 : CollatzResearch.WordTrace tailWord_1982008 prefixEnd_1982008 339240921685528872761639 := by
  unfold tailWord_1982008
  simp only [CollatzResearch.WordTrace]
  refine ⟨36144885301765495431073339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48193180402353993908097785 36144885301765495431073339)
  ·
    refine ⟨54217327952648243146610009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36144885301765495431073339 54217327952648243146610009)
    ·
      refine ⟨40662995964486182359957507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54217327952648243146610009 40662995964486182359957507)
      ·
        refine ⟨60994493946729273539936261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40662995964486182359957507 60994493946729273539936261)
        ·
          refine ⟨11436467615011738788738049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60994493946729273539936261 11436467615011738788738049)
          ·
            refine ⟨8577350711258804091553537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11436467615011738788738049 8577350711258804091553537)
            ·
              refine ⟨6433013033444103068665153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8577350711258804091553537 6433013033444103068665153)
              ·
                refine ⟨4824759775083077301498865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6433013033444103068665153 4824759775083077301498865)
                ·
                  refine ⟨3618569831312307976124149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4824759775083077301498865 3618569831312307976124149)
                  ·
                    refine ⟨339240921685528872761639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3618569831312307976124149 339240921685528872761639)
                    ·
                      rfl

theorem cell23_1982008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_1982008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982008 prefixEnd_1982008 := by exact prefixLift 1982008
  have htrace : WordTrace (prefixWord ++ tailWord_1982008) baseStart_1982008 baseEnd_1982008 := by
    simpa [prefixWord, tailWord_1982008, baseEnd_1982008] using wordTrace_append hprefix tailTrace_1982008
  have hstable : (prefixWord ++ tailWord_1982008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982008).length < 2 ^ (prefixWord ++ tailWord_1982008).sum := by decide
  have hdescent : baseEnd_1982008 < baseStart_1982008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982041 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_1982041 : Nat := 118140960795 + 1982041 * 2 ^ 59
def prefixEnd_1982041 : Nat := 4983230072969 + 3 ^ 40 * 1982041 * 2
def baseEnd_1982041 : Nat := 1017739709918184989172265

theorem tailTrace_1982041 : CollatzResearch.WordTrace tailWord_1982041 prefixEnd_1982041 1017739709918184989172265 := by
  unfold tailWord_1982041
  simp only [CollatzResearch.WordTrace]
  refine ⟨72290974212411437498097977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48193982808274291665398651 72290974212411437498097977)
  ·
    refine ⟨54218230659308578123573483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72290974212411437498097977 54218230659308578123573483)
    ·
      refine ⟨81327345988962867185360225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54218230659308578123573483 81327345988962867185360225)
      ·
        refine ⟨60995509491722150389020169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81327345988962867185360225 60995509491722150389020169)
        ·
          refine ⟨45746632118791612791765127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60995509491722150389020169 45746632118791612791765127)
          ·
            refine ⟨68619948178187419187647691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45746632118791612791765127 68619948178187419187647691)
            ·
              refine ⟨102929922267281128781471537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68619948178187419187647691 102929922267281128781471537)
              ·
                refine ⟨77197441700460846586103653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102929922267281128781471537 77197441700460846586103653)
                ·
                  refine ⟨14474520318836408734894435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77197441700460846586103653 14474520318836408734894435)
                  ·
                    refine ⟨21711780478254613102341653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14474520318836408734894435 21711780478254613102341653)
                    ·
                      refine ⟨1017739709918184989172265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21711780478254613102341653 1017739709918184989172265)
                      ·
                        rfl

theorem cell23_1982041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_1982041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982041 prefixEnd_1982041 := by exact prefixLift 1982041
  have htrace : WordTrace (prefixWord ++ tailWord_1982041) baseStart_1982041 baseEnd_1982041 := by
    simpa [prefixWord, tailWord_1982041, baseEnd_1982041] using wordTrace_append hprefix tailTrace_1982041
  have hstable : (prefixWord ++ tailWord_1982041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982041).length < 2 ^ (prefixWord ++ tailWord_1982041).sum := by decide
  have hdescent : baseEnd_1982041 < baseStart_1982041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982058 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1982058 : Nat := 118140960795 + 1982058 * 2 ^ 59
def prefixEnd_1982058 : Nat := 4983230072969 + 3 ^ 40 * 1982058 * 2
def baseEnd_1982058 : Nat := 1017748439089311422659687

theorem tailTrace_1982058 : CollatzResearch.WordTrace tailWord_1982058 prefixEnd_1982058 1017748439089311422659687 := by
  unfold tailWord_1982058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18072898563337462350366707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48194396168899899600977885 18072898563337462350366707)
  ·
    refine ⟨27109347845006193525550061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18072898563337462350366707 27109347845006193525550061)
    ·
      refine ⟨10166005441877322572081273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27109347845006193525550061 10166005441877322572081273)
      ·
        refine ⟨7624504081407991929060955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10166005441877322572081273 7624504081407991929060955)
        ·
          refine ⟨11436756122111987893591433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624504081407991929060955 11436756122111987893591433)
          ·
            refine ⟨8577567091583990920193575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11436756122111987893591433 8577567091583990920193575)
            ·
              refine ⟨12866350637375986380290363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8577567091583990920193575 12866350637375986380290363)
              ·
                refine ⟨19299525956063979570435545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12866350637375986380290363 19299525956063979570435545)
                ·
                  refine ⟨14474644467047984677826659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19299525956063979570435545 14474644467047984677826659)
                  ·
                    refine ⟨21711966700571977016739989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14474644467047984677826659 21711966700571977016739989)
                    ·
                      refine ⟨1017748439089311422659687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21711966700571977016739989 1017748439089311422659687)
                      ·
                        rfl

theorem cell23_1982058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1982058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982058 prefixEnd_1982058 := by exact prefixLift 1982058
  have htrace : WordTrace (prefixWord ++ tailWord_1982058) baseStart_1982058 baseEnd_1982058 := by
    simpa [prefixWord, tailWord_1982058, baseEnd_1982058] using wordTrace_append hprefix tailTrace_1982058
  have hstable : (prefixWord ++ tailWord_1982058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982058).length < 2 ^ (prefixWord ++ tailWord_1982058).sum := by decide
  have hdescent : baseEnd_1982058 < baseStart_1982058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982085 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 6]
def baseStart_1982085 : Nat := 118140960795 + 1982085 * 2 ^ 59
def prefixEnd_1982085 : Nat := 4983230072969 + 3 ^ 40 * 1982085 * 2
def baseEnd_1982085 : Nat := 113084700340775868558007

theorem tailTrace_1982085 : CollatzResearch.WordTrace tailWord_1982085 prefixEnd_1982085 113084700340775868558007 := by
  unfold tailWord_1982085
  simp only [CollatzResearch.WordTrace]
  refine ⟨72292579024252033012699709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48195052682834688675133139 72292579024252033012699709)
  ·
    refine ⟨27109717134094512379762391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72292579024252033012699709 27109717134094512379762391)
    ·
      refine ⟨40664575701141768569643587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27109717134094512379762391 40664575701141768569643587)
      ·
        refine ⟨60996863551712652854465381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40664575701141768569643587 60996863551712652854465381)
        ·
          refine ⟨11436911915946122410212259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60996863551712652854465381 11436911915946122410212259)
          ·
            refine ⟨17155367873919183615318389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11436911915946122410212259 17155367873919183615318389)
            ·
              refine ⟨1608315738179923463936099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17155367873919183615318389 1608315738179923463936099)
              ·
                refine ⟨2412473607269885195904149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608315738179923463936099 2412473607269885195904149)
                ·
                  refine ⟨113084700340775868558007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2412473607269885195904149 113084700340775868558007)
                  ·
                    rfl

theorem cell23_1982085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_1982085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982085 prefixEnd_1982085 := by exact prefixLift 1982085
  have htrace : WordTrace (prefixWord ++ tailWord_1982085) baseStart_1982085 baseEnd_1982085 := by
    simpa [prefixWord, tailWord_1982085, baseEnd_1982085] using wordTrace_append hprefix tailTrace_1982085
  have hstable : (prefixWord ++ tailWord_1982085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982085).length < 2 ^ (prefixWord ++ tailWord_1982085).sum := by decide
  have hdescent : baseEnd_1982085 < baseStart_1982085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982152 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 5, 2, 2]
def baseStart_1982152 : Nat := 118140960795 + 1982152 * 2 ^ 59
def prefixEnd_1982152 : Nat := 4983230072969 + 3 ^ 40 * 1982152 * 2
def baseEnd_1982152 : Nat := 1017796706270834054884255

theorem tailTrace_1982152 : CollatzResearch.WordTrace tailWord_1982152 prefixEnd_1982152 1017796706270834054884255 := by
  unfold tailWord_1982152
  simp only [CollatzResearch.WordTrace]
  refine ⟨36147511357504651727694355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48196681810006202303592473 36147511357504651727694355)
  ·
    refine ⟨54221267036256977591541533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36147511357504651727694355 54221267036256977591541533)
    ·
      refine ⟨20332975138596366596828075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54221267036256977591541533 20332975138596366596828075)
      ·
        refine ⟨30499462707894549895242113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20332975138596366596828075 30499462707894549895242113)
        ·
          refine ⟨22874597030920912421431585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30499462707894549895242113 22874597030920912421431585)
          ·
            refine ⟨17155947773190684316073689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22874597030920912421431585 17155947773190684316073689)
            ·
              refine ⟨12866960829893013237055267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17155947773190684316073689 12866960829893013237055267)
              ·
                refine ⟨19300441244839519855582901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12866960829893013237055267 19300441244839519855582901)
                ·
                  refine ⟨1809416366703704986460897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19300441244839519855582901 1809416366703704986460897)
                  ·
                    refine ⟨1357062275027778739845673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1809416366703704986460897 1357062275027778739845673)
                    ·
                      refine ⟨1017796706270834054884255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1357062275027778739845673 1017796706270834054884255)
                      ·
                        rfl

theorem cell23_1982152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_1982152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982152 prefixEnd_1982152 := by exact prefixLift 1982152
  have htrace : WordTrace (prefixWord ++ tailWord_1982152) baseStart_1982152 baseEnd_1982152 := by
    simpa [prefixWord, tailWord_1982152, baseEnd_1982152] using wordTrace_append hprefix tailTrace_1982152
  have hstable : (prefixWord ++ tailWord_1982152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982152).length < 2 ^ (prefixWord ++ tailWord_1982152).sum := by decide
  have hdescent : baseEnd_1982152 < baseStart_1982152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982158 : List Nat := [4, 1, 1, 1, 3, 1, 1, 11]
def baseStart_1982158 : Nat := 118140960795 + 1982158 * 2 ^ 59
def prefixEnd_1982158 : Nat := 4983230072969 + 3 ^ 40 * 1982158 * 2
def baseEnd_1982158 : Nat := 37696288413139297459601

theorem tailTrace_1982158 : CollatzResearch.WordTrace tailWord_1982158 prefixEnd_1982158 37696288413139297459601 := by
  unfold tailWord_1982158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9036905194123445810013391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48196827701991710986738085 9036905194123445810013391)
  ·
    refine ⟨13555357791185168715020087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9036905194123445810013391 13555357791185168715020087)
    ·
      refine ⟨20333036686777753072530131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13555357791185168715020087 20333036686777753072530131)
      ·
        refine ⟨30499555030166629608795197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20333036686777753072530131 30499555030166629608795197)
        ·
          refine ⟨11437333136312486103298199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30499555030166629608795197 11437333136312486103298199)
          ·
            refine ⟨17155999704468729154947299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11437333136312486103298199 17155999704468729154947299)
            ·
              refine ⟨25733999556703093732420949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17155999704468729154947299 25733999556703093732420949)
              ·
                refine ⟨37696288413139297459601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 25733999556703093732420949 37696288413139297459601)
                ·
                  rfl

theorem cell23_1982158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_1982158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982158 prefixEnd_1982158 := by exact prefixLift 1982158
  have htrace : WordTrace (prefixWord ++ tailWord_1982158) baseStart_1982158 baseEnd_1982158 := by
    simpa [prefixWord, tailWord_1982158, baseEnd_1982158] using wordTrace_append hprefix tailTrace_1982158
  have hstable : (prefixWord ++ tailWord_1982158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982158).length < 2 ^ (prefixWord ++ tailWord_1982158).sum := by decide
  have hdescent : baseEnd_1982158 < baseStart_1982158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982179 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 2, 4]
def baseStart_1982179 : Nat := 118140960795 + 1982179 * 2 ^ 59
def prefixEnd_1982179 : Nat := 4983230072969 + 3 ^ 40 * 1982179 * 2
def baseEnd_1982179 : Nat := 339270190082835149748877

theorem tailTrace_1982179 : CollatzResearch.WordTrace tailWord_1982179 prefixEnd_1982179 339270190082835149748877 := by
  unfold tailWord_1982179
  simp only [CollatzResearch.WordTrace]
  refine ⟨72296007485911487066621591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48197338323940991377747727 72296007485911487066621591)
  ·
    refine ⟨108444011228867230599932387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72296007485911487066621591 108444011228867230599932387)
    ·
      refine ⟨162666016843300845899898581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108444011228867230599932387 162666016843300845899898581)
      ·
        refine ⟨3812484769764863575778873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 162666016843300845899898581 3812484769764863575778873)
        ·
          refine ⟨2859363577323647681834155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3812484769764863575778873 2859363577323647681834155)
          ·
            refine ⟨4289045365985471522751233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2859363577323647681834155 4289045365985471522751233)
            ·
              refine ⟨3216784024489103642063425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4289045365985471522751233 3216784024489103642063425)
              ·
                refine ⟨2412588018366827731547569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3216784024489103642063425 2412588018366827731547569)
                ·
                  refine ⟨1809441013775120798660677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2412588018366827731547569 1809441013775120798660677)
                  ·
                    refine ⟨339270190082835149748877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1809441013775120798660677 339270190082835149748877)
                    ·
                      rfl

theorem cell23_1982179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 4].length) (baseStart_1982179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982179 prefixEnd_1982179 := by exact prefixLift 1982179
  have htrace : WordTrace (prefixWord ++ tailWord_1982179) baseStart_1982179 baseEnd_1982179 := by
    simpa [prefixWord, tailWord_1982179, baseEnd_1982179] using wordTrace_append hprefix tailTrace_1982179
  have hstable : (prefixWord ++ tailWord_1982179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982179).length < 2 ^ (prefixWord ++ tailWord_1982179).sum := by decide
  have hdescent : baseEnd_1982179 < baseStart_1982179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982188 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_1982188 : Nat := 118140960795 + 1982188 * 2 ^ 59
def prefixEnd_1982188 : Nat := 4983230072969 + 3 ^ 40 * 1982188 * 2
def baseEnd_1982188 : Nat := 339271730524798638011363

theorem tailTrace_1982188 : CollatzResearch.WordTrace tailWord_1982188 prefixEnd_1982188 339271730524798638011363 := by
  unfold tailWord_1982188
  simp only [CollatzResearch.WordTrace]
  refine ⟨36148167871439440801849609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48197557161919254402466145 36148167871439440801849609)
  ·
    refine ⟨27111125903579580601387207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36148167871439440801849609 27111125903579580601387207)
    ·
      refine ⟨40666688855369370902080811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27111125903579580601387207 40666688855369370902080811)
      ·
        refine ⟨61000033283054056353121217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40666688855369370902080811 61000033283054056353121217)
        ·
          refine ⟨45750024962290542264840913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61000033283054056353121217 45750024962290542264840913)
          ·
            refine ⟨34312518721717906698630685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45750024962290542264840913 34312518721717906698630685)
            ·
              refine ⟨12867194520644215011986507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34312518721717906698630685 12867194520644215011986507)
              ·
                refine ⟨19300791780966322517979761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12867194520644215011986507 19300791780966322517979761)
                ·
                  refine ⟨14475593835724741888484821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19300791780966322517979761 14475593835724741888484821)
                  ·
                    refine ⟨339271730524798638011363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14475593835724741888484821 339271730524798638011363)
                    ·
                      rfl

theorem cell23_1982188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_1982188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982188 prefixEnd_1982188 := by exact prefixLift 1982188
  have htrace : WordTrace (prefixWord ++ tailWord_1982188) baseStart_1982188 baseEnd_1982188 := by
    simpa [prefixWord, tailWord_1982188, baseEnd_1982188] using wordTrace_append hprefix tailTrace_1982188
  have hstable : (prefixWord ++ tailWord_1982188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982188).length < 2 ^ (prefixWord ++ tailWord_1982188).sum := by decide
  have hdescent : baseEnd_1982188 < baseStart_1982188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982196 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1982196 : Nat := 118140960795 + 1982196 * 2 ^ 59
def prefixEnd_1982196 : Nat := 4983230072969 + 3 ^ 40 * 1982196 * 2
def baseEnd_1982196 : Nat := 339273099806543960911351

theorem tailTrace_1982196 : CollatzResearch.WordTrace tailWord_1982196 prefixEnd_1982196 339273099806543960911351 := by
  unfold tailWord_1982196
  simp only [CollatzResearch.WordTrace]
  refine ⟨36148313763424949484995221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48197751684566599313326961 36148313763424949484995221)
  ·
    refine ⟨1694452207660544507109151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36148313763424949484995221 1694452207660544507109151)
    ·
      refine ⟨2541678311490816760663727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1694452207660544507109151 2541678311490816760663727)
      ·
        refine ⟨3812517467236225140995591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2541678311490816760663727 3812517467236225140995591)
        ·
          refine ⟨5718776200854337711493387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3812517467236225140995591 5718776200854337711493387)
          ·
            refine ⟨8578164301281506567240081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5718776200854337711493387 8578164301281506567240081)
            ·
              refine ⟨6433623225961129925430061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8578164301281506567240081 6433623225961129925430061)
              ·
                refine ⟨2412608709735423722036273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6433623225961129925430061 2412608709735423722036273)
                ·
                  refine ⟨1809456532301567791527205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2412608709735423722036273 1809456532301567791527205)
                  ·
                    refine ⟨339273099806543960911351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1809456532301567791527205 339273099806543960911351)
                    ·
                      rfl

theorem cell23_1982196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1982196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982196 prefixEnd_1982196 := by exact prefixLift 1982196
  have htrace : WordTrace (prefixWord ++ tailWord_1982196) baseStart_1982196 baseEnd_1982196 := by
    simpa [prefixWord, tailWord_1982196, baseEnd_1982196] using wordTrace_append hprefix tailTrace_1982196
  have hstable : (prefixWord ++ tailWord_1982196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982196).length < 2 ^ (prefixWord ++ tailWord_1982196).sum := by decide
  have hdescent : baseEnd_1982196 < baseStart_1982196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982214 : List Nat := [6, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_1982214 : Nat := 118140960795 + 1982214 * 2 ^ 59
def prefixEnd_1982214 : Nat := 4983230072969 + 3 ^ 40 * 1982214 * 2
def baseEnd_1982214 : Nat := 1017828542071412812308971

theorem tailTrace_1982214 : CollatzResearch.WordTrace tailWord_1982214 prefixEnd_1982214 1017828542071412812308971 := by
  unfold tailWord_1982214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2259290126274521501379553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48198189360523125362763797 2259290126274521501379553)
  ·
    refine ⟨1694467594705891126034665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2259290126274521501379553 1694467594705891126034665)
    ·
      refine ⟨1270850696029418344525999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1694467594705891126034665 1270850696029418344525999)
      ·
        refine ⟨1906276044044127516788999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1270850696029418344525999 1906276044044127516788999)
        ·
          refine ⟨2859414066066191275183499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1906276044044127516788999 2859414066066191275183499)
          ·
            refine ⟨4289121099099286912775249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2859414066066191275183499 4289121099099286912775249)
            ·
              refine ⟨3216840824324465184581437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4289121099099286912775249 3216840824324465184581437)
              ·
                refine ⟨1206315309121674444218039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3216840824324465184581437 1206315309121674444218039)
                ·
                  refine ⟨1809472963682511666327059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1206315309121674444218039 1809472963682511666327059)
                  ·
                    refine ⟨2714209445523767499490589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1809472963682511666327059 2714209445523767499490589)
                    ·
                      refine ⟨1017828542071412812308971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2714209445523767499490589 1017828542071412812308971)
                      ·
                        rfl

theorem cell23_1982214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_1982214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982214 prefixEnd_1982214 := by exact prefixLift 1982214
  have htrace : WordTrace (prefixWord ++ tailWord_1982214) baseStart_1982214 baseEnd_1982214 := by
    simpa [prefixWord, tailWord_1982214, baseEnd_1982214] using wordTrace_append hprefix tailTrace_1982214
  have hstable : (prefixWord ++ tailWord_1982214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982214).length < 2 ^ (prefixWord ++ tailWord_1982214).sum := by decide
  have hdescent : baseEnd_1982214 < baseStart_1982214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982229 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 1, 3, 2]
def baseStart_1982229 : Nat := 118140960795 + 1982229 * 2 ^ 59
def prefixEnd_1982229 : Nat := 4983230072969 + 3 ^ 40 * 1982229 * 2
def baseEnd_1982229 : Nat := 1017836244281230253621401

theorem tailTrace_1982229 : CollatzResearch.WordTrace tailWord_1982229 prefixEnd_1982229 1017836244281230253621401 := by
  unfold tailWord_1982229
  simp only [CollatzResearch.WordTrace]
  refine ⟨72297831135730345605941741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48198554090486897070627827 72297831135730345605941741)
  ·
    refine ⟨27111686675898879602228153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72297831135730345605941741 27111686675898879602228153)
    ·
      refine ⟨20333765006924159701671115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27111686675898879602228153 20333765006924159701671115)
      ·
        refine ⟨30500647510386239552506673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20333765006924159701671115 30500647510386239552506673)
        ·
          refine ⟨22875485632789679664380005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30500647510386239552506673 22875485632789679664380005)
          ·
            refine ⟨4289153556148064937071251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22875485632789679664380005 4289153556148064937071251)
            ·
              refine ⟨6433730334222097405606877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289153556148064937071251 6433730334222097405606877)
              ·
                refine ⟨2412648875333286527102579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6433730334222097405606877 2412648875333286527102579)
                ·
                  refine ⟨3618973312999929790653869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412648875333286527102579 3618973312999929790653869)
                  ·
                    refine ⟨1357114992374973671495201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3618973312999929790653869 1357114992374973671495201)
                    ·
                      refine ⟨1017836244281230253621401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1357114992374973671495201 1017836244281230253621401)
                      ·
                        rfl

theorem cell23_1982229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_1982229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982229 prefixEnd_1982229 := by exact prefixLift 1982229
  have htrace : WordTrace (prefixWord ++ tailWord_1982229) baseStart_1982229 baseEnd_1982229 := by
    simpa [prefixWord, tailWord_1982229, baseEnd_1982229] using wordTrace_append hprefix tailTrace_1982229
  have hstable : (prefixWord ++ tailWord_1982229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982229).length < 2 ^ (prefixWord ++ tailWord_1982229).sum := by decide
  have hdescent : baseEnd_1982229 < baseStart_1982229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982305 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_1982305 : Nat := 118140960795 + 1982305 * 2 ^ 59
def prefixEnd_1982305 : Nat := 4983230072969 + 3 ^ 40 * 1982305 * 2
def baseEnd_1982305 : Nat := 1017875268810971956271051

theorem tailTrace_1982305 : CollatzResearch.WordTrace tailWord_1982305 prefixEnd_1982305 1017875268810971956271051 := by
  unfold tailWord_1982305
  simp only [CollatzResearch.WordTrace]
  refine ⟨72300603083455010585708369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48200402055636673723805579 72300603083455010585708369)
  ·
    refine ⟨54225452312591257939281277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72300603083455010585708369 54225452312591257939281277)
    ·
      refine ⟨20334544617221721727230479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54225452312591257939281277 20334544617221721727230479)
      ·
        refine ⟨30501816925832582590845719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20334544617221721727230479 30501816925832582590845719)
        ·
          refine ⟨45752725388748873886268579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30501816925832582590845719 45752725388748873886268579)
          ·
            refine ⟨68629088083123310829402869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45752725388748873886268579 68629088083123310829402869)
            ·
              refine ⟨6433977007792810390256519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68629088083123310829402869 6433977007792810390256519)
              ·
                refine ⟨9650965511689215585384779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433977007792810390256519 9650965511689215585384779)
                ·
                  refine ⟨14476448267533823378077169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9650965511689215585384779 14476448267533823378077169)
                  ·
                    refine ⟨10857336200650367533557877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14476448267533823378077169 10857336200650367533557877)
                    ·
                      refine ⟨1017875268810971956271051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10857336200650367533557877 1017875268810971956271051)
                      ·
                        rfl

theorem cell23_1982305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_1982305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982305 prefixEnd_1982305 := by exact prefixLift 1982305
  have htrace : WordTrace (prefixWord ++ tailWord_1982305) baseStart_1982305 baseEnd_1982305 := by
    simpa [prefixWord, tailWord_1982305, baseEnd_1982305] using wordTrace_append hprefix tailTrace_1982305
  have hstable : (prefixWord ++ tailWord_1982305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982305).length < 2 ^ (prefixWord ++ tailWord_1982305).sum := by decide
  have hdescent : baseEnd_1982305 < baseStart_1982305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982315 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 4]
def baseStart_1982315 : Nat := 118140960795 + 1982315 * 2 ^ 59
def prefixEnd_1982315 : Nat := 4983230072969 + 3 ^ 40 * 1982315 * 2
def baseEnd_1982315 : Nat := 1017880403617516917146005

theorem tailTrace_1982315 : CollatzResearch.WordTrace tailWord_1982315 prefixEnd_1982315 1017880403617516917146005 := by
  unfold tailWord_1982315
  simp only [CollatzResearch.WordTrace]
  refine ⟨72300967813418782293572399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48200645208945854862381599 72300967813418782293572399)
  ·
    refine ⟨108451451720128173440358599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72300967813418782293572399 108451451720128173440358599)
    ·
      refine ⟨162677177580192260160537899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108451451720128173440358599 162677177580192260160537899)
      ·
        refine ⟨244015766370288390240806849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162677177580192260160537899 244015766370288390240806849)
        ·
          refine ⟨183011824777716292680605137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244015766370288390240806849 183011824777716292680605137)
          ·
            refine ⟨137258868583287219510453853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183011824777716292680605137 137258868583287219510453853)
            ·
              refine ⟨51472075718732707316420195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137258868583287219510453853 51472075718732707316420195)
              ·
                refine ⟨77208113578099060974630293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51472075718732707316420195 77208113578099060974630293)
                ·
                  refine ⟨3619130323973393483185795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77208113578099060974630293 3619130323973393483185795)
                  ·
                    refine ⟨5428695485960090224778693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3619130323973393483185795 5428695485960090224778693)
                    ·
                      refine ⟨1017880403617516917146005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5428695485960090224778693 1017880403617516917146005)
                      ·
                        rfl

theorem cell23_1982315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 4].length) (baseStart_1982315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982315 prefixEnd_1982315 := by exact prefixLift 1982315
  have htrace : WordTrace (prefixWord ++ tailWord_1982315) baseStart_1982315 baseEnd_1982315 := by
    simpa [prefixWord, tailWord_1982315, baseEnd_1982315] using wordTrace_append hprefix tailTrace_1982315
  have hstable : (prefixWord ++ tailWord_1982315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982315).length < 2 ^ (prefixWord ++ tailWord_1982315).sum := by decide
  have hdescent : baseEnd_1982315 < baseStart_1982315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982332 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 6, 4, 2]
def baseStart_1982332 : Nat := 118140960795 + 1982332 * 2 ^ 59
def prefixEnd_1982332 : Nat := 4983230072969 + 3 ^ 40 * 1982332 * 2
def baseEnd_1982332 : Nat := 1017889132788643350633427

theorem tailTrace_1982332 : CollatzResearch.WordTrace tailWord_1982332 prefixEnd_1982332 1017889132788643350633427 := by
  unfold tailWord_1982332
  simp only [CollatzResearch.WordTrace]
  refine ⟨36150793927178597098470625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48201058569571462797960833 36150793927178597098470625)
  ·
    refine ⟨27113095445383947823852969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36150793927178597098470625 27113095445383947823852969)
    ·
      refine ⟨20334821584037960867889727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27113095445383947823852969 20334821584037960867889727)
      ·
        refine ⟨30502232376056941301834591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20334821584037960867889727 30502232376056941301834591)
        ·
          refine ⟨45753348564085411952751887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30502232376056941301834591 45753348564085411952751887)
          ·
            refine ⟨68630022846128117929127831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45753348564085411952751887 68630022846128117929127831)
            ·
              refine ⟨102945034269192176893691747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68630022846128117929127831 102945034269192176893691747)
              ·
                refine ⟨154417551403788265340537621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102945034269192176893691747 154417551403788265340537621)
                ·
                  refine ⟨7238322722052574937837701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154417551403788265340537621 7238322722052574937837701)
                  ·
                    refine ⟨1357185510384857800844569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7238322722052574937837701 1357185510384857800844569)
                    ·
                      refine ⟨1017889132788643350633427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1357185510384857800844569 1017889132788643350633427)
                      ·
                        rfl

theorem cell23_1982332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_1982332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982332 prefixEnd_1982332 := by exact prefixLift 1982332
  have htrace : WordTrace (prefixWord ++ tailWord_1982332) baseStart_1982332 baseEnd_1982332 := by
    simpa [prefixWord, tailWord_1982332, baseEnd_1982332] using wordTrace_append hprefix tailTrace_1982332
  have hstable : (prefixWord ++ tailWord_1982332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982332).length < 2 ^ (prefixWord ++ tailWord_1982332).sum := by decide
  have hdescent : baseEnd_1982332 < baseStart_1982332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982345 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_1982345 : Nat := 118140960795 + 1982345 * 2 ^ 59
def prefixEnd_1982345 : Nat := 4983230072969 + 3 ^ 40 * 1982345 * 2
def baseEnd_1982345 : Nat := 1017895808037151799770867

theorem tailTrace_1982345 : CollatzResearch.WordTrace tailWord_1982345 prefixEnd_1982345 1017895808037151799770867 := by
  unfold tailWord_1982345
  simp only [CollatzResearch.WordTrace]
  refine ⟨72302062003310097417164489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48201374668873398278109659 72302062003310097417164489)
  ·
    refine ⟨54226546502482573062873367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72302062003310097417164489 54226546502482573062873367)
    ·
      refine ⟨81339819753723859594310051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54226546502482573062873367 81339819753723859594310051)
      ·
        refine ⟨122009729630585789391465077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81339819753723859594310051 122009729630585789391465077)
        ·
          refine ⟨11438412152867417755449851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122009729630585789391465077 11438412152867417755449851)
          ·
            refine ⟨17157618229301126633174777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11438412152867417755449851 17157618229301126633174777)
            ·
              refine ⟨12868213671975844974881083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17157618229301126633174777 12868213671975844974881083)
              ·
                refine ⟨19302320507963767462321625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12868213671975844974881083 19302320507963767462321625)
                ·
                  refine ⟨14476740380972825596741219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19302320507963767462321625 14476740380972825596741219)
                  ·
                    refine ⟨21715110571459238395111829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14476740380972825596741219 21715110571459238395111829)
                    ·
                      refine ⟨1017895808037151799770867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21715110571459238395111829 1017895808037151799770867)
                      ·
                        rfl

theorem cell23_1982345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_1982345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982345 prefixEnd_1982345 := by exact prefixLift 1982345
  have htrace : WordTrace (prefixWord ++ tailWord_1982345) baseStart_1982345 baseEnd_1982345 := by
    simpa [prefixWord, tailWord_1982345, baseEnd_1982345] using wordTrace_append hprefix tailTrace_1982345
  have hstable : (prefixWord ++ tailWord_1982345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982345).length < 2 ^ (prefixWord ++ tailWord_1982345).sum := by decide
  have hdescent : baseEnd_1982345 < baseStart_1982345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982350 : List Nat := [4, 1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_1982350 : Nat := 118140960795 + 1982350 * 2 ^ 59
def prefixEnd_1982350 : Nat := 4983230072969 + 3 ^ 40 * 1982350 * 2
def baseEnd_1982350 : Nat := 113099819493380475578705

theorem tailTrace_1982350 : CollatzResearch.WordTrace tailWord_1982350 prefixEnd_1982350 113099819493380475578705 := by
  unfold tailWord_1982350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9037780546036497908887063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48201496245527988847397669 9037780546036497908887063)
  ·
    refine ⟨13556670819054746863330595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9037780546036497908887063 13556670819054746863330595)
    ·
      refine ⟨20335006228582120294995893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13556670819054746863330595 20335006228582120294995893)
      ·
        refine ⟨1906406833929573777655865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20335006228582120294995893 1906406833929573777655865)
        ·
          refine ⟨1429805125447180333241899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1906406833929573777655865 1429805125447180333241899)
          ·
            refine ⟨2144707688170770499862849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429805125447180333241899 2144707688170770499862849)
            ·
              refine ⟨1608530766128077874897137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2144707688170770499862849 1608530766128077874897137)
              ·
                refine ⟨1206398074596058406172853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1608530766128077874897137 1206398074596058406172853)
                ·
                  refine ⟨113099819493380475578705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1206398074596058406172853 113099819493380475578705)
                  ·
                    rfl

theorem cell23_1982350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_1982350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982350 prefixEnd_1982350 := by exact prefixLift 1982350
  have htrace : WordTrace (prefixWord ++ tailWord_1982350) baseStart_1982350 baseEnd_1982350 := by
    simpa [prefixWord, tailWord_1982350, baseEnd_1982350] using wordTrace_append hprefix tailTrace_1982350
  have hstable : (prefixWord ++ tailWord_1982350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982350).length < 2 ^ (prefixWord ++ tailWord_1982350).sum := by decide
  have hdescent : baseEnd_1982350 < baseStart_1982350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982372 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 6]
def baseStart_1982372 : Nat := 118140960795 + 1982372 * 2 ^ 59
def prefixEnd_1982372 : Nat := 4983230072969 + 3 ^ 40 * 1982372 * 2
def baseEnd_1982372 : Nat := 113101074668313688237027

theorem tailTrace_1982372 : CollatzResearch.WordTrace tailWord_1982372 prefixEnd_1982372 113101074668313688237027 := by
  unfold tailWord_1982372
  simp only [CollatzResearch.WordTrace]
  refine ⟨36151523387106140514198685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48202031182808187352264913 36151523387106140514198685)
  ·
    refine ⟨13556821270164802692824507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36151523387106140514198685 13556821270164802692824507)
    ·
      refine ⟨20335231905247204039236761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13556821270164802692824507 20335231905247204039236761)
      ·
        refine ⟨15251423928935403029427571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20335231905247204039236761 15251423928935403029427571)
        ·
          refine ⟨22877135893403104544141357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15251423928935403029427571 22877135893403104544141357)
          ·
            refine ⟨8578925960026164204053009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22877135893403104544141357 8578925960026164204053009)
            ·
              refine ⟨6434194470019623153039757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8578925960026164204053009 6434194470019623153039757)
              ·
                refine ⟨2412822926257358682389909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6434194470019623153039757 2412822926257358682389909)
                ·
                  refine ⟨113101074668313688237027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2412822926257358682389909 113101074668313688237027)
                  ·
                    rfl

theorem cell23_1982372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_1982372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982372 prefixEnd_1982372 := by exact prefixLift 1982372
  have htrace : WordTrace (prefixWord ++ tailWord_1982372) baseStart_1982372 baseEnd_1982372 := by
    simpa [prefixWord, tailWord_1982372, baseEnd_1982372] using wordTrace_append hprefix tailTrace_1982372
  have hstable : (prefixWord ++ tailWord_1982372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982372).length < 2 ^ (prefixWord ++ tailWord_1982372).sum := by decide
  have hdescent : baseEnd_1982372 < baseStart_1982372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982416 : List Nat := [2, 1, 1, 1, 1, 2, 6, 4, 1, 1, 3]
def baseStart_1982416 : Nat := 118140960795 + 1982416 * 2 ^ 59
def prefixEnd_1982416 : Nat := 4983230072969 + 3 ^ 40 * 1982416 * 2
def baseEnd_1982416 : Nat := 1017932265163621021983041

theorem tailTrace_1982416 : CollatzResearch.WordTrace tailWord_1982416 prefixEnd_1982416 1017932265163621021983041 := by
  unfold tailWord_1982416
  simp only [CollatzResearch.WordTrace]
  refine ⟨36152325793026438271499551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48203101057368584361999401 36152325793026438271499551)
  ·
    refine ⟨54228488689539657407249327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36152325793026438271499551 54228488689539657407249327)
    ·
      refine ⟨81342733034309486110873991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54228488689539657407249327 81342733034309486110873991)
      ·
        refine ⟨122014099551464229166310987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81342733034309486110873991 122014099551464229166310987)
        ·
          refine ⟨183021149327196343749466481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122014099551464229166310987 183021149327196343749466481)
          ·
            refine ⟨137265861995397257812099861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183021149327196343749466481 137265861995397257812099861)
            ·
              refine ⟨6434337281034246459942181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137265861995397257812099861 6434337281034246459942181)
              ·
                refine ⟨1206438240193921211239159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6434337281034246459942181 1206438240193921211239159)
                ·
                  refine ⟨1809657360290881816858739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1206438240193921211239159 1809657360290881816858739)
                  ·
                    refine ⟨2714486040436322725288109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1809657360290881816858739 2714486040436322725288109)
                    ·
                      refine ⟨1017932265163621021983041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2714486040436322725288109 1017932265163621021983041)
                      ·
                        rfl

theorem cell23_1982416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 1, 1, 3].length) (baseStart_1982416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982416 prefixEnd_1982416 := by exact prefixLift 1982416
  have htrace : WordTrace (prefixWord ++ tailWord_1982416) baseStart_1982416 baseEnd_1982416 := by
    simpa [prefixWord, tailWord_1982416, baseEnd_1982416] using wordTrace_append hprefix tailTrace_1982416
  have hstable : (prefixWord ++ tailWord_1982416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982416).length < 2 ^ (prefixWord ++ tailWord_1982416).sum := by decide
  have hdescent : baseEnd_1982416 < baseStart_1982416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982442 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1982442 : Nat := 118140960795 + 1982442 * 2 ^ 59
def prefixEnd_1982442 : Nat := 4983230072969 + 3 ^ 40 * 1982442 * 2
def baseEnd_1982442 : Nat := 1017945615660637920257921

theorem tailTrace_1982442 : CollatzResearch.WordTrace tailWord_1982442 prefixEnd_1982442 1017945615660637920257921 := by
  unfold tailWord_1982442
  simp only [CollatzResearch.WordTrace]
  refine ⟨18076399970989670745861395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48203733255972455322297053 18076399970989670745861395)
  ·
    refine ⟨27114599956484506118792093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18076399970989670745861395 27114599956484506118792093)
    ·
      refine ⟨10167974983681689794547035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27114599956484506118792093 10167974983681689794547035)
      ·
        refine ⟨15251962475522534691820553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10167974983681689794547035 15251962475522534691820553)
        ·
          refine ⟨11438971856641901018865415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15251962475522534691820553 11438971856641901018865415)
          ·
            refine ⟨17158457784962851528298123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11438971856641901018865415 17158457784962851528298123)
            ·
              refine ⟨25737686677444277292447185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17158457784962851528298123 25737686677444277292447185)
              ·
                refine ⟨19303265008083207969335389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25737686677444277292447185 19303265008083207969335389)
                ·
                  refine ⟨7238724378031202988500771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19303265008083207969335389 7238724378031202988500771)
                  ·
                    refine ⟨10858086567046804482751157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7238724378031202988500771 10858086567046804482751157)
                    ·
                      refine ⟨1017945615660637920257921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10858086567046804482751157 1017945615660637920257921)
                      ·
                        rfl

theorem cell23_1982442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1982442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982442 prefixEnd_1982442 := by exact prefixLift 1982442
  have htrace : WordTrace (prefixWord ++ tailWord_1982442) baseStart_1982442 baseEnd_1982442 := by
    simpa [prefixWord, tailWord_1982442, baseEnd_1982442] using wordTrace_append hprefix tailTrace_1982442
  have hstable : (prefixWord ++ tailWord_1982442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982442).length < 2 ^ (prefixWord ++ tailWord_1982442).sum := by decide
  have hdescent : baseEnd_1982442 < baseStart_1982442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982459 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 1, 2, 3]
def baseStart_1982459 : Nat := 118140960795 + 1982459 * 2 ^ 59
def prefixEnd_1982459 : Nat := 4983230072969 + 3 ^ 40 * 1982459 * 2
def baseEnd_1982459 : Nat := 1017954344831764353745343

theorem tailTrace_1982459 : CollatzResearch.WordTrace tailWord_1982459 prefixEnd_1982459 1017954344831764353745343 := by
  unfold tailWord_1982459
  simp only [CollatzResearch.WordTrace]
  refine ⟨72306219924897094886814431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48204146616598063257876287 72306219924897094886814431)
  ·
    refine ⟨108459329887345642330221647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72306219924897094886814431 108459329887345642330221647)
    ·
      refine ⟨162688994831018463495332471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108459329887345642330221647 162688994831018463495332471)
      ·
        refine ⟨244033492246527695242998707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162688994831018463495332471 244033492246527695242998707)
        ·
          refine ⟨366050238369791542864498061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244033492246527695242998707 366050238369791542864498061)
          ·
            refine ⟨137268839388671828574186773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366050238369791542864498061 137268839388671828574186773)
            ·
              refine ⟨6434476846343991964415005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137268839388671828574186773 6434476846343991964415005)
              ·
                refine ⟨2412928817378996986655627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6434476846343991964415005 2412928817378996986655627)
                ·
                  refine ⟨3619393226068495479983441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412928817378996986655627 3619393226068495479983441)
                  ·
                    refine ⟨2714544919551371609987581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3619393226068495479983441 2714544919551371609987581)
                    ·
                      refine ⟨1017954344831764353745343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2714544919551371609987581 1017954344831764353745343)
                      ·
                        rfl

theorem cell23_1982459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 2, 3].length) (baseStart_1982459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982459 prefixEnd_1982459 := by exact prefixLift 1982459
  have htrace : WordTrace (prefixWord ++ tailWord_1982459) baseStart_1982459 baseEnd_1982459 := by
    simpa [prefixWord, tailWord_1982459, baseEnd_1982459] using wordTrace_append hprefix tailTrace_1982459
  have hstable : (prefixWord ++ tailWord_1982459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982459).length < 2 ^ (prefixWord ++ tailWord_1982459).sum := by decide
  have hdescent : baseEnd_1982459 < baseStart_1982459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982493 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_1982493 : Nat := 118140960795 + 1982493 * 2 ^ 59
def prefixEnd_1982493 : Nat := 4983230072969 + 3 ^ 40 * 1982493 * 2
def baseEnd_1982493 : Nat := 1017971803174017220720187

theorem tailTrace_1982493 : CollatzResearch.WordTrace tailWord_1982493 prefixEnd_1982493 1017971803174017220720187 := by
  unfold tailWord_1982493
  simp only [CollatzResearch.WordTrace]
  refine ⟨72307460006773918693552133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48204973337849279129034755 72307460006773918693552133)
  ·
    refine ⟨13557648751270109755041025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72307460006773918693552133 13557648751270109755041025)
    ·
      refine ⟨10168236563452582316280769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13557648751270109755041025 10168236563452582316280769)
      ·
        refine ⟨7626177422589436737210577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10168236563452582316280769 7626177422589436737210577)
        ·
          refine ⟨5719633066942077552907933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7626177422589436737210577 5719633066942077552907933)
          ·
            refine ⟨2144862400103279082340475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5719633066942077552907933 2144862400103279082340475)
            ·
              refine ⟨3217293600154918623510713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144862400103279082340475 3217293600154918623510713)
              ·
                refine ⟨2412970200116188967633035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3217293600154918623510713 2412970200116188967633035)
                ·
                  refine ⟨3619455300174283451449553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412970200116188967633035 3619455300174283451449553)
                  ·
                    refine ⟨2714591475130712588587165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3619455300174283451449553 2714591475130712588587165)
                    ·
                      refine ⟨1017971803174017220720187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2714591475130712588587165 1017971803174017220720187)
                      ·
                        rfl

theorem cell23_1982493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_1982493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982493 prefixEnd_1982493 := by exact prefixLift 1982493
  have htrace : WordTrace (prefixWord ++ tailWord_1982493) baseStart_1982493 baseEnd_1982493 := by
    simpa [prefixWord, tailWord_1982493, baseEnd_1982493] using wordTrace_append hprefix tailTrace_1982493
  have hstable : (prefixWord ++ tailWord_1982493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982493).length < 2 ^ (prefixWord ++ tailWord_1982493).sum := by decide
  have hdescent : baseEnd_1982493 < baseStart_1982493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982506 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1982506 : Nat := 118140960795 + 1982506 * 2 ^ 59
def prefixEnd_1982506 : Nat := 4983230072969 + 3 ^ 40 * 1982506 * 2
def baseEnd_1982506 : Nat := 1017978478422525669857627

theorem tailTrace_1982506 : CollatzResearch.WordTrace tailWord_1982506 prefixEnd_1982506 1017978478422525669857627 := by
  unfold tailWord_1982506
  simp only [CollatzResearch.WordTrace]
  refine ⟨18076983538931705478443843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48205289437151214609183581 18076983538931705478443843)
  ·
    refine ⟨27115475308397558217665765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18076983538931705478443843 27115475308397558217665765)
    ·
      refine ⟨5084151620324542165812331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27115475308397558217665765 5084151620324542165812331)
      ·
        refine ⟨7626227430486813248718497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5084151620324542165812331 7626227430486813248718497)
        ·
          refine ⟨5719670572865109936538873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7626227430486813248718497 5719670572865109936538873)
          ·
            refine ⟨4289752929648832452404155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5719670572865109936538873 4289752929648832452404155)
            ·
              refine ⟨6434629394473248678606233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289752929648832452404155 6434629394473248678606233)
              ·
                refine ⟨4825972045854936508954675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6434629394473248678606233 4825972045854936508954675)
                ·
                  refine ⟨7238958068782404763432013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4825972045854936508954675 7238958068782404763432013)
                  ·
                    refine ⟨2714609275793401786287005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7238958068782404763432013 2714609275793401786287005)
                    ·
                      refine ⟨1017978478422525669857627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2714609275793401786287005 1017978478422525669857627)
                      ·
                        rfl

theorem cell23_1982506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1982506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982506 prefixEnd_1982506 := by exact prefixLift 1982506
  have htrace : WordTrace (prefixWord ++ tailWord_1982506) baseStart_1982506 baseEnd_1982506 := by
    simpa [prefixWord, tailWord_1982506, baseEnd_1982506] using wordTrace_append hprefix tailTrace_1982506
  have hstable : (prefixWord ++ tailWord_1982506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982506).length < 2 ^ (prefixWord ++ tailWord_1982506).sum := by decide
  have hdescent : baseEnd_1982506 < baseStart_1982506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982522 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_1982522 : Nat := 118140960795 + 1982522 * 2 ^ 59
def prefixEnd_1982522 : Nat := 4983230072969 + 3 ^ 40 * 1982522 * 2
def baseEnd_1982522 : Nat := 339328898037665869085851

theorem tailTrace_1982522 : CollatzResearch.WordTrace tailWord_1982522 prefixEnd_1982522 339328898037665869085851 := by
  unfold tailWord_1982522
  simp only [CollatzResearch.WordTrace]
  refine ⟨18077129430917214161589455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48205678482445904430905213 18077129430917214161589455)
  ·
    refine ⟨27115694146375821242384183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18077129430917214161589455 27115694146375821242384183)
    ·
      refine ⟨40673541219563731863576275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27115694146375821242384183 40673541219563731863576275)
      ·
        refine ⟨61010311829345597795364413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40673541219563731863576275 61010311829345597795364413)
        ·
          refine ⟨22878866936004599173261655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61010311829345597795364413 22878866936004599173261655)
          ·
            refine ⟨34318300404006898759892483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22878866936004599173261655 34318300404006898759892483)
            ·
              refine ⟨51477450606010348139838725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34318300404006898759892483 51477450606010348139838725)
              ·
                refine ⟨9652021988626940276219761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51477450606010348139838725 9652021988626940276219761)
                ·
                  refine ⟨7239016491470205207164821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9652021988626940276219761 7239016491470205207164821)
                  ·
                    refine ⟨339328898037665869085851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7239016491470205207164821 339328898037665869085851)
                    ·
                      rfl

theorem cell23_1982522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_1982522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982522 prefixEnd_1982522 := by exact prefixLift 1982522
  have htrace : WordTrace (prefixWord ++ tailWord_1982522) baseStart_1982522 baseEnd_1982522 := by
    simpa [prefixWord, tailWord_1982522, baseEnd_1982522] using wordTrace_append hprefix tailTrace_1982522
  have hstable : (prefixWord ++ tailWord_1982522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982522).length < 2 ^ (prefixWord ++ tailWord_1982522).sum := by decide
  have hdescent : baseEnd_1982522 < baseStart_1982522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982529 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1982529 : Nat := 118140960795 + 1982529 * 2 ^ 59
def prefixEnd_1982529 : Nat := 4983230072969 + 3 ^ 40 * 1982529 * 2
def baseEnd_1982529 : Nat := 1017990288477579079870021

theorem tailTrace_1982529 : CollatzResearch.WordTrace tailWord_1982529 prefixEnd_1982529 1017990288477579079870021 := by
  unfold tailWord_1982529
  simp only [CollatzResearch.WordTrace]
  refine ⟨72308773034643496841862641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48205848689762331227908427 72308773034643496841862641)
  ·
    refine ⟨54231579775982622631396981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72308773034643496841862641 54231579775982622631396981)
    ·
      refine ⟨5084210603998370871693467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54231579775982622631396981 5084210603998370871693467)
      ·
        refine ⟨7626315905997556307540201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5084210603998370871693467 7626315905997556307540201)
        ·
          refine ⟨5719736929498167230655151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7626315905997556307540201 5719736929498167230655151)
          ·
            refine ⟨8579605394247250845982727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5719736929498167230655151 8579605394247250845982727)
            ·
              refine ⟨12869408091370876268974091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8579605394247250845982727 12869408091370876268974091)
              ·
                refine ⟨19304112137056314403461137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12869408091370876268974091 19304112137056314403461137)
                ·
                  refine ⟨14478084102792235802595853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19304112137056314403461137 14478084102792235802595853)
                  ·
                    refine ⟨5429281538547088425973445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14478084102792235802595853 5429281538547088425973445)
                    ·
                      refine ⟨1017990288477579079870021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5429281538547088425973445 1017990288477579079870021)
                      ·
                        rfl

theorem cell23_1982529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1982529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982529 prefixEnd_1982529 := by exact prefixLift 1982529
  have htrace : WordTrace (prefixWord ++ tailWord_1982529) baseStart_1982529 baseEnd_1982529 := by
    simpa [prefixWord, tailWord_1982529, baseEnd_1982529] using wordTrace_append hprefix tailTrace_1982529
  have hstable : (prefixWord ++ tailWord_1982529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982529).length < 2 ^ (prefixWord ++ tailWord_1982529).sum := by decide
  have hdescent : baseEnd_1982529 < baseStart_1982529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982550 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_1982550 : Nat := 118140960795 + 1982550 * 2 ^ 59
def prefixEnd_1982550 : Nat := 4983230072969 + 3 ^ 40 * 1982550 * 2
def baseEnd_1982550 : Nat := 1018001071571323497707425

theorem tailTrace_1982550 : CollatzResearch.WordTrace tailWord_1982550 prefixEnd_1982550 1018001071571323497707425 := by
  unfold tailWord_1982550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4519346185472963589273569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48206359311711611618918069 4519346185472963589273569)
  ·
    refine ⟨3389509639104722691955177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4519346185472963589273569 3389509639104722691955177)
    ·
      refine ⟨2542132229328542018966383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3389509639104722691955177 2542132229328542018966383)
      ·
        refine ⟨3813198343992813028449575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2542132229328542018966383 3813198343992813028449575)
        ·
          refine ⟨5719797515989219542674363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813198343992813028449575 5719797515989219542674363)
          ·
            refine ⟨8579696273983829314011545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5719797515989219542674363 8579696273983829314011545)
            ·
              refine ⟨6434772205487871985508659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8579696273983829314011545 6434772205487871985508659)
              ·
                refine ⟨9652158308231807978262989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6434772205487871985508659 9652158308231807978262989)
                ·
                  refine ⟨3619559365586927991848621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9652158308231807978262989 3619559365586927991848621)
                  ·
                    refine ⟨1357334762095097996943233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3619559365586927991848621 1357334762095097996943233)
                    ·
                      refine ⟨1018001071571323497707425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1357334762095097996943233 1018001071571323497707425)
                      ·
                        rfl

theorem cell23_1982550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_1982550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982550 prefixEnd_1982550 := by exact prefixLift 1982550
  have htrace : WordTrace (prefixWord ++ tailWord_1982550) baseStart_1982550 baseEnd_1982550 := by
    simpa [prefixWord, tailWord_1982550, baseEnd_1982550] using wordTrace_append hprefix tailTrace_1982550
  have hstable : (prefixWord ++ tailWord_1982550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982550).length < 2 ^ (prefixWord ++ tailWord_1982550).sum := by decide
  have hdescent : baseEnd_1982550 < baseStart_1982550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982552 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 9]
def baseStart_1982552 : Nat := 118140960795 + 1982552 * 2 ^ 59
def prefixEnd_1982552 : Nat := 4983230072969 + 3 ^ 40 * 1982552 * 2
def baseEnd_1982552 : Nat := 113111344281403609986935

theorem tailTrace_1982552 : CollatzResearch.WordTrace tailWord_1982552 prefixEnd_1982552 113111344281403609986935 := by
  unfold tailWord_1982552
  simp only [CollatzResearch.WordTrace]
  refine ⟨36154805956780085884974955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48206407942373447846633273 36154805956780085884974955)
  ·
    refine ⟨54232208935170128827462433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36154805956780085884974955 54232208935170128827462433)
    ·
      refine ⟨40674156701377596620596825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54232208935170128827462433 40674156701377596620596825)
      ·
        refine ⟨30505617526033197465447619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40674156701377596620596825 30505617526033197465447619)
        ·
          refine ⟨45758426289049796198171429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30505617526033197465447619 45758426289049796198171429)
          ·
            refine ⟨8579704929196836787157143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45758426289049796198171429 8579704929196836787157143)
            ·
              refine ⟨12869557393795255180735715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8579704929196836787157143 12869557393795255180735715)
              ·
                refine ⟨19304336090692882771103573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12869557393795255180735715 19304336090692882771103573)
                ·
                  refine ⟨113111344281403609986935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19304336090692882771103573 113111344281403609986935)
                  ·
                    rfl

theorem cell23_1982552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 9].length) (baseStart_1982552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982552 prefixEnd_1982552 := by exact prefixLift 1982552
  have htrace : WordTrace (prefixWord ++ tailWord_1982552) baseStart_1982552 baseEnd_1982552 := by
    simpa [prefixWord, tailWord_1982552, baseEnd_1982552] using wordTrace_append hprefix tailTrace_1982552
  have hstable : (prefixWord ++ tailWord_1982552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982552).length < 2 ^ (prefixWord ++ tailWord_1982552).sum := by decide
  have hdescent : baseEnd_1982552 < baseStart_1982552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982592 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_1982592 : Nat := 118140960795 + 1982592 * 2 ^ 59
def prefixEnd_1982592 : Nat := 4983230072969 + 3 ^ 40 * 1982592 * 2
def baseEnd_1982592 : Nat := 1018022637758812333382231

theorem tailTrace_1982592 : CollatzResearch.WordTrace tailWord_1982592 prefixEnd_1982592 1018022637758812333382231 := by
  unfold tailWord_1982592
  simp only [CollatzResearch.WordTrace]
  refine ⟨36155535416707629300703015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48207380555610172400937353 36155535416707629300703015)
  ·
    refine ⟨54233303125061443951054523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36155535416707629300703015 54233303125061443951054523)
    ·
      refine ⟨81349954687592165926581785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54233303125061443951054523 81349954687592165926581785)
      ·
        refine ⟨61012466015694124444936339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81349954687592165926581785 61012466015694124444936339)
        ·
          refine ⟨91518699023541186667404509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61012466015694124444936339 91518699023541186667404509)
          ·
            refine ⟨34319512133827945000276691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91518699023541186667404509 34319512133827945000276691)
            ·
              refine ⟨51479268200741917500415037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34319512133827945000276691 51479268200741917500415037)
              ·
                refine ⟨19304725575278219062655639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51479268200741917500415037 19304725575278219062655639)
                ·
                  refine ⟨28957088362917328593983459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19304725575278219062655639 28957088362917328593983459)
                  ·
                    refine ⟨43435632544375992890975189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28957088362917328593983459 43435632544375992890975189)
                    ·
                      refine ⟨1018022637758812333382231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 43435632544375992890975189 1018022637758812333382231)
                      ·
                        rfl

theorem cell23_1982592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_1982592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982592 prefixEnd_1982592 := by exact prefixLift 1982592
  have htrace : WordTrace (prefixWord ++ tailWord_1982592) baseStart_1982592 baseEnd_1982592 := by
    simpa [prefixWord, tailWord_1982592, baseEnd_1982592] using wordTrace_append hprefix tailTrace_1982592
  have hstable : (prefixWord ++ tailWord_1982592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982592).length < 2 ^ (prefixWord ++ tailWord_1982592).sum := by decide
  have hdescent : baseEnd_1982592 < baseStart_1982592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982706 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_1982706 : Nat := 118140960795 + 1982706 * 2 ^ 59
def prefixEnd_1982706 : Nat := 4983230072969 + 3 ^ 40 * 1982706 * 2
def baseEnd_1982706 : Nat := 339360391517808295785569

theorem tailTrace_1982706 : CollatzResearch.WordTrace tailWord_1982706 prefixEnd_1982706 339360391517808295785569 := by
  unfold tailWord_1982706
  simp only [CollatzResearch.WordTrace]
  refine ⟨18078807188750564017763993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48210152503334837380703981 18078807188750564017763993)
  ·
    refine ⟨13559105391562923013322995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18078807188750564017763993 13559105391562923013322995)
    ·
      refine ⟨20338658087344384519984493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13559105391562923013322995 20338658087344384519984493)
      ·
        refine ⟨7626996782754144194994185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20338658087344384519984493 7626996782754144194994185)
        ·
          refine ⟨5720247587065608146245639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7626996782754144194994185 5720247587065608146245639)
          ·
            refine ⟨8580371380598412219368459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5720247587065608146245639 8580371380598412219368459)
            ·
              refine ⟨12870557070897618329052689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8580371380598412219368459 12870557070897618329052689)
              ·
                refine ⟨9652917803173213746789517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12870557070897618329052689 9652917803173213746789517)
                ·
                  refine ⟨3619844176189955155046069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9652917803173213746789517 3619844176189955155046069)
                  ·
                    refine ⟨339360391517808295785569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3619844176189955155046069 339360391517808295785569)
                    ·
                      rfl

theorem cell23_1982706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_1982706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982706 prefixEnd_1982706 := by exact prefixLift 1982706
  have htrace : WordTrace (prefixWord ++ tailWord_1982706) baseStart_1982706 baseEnd_1982706 := by
    simpa [prefixWord, tailWord_1982706, baseEnd_1982706] using wordTrace_append hprefix tailTrace_1982706
  have hstable : (prefixWord ++ tailWord_1982706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982706).length < 2 ^ (prefixWord ++ tailWord_1982706).sum := by decide
  have hdescent : baseEnd_1982706 < baseStart_1982706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982743 : List Nat := [1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1982743 : Nat := 118140960795 + 1982743 * 2 ^ 59
def prefixEnd_1982743 : Nat := 4983230072969 + 3 ^ 40 * 1982743 * 2
def baseEnd_1982743 : Nat := 1018100173337641242594037

theorem tailTrace_1982743 : CollatzResearch.WordTrace tailWord_1982743 prefixEnd_1982743 1018100173337641242594037 := by
  unfold tailWord_1982743
  simp only [CollatzResearch.WordTrace]
  refine ⟨72316578255868211390152883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48211052170578807593435255 72316578255868211390152883)
  ·
    refine ⟨108474867383802317085229325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72316578255868211390152883 108474867383802317085229325)
    ·
      refine ⟨40678075268925868906960997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108474867383802317085229325 40678075268925868906960997)
      ·
        refine ⟨7627139112923600420055187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40678075268925868906960997 7627139112923600420055187)
        ·
          refine ⟨11440708669385400630082781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7627139112923600420055187 11440708669385400630082781)
          ·
            refine ⟨4290265751019525236281043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11440708669385400630082781 4290265751019525236281043)
            ·
              refine ⟨6435398626529287854421565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4290265751019525236281043 6435398626529287854421565)
              ·
                refine ⟨2413274484948482945408087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6435398626529287854421565 2413274484948482945408087)
                ·
                  refine ⟨3619911727422724418112131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413274484948482945408087 3619911727422724418112131)
                  ·
                    refine ⟨5429867591134086627168197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3619911727422724418112131 5429867591134086627168197)
                    ·
                      refine ⟨1018100173337641242594037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5429867591134086627168197 1018100173337641242594037)
                      ·
                        rfl

theorem cell23_1982743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1982743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982743 prefixEnd_1982743 := by exact prefixLift 1982743
  have htrace : WordTrace (prefixWord ++ tailWord_1982743) baseStart_1982743 baseEnd_1982743 := by
    simpa [prefixWord, tailWord_1982743, baseEnd_1982743] using wordTrace_append hprefix tailTrace_1982743
  have hstable : (prefixWord ++ tailWord_1982743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982743).length < 2 ^ (prefixWord ++ tailWord_1982743).sum := by decide
  have hdescent : baseEnd_1982743 < baseStart_1982743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982753 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 2, 4]
def baseStart_1982753 : Nat := 118140960795 + 1982753 * 2 ^ 59
def prefixEnd_1982753 : Nat := 4983230072969 + 3 ^ 40 * 1982753 * 2
def baseEnd_1982753 : Nat := 339368436048062067822997

theorem tailTrace_1982753 : CollatzResearch.WordTrace tailWord_1982753 prefixEnd_1982753 339368436048062067822997 := by
  unfold tailWord_1982753
  simp only [CollatzResearch.WordTrace]
  refine ⟨72316942985831983098016913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48211295323887988732011275 72316942985831983098016913)
  ·
    refine ⟨54237707239373987323512685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72316942985831983098016913 54237707239373987323512685)
    ·
      refine ⟨20339140214765245246317257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54237707239373987323512685 20339140214765245246317257)
      ·
        refine ⟨15254355161073933934737943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20339140214765245246317257 15254355161073933934737943)
        ·
          refine ⟨22881532741610900902106915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15254355161073933934737943 22881532741610900902106915)
          ·
            refine ⟨34322299112416351353160373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22881532741610900902106915 34322299112416351353160373)
            ·
              refine ⟨3217715541789032939358785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34322299112416351353160373 3217715541789032939358785)
              ·
                refine ⟨2413286656341774704519089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3217715541789032939358785 2413286656341774704519089)
                ·
                  refine ⟨1809964992256331028389317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2413286656341774704519089 1809964992256331028389317)
                  ·
                    refine ⟨339368436048062067822997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1809964992256331028389317 339368436048062067822997)
                    ·
                      rfl

theorem cell23_1982753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_1982753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982753 prefixEnd_1982753 := by exact prefixLift 1982753
  have htrace : WordTrace (prefixWord ++ tailWord_1982753) baseStart_1982753 baseEnd_1982753 := by
    simpa [prefixWord, tailWord_1982753, baseEnd_1982753] using wordTrace_append hprefix tailTrace_1982753
  have hstable : (prefixWord ++ tailWord_1982753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982753).length < 2 ^ (prefixWord ++ tailWord_1982753).sum := by decide
  have hdescent : baseEnd_1982753 < baseStart_1982753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982770 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_1982770 : Nat := 118140960795 + 1982770 * 2 ^ 59
def prefixEnd_1982770 : Nat := 4983230072969 + 3 ^ 40 * 1982770 * 2
def baseEnd_1982770 : Nat := 339371345771770878985471

theorem tailTrace_1982770 : CollatzResearch.WordTrace tailWord_1982770 prefixEnd_1982770 339371345771770878985471 := by
  unfold tailWord_1982770
  simp only [CollatzResearch.WordTrace]
  refine ⟨18079390756692598750346441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48211708684513596667590509 18079390756692598750346441)
  ·
    refine ⟨13559543067519449062759831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18079390756692598750346441 13559543067519449062759831)
    ·
      refine ⟨20339314601279173594139747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13559543067519449062759831 20339314601279173594139747)
      ·
        refine ⟨30508971901918760391209621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20339314601279173594139747 30508971901918760391209621)
        ·
          refine ⟨1430108057902441893337951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30508971901918760391209621 1430108057902441893337951)
          ·
            refine ⟨2145162086853662840006927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430108057902441893337951 2145162086853662840006927)
            ·
              refine ⟨3217743130280494260010391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145162086853662840006927 3217743130280494260010391)
              ·
                refine ⟨4826614695420741390015587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217743130280494260010391 4826614695420741390015587)
                ·
                  refine ⟨7239922043131112085023381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826614695420741390015587 7239922043131112085023381)
                  ·
                    refine ⟨339371345771770878985471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7239922043131112085023381 339371345771770878985471)
                    ·
                      rfl

theorem cell23_1982770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_1982770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982770 prefixEnd_1982770 := by exact prefixLift 1982770
  have htrace : WordTrace (prefixWord ++ tailWord_1982770) baseStart_1982770 baseEnd_1982770 := by
    simpa [prefixWord, tailWord_1982770, baseEnd_1982770] using wordTrace_append hprefix tailTrace_1982770
  have hstable : (prefixWord ++ tailWord_1982770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982770).length < 2 ^ (prefixWord ++ tailWord_1982770).sum := by decide
  have hdescent : baseEnd_1982770 < baseStart_1982770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982833 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 1, 4, 2]
def baseStart_1982833 : Nat := 118140960795 + 1982833 * 2 ^ 59
def prefixEnd_1982833 : Nat := 4983230072969 + 3 ^ 40 * 1982833 * 2
def baseEnd_1982833 : Nat := 1018146386596545890468623

theorem tailTrace_1982833 : CollatzResearch.WordTrace tailWord_1982833 prefixEnd_1982833 1018146386596545890468623 := by
  unfold tailWord_1982833
  simp only [CollatzResearch.WordTrace]
  refine ⟨72319860825542156760929153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48213240550361437840619435 72319860825542156760929153)
  ·
    refine ⟨54239895619156617570696865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72319860825542156760929153 54239895619156617570696865)
    ·
      refine ⟨40679921714367463178022649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54239895619156617570696865 40679921714367463178022649)
      ·
        refine ⟨30509941285775597383516987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40679921714367463178022649 30509941285775597383516987)
        ·
          refine ⟨45764911928663396075275481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30509941285775597383516987 45764911928663396075275481)
          ·
            refine ⟨34323683946497547056456611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45764911928663396075275481 34323683946497547056456611)
            ·
              refine ⟨51485525919746320584684917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34323683946497547056456611 51485525919746320584684917)
              ·
                refine ⟨4826768054976217554814211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51485525919746320584684917 4826768054976217554814211)
                ·
                  refine ⟨7240152082464326332221317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826768054976217554814211 7240152082464326332221317)
                  ·
                    refine ⟨1357528515462061187291497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7240152082464326332221317 1357528515462061187291497)
                    ·
                      refine ⟨1018146386596545890468623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1357528515462061187291497 1018146386596545890468623)
                      ·
                        rfl

theorem cell23_1982833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_1982833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982833 prefixEnd_1982833 := by exact prefixLift 1982833
  have htrace : WordTrace (prefixWord ++ tailWord_1982833) baseStart_1982833 baseEnd_1982833 := by
    simpa [prefixWord, tailWord_1982833, baseEnd_1982833] using wordTrace_append hprefix tailTrace_1982833
  have hstable : (prefixWord ++ tailWord_1982833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982833).length < 2 ^ (prefixWord ++ tailWord_1982833).sum := by decide
  have hdescent : baseEnd_1982833 < baseStart_1982833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982837 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_1982837 : Nat := 118140960795 + 1982837 * 2 ^ 59
def prefixEnd_1982837 : Nat := 4983230072969 + 3 ^ 40 * 1982837 * 2
def baseEnd_1982837 : Nat := 1018148440519163874818605

theorem tailTrace_1982837 : CollatzResearch.WordTrace tailWord_1982837 prefixEnd_1982837 1018148440519163874818605 := by
  unfold tailWord_1982837
  simp only [CollatzResearch.WordTrace]
  refine ⟨72320006717527665444074765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48213337811685110296049843 72320006717527665444074765)
  ·
    refine ⟨27120002519072874541528037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72320006717527665444074765 27120002519072874541528037)
    ·
      refine ⟨5085000472326163976536507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27120002519072874541528037 5085000472326163976536507)
      ·
        refine ⟨7627500708489245964804761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5085000472326163976536507 7627500708489245964804761)
        ·
          refine ⟨5720625531366934473603571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7627500708489245964804761 5720625531366934473603571)
          ·
            refine ⟨8580938297050401710405357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5720625531366934473603571 8580938297050401710405357)
            ·
              refine ⟨3217851861393900641402009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8580938297050401710405357 3217851861393900641402009)
              ·
                refine ⟨2413388896045425481051507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3217851861393900641402009 2413388896045425481051507)
                ·
                  refine ⟨3620083344068138221577261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413388896045425481051507 3620083344068138221577261)
                  ·
                    refine ⟨1357531254025551833091473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3620083344068138221577261 1357531254025551833091473)
                    ·
                      refine ⟨1018148440519163874818605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1357531254025551833091473 1018148440519163874818605)
                      ·
                        rfl

theorem cell23_1982837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_1982837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982837 prefixEnd_1982837 := by exact prefixLift 1982837
  have htrace : WordTrace (prefixWord ++ tailWord_1982837) baseStart_1982837 baseEnd_1982837 := by
    simpa [prefixWord, tailWord_1982837, baseEnd_1982837] using wordTrace_append hprefix tailTrace_1982837
  have hstable : (prefixWord ++ tailWord_1982837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982837).length < 2 ^ (prefixWord ++ tailWord_1982837).sum := by decide
  have hdescent : baseEnd_1982837 < baseStart_1982837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982873 : List Nat := [1, 2, 1, 2, 1, 4, 3, 4, 5]
def baseStart_1982873 : Nat := 118140960795 + 1982873 * 2 ^ 59
def prefixEnd_1982873 : Nat := 4983230072969 + 3 ^ 40 * 1982873 * 2
def baseEnd_1982873 : Nat := 113129658424747303774271

theorem tailTrace_1982873 : CollatzResearch.WordTrace tailWord_1982873 prefixEnd_1982873 113129658424747303774271 := by
  unfold tailWord_1982873
  simp only [CollatzResearch.WordTrace]
  refine ⟨72321319745397243592385273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48214213163598162394923515 72321319745397243592385273)
  ·
    refine ⟨54240989809047932694288955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72321319745397243592385273 54240989809047932694288955)
    ·
      refine ⟨81361484713571899041433433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54240989809047932694288955 81361484713571899041433433)
      ·
        refine ⟨61021113535178924281075075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81361484713571899041433433 61021113535178924281075075)
        ·
          refine ⟨91531670302768386421612613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61021113535178924281075075 91531670302768386421612613)
          ·
            refine ⟨17162188181769072454052365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91531670302768386421612613 17162188181769072454052365)
            ·
              refine ⟨6435820568163402170269637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17162188181769072454052365 6435820568163402170269637)
              ·
                refine ⟨1206716356530637906925557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6435820568163402170269637 1206716356530637906925557)
                ·
                  refine ⟨113129658424747303774271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1206716356530637906925557 113129658424747303774271)
                  ·
                    rfl

theorem cell23_1982873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 5].length) (baseStart_1982873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982873 prefixEnd_1982873 := by exact prefixLift 1982873
  have htrace : WordTrace (prefixWord ++ tailWord_1982873) baseStart_1982873 baseEnd_1982873 := by
    simpa [prefixWord, tailWord_1982873, baseEnd_1982873] using wordTrace_append hprefix tailTrace_1982873
  have hstable : (prefixWord ++ tailWord_1982873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982873).length < 2 ^ (prefixWord ++ tailWord_1982873).sum := by decide
  have hdescent : baseEnd_1982873 < baseStart_1982873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982883 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 3]
def baseStart_1982883 : Nat := 118140960795 + 1982883 * 2 ^ 59
def prefixEnd_1982883 : Nat := 4983230072969 + 3 ^ 40 * 1982883 * 2
def baseEnd_1982883 : Nat := 1018172060629270694843393

theorem tailTrace_1982883 : CollatzResearch.WordTrace tailWord_1982883 prefixEnd_1982883 1018172060629270694843393 := by
  unfold tailWord_1982883
  simp only [CollatzResearch.WordTrace]
  refine ⟨72321684475361015300249303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48214456316907343533499535 72321684475361015300249303)
  ·
    refine ⟨108482526713041522950373955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72321684475361015300249303 108482526713041522950373955)
    ·
      refine ⟨162723790069562284425560933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108482526713041522950373955 162723790069562284425560933)
      ·
        refine ⟨30510710638042928329792675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162723790069562284425560933 30510710638042928329792675)
        ·
          refine ⟨45766065957064392494689013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30510710638042928329792675 45766065957064392494689013)
          ·
            refine ⟨4290568683474786796377095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45766065957064392494689013 4290568683474786796377095)
            ·
              refine ⟨6435853025212180194565643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4290568683474786796377095 6435853025212180194565643)
              ·
                refine ⟨9653779537818270291848465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6435853025212180194565643 9653779537818270291848465)
                ·
                  refine ⟨7240334653363702718886349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9653779537818270291848465 7240334653363702718886349)
                  ·
                    refine ⟨2715125495011388519582381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7240334653363702718886349 2715125495011388519582381)
                    ·
                      refine ⟨1018172060629270694843393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2715125495011388519582381 1018172060629270694843393)
                      ·
                        rfl

theorem cell23_1982883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_1982883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982883 prefixEnd_1982883 := by exact prefixLift 1982883
  have htrace : WordTrace (prefixWord ++ tailWord_1982883) baseStart_1982883 baseEnd_1982883 := by
    simpa [prefixWord, tailWord_1982883, baseEnd_1982883] using wordTrace_append hprefix tailTrace_1982883
  have hstable : (prefixWord ++ tailWord_1982883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982883).length < 2 ^ (prefixWord ++ tailWord_1982883).sum := by decide
  have hdescent : baseEnd_1982883 < baseStart_1982883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982903 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 2, 5]
def baseStart_1982903 : Nat := 118140960795 + 1982903 * 2 ^ 59
def prefixEnd_1982903 : Nat := 4983230072969 + 3 ^ 40 * 1982903 * 2
def baseEnd_1982903 : Nat := 339394110080786872197767

theorem tailTrace_1982903 : CollatzResearch.WordTrace tailWord_1982903 prefixEnd_1982903 339394110080786872197767 := by
  unfold tailWord_1982903
  simp only [CollatzResearch.WordTrace]
  refine ⟨72322413935288558715977363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48214942623525705810651575 72322413935288558715977363)
  ·
    refine ⟨108483620902932838073966045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72322413935288558715977363 108483620902932838073966045)
    ·
      refine ⟨40681357838599814277737267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108483620902932838073966045 40681357838599814277737267)
      ·
        refine ⟨61022036757899721416605901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40681357838599814277737267 61022036757899721416605901)
        ·
          refine ⟨22883263784212395531227213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61022036757899721416605901 22883263784212395531227213)
          ·
            refine ⟨8581223919079648324210205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22883263784212395531227213 8581223919079648324210205)
            ·
              refine ⟨3217958969654868121578827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8581223919079648324210205 3217958969654868121578827)
              ·
                refine ⟨4826938454482302182368241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217958969654868121578827 4826938454482302182368241)
                ·
                  refine ⟨3620203840861726636776181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4826938454482302182368241 3620203840861726636776181)
                  ·
                    refine ⟨339394110080786872197767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3620203840861726636776181 339394110080786872197767)
                    ·
                      rfl

theorem cell23_1982903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_1982903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982903 prefixEnd_1982903 := by exact prefixLift 1982903
  have htrace : WordTrace (prefixWord ++ tailWord_1982903) baseStart_1982903 baseEnd_1982903 := by
    simpa [prefixWord, tailWord_1982903, baseEnd_1982903] using wordTrace_append hprefix tailTrace_1982903
  have hstable : (prefixWord ++ tailWord_1982903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982903).length < 2 ^ (prefixWord ++ tailWord_1982903).sum := by decide
  have hdescent : baseEnd_1982903 < baseStart_1982903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982936 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1982936 : Nat := 118140960795 + 1982936 * 2 ^ 59
def prefixEnd_1982936 : Nat := 4983230072969 + 3 ^ 40 * 1982936 * 2
def baseEnd_1982936 : Nat := 1018199275103958987480649

theorem tailTrace_1982936 : CollatzResearch.WordTrace tailWord_1982936 prefixEnd_1982936 1018199275103958987480649 := by
  unfold tailWord_1982936
  simp only [CollatzResearch.WordTrace]
  refine ⟨36161808772084502675964331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48215745029446003567952441 36161808772084502675964331)
  ·
    refine ⟨54242713158126754013946497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36161808772084502675964331 54242713158126754013946497)
    ·
      refine ⟨40682034868595065510459873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54242713158126754013946497 40682034868595065510459873)
      ·
        refine ⟨30511526151446299132844905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40682034868595065510459873 30511526151446299132844905)
        ·
          refine ⟨22883644613584724349633679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30511526151446299132844905 22883644613584724349633679)
          ·
            refine ⟨34325466920377086524450519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22883644613584724349633679 34325466920377086524450519)
            ·
              refine ⟨51488200380565629786675779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34325466920377086524450519 51488200380565629786675779)
              ·
                refine ⟨77232300570848444680013669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51488200380565629786675779 77232300570848444680013669)
                ·
                  refine ⟨14481056357034083377502563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77232300570848444680013669 14481056357034083377502563)
                  ·
                    refine ⟨21721584535551125066253845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14481056357034083377502563 21721584535551125066253845)
                    ·
                      refine ⟨1018199275103958987480649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21721584535551125066253845 1018199275103958987480649)
                      ·
                        rfl

theorem cell23_1982936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1982936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982936 prefixEnd_1982936 := by exact prefixLift 1982936
  have htrace : WordTrace (prefixWord ++ tailWord_1982936) baseStart_1982936 baseEnd_1982936 := by
    simpa [prefixWord, tailWord_1982936, baseEnd_1982936] using wordTrace_append hprefix tailTrace_1982936
  have hstable : (prefixWord ++ tailWord_1982936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982936).length < 2 ^ (prefixWord ++ tailWord_1982936).sum := by decide
  have hdescent : baseEnd_1982936 < baseStart_1982936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982943 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 3]
def baseStart_1982943 : Nat := 118140960795 + 1982943 * 2 ^ 59
def prefixEnd_1982943 : Nat := 4983230072969 + 3 ^ 40 * 1982943 * 2
def baseEnd_1982943 : Nat := 1018202869468540460093117

theorem tailTrace_1982943 : CollatzResearch.WordTrace tailWord_1982943 prefixEnd_1982943 1018202869468540460093117 := by
  unfold tailWord_1982943
  simp only [CollatzResearch.WordTrace]
  refine ⟨72323872855143645547433483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48215915236762430364955655 72323872855143645547433483)
  ·
    refine ⟨108485809282715468321150225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72323872855143645547433483 108485809282715468321150225)
    ·
      refine ⟨81364356962036601240862669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108485809282715468321150225 81364356962036601240862669)
      ·
        refine ⟨30511633860763725465323501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81364356962036601240862669 30511633860763725465323501)
        ·
          refine ⟨11441862697786397049496313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30511633860763725465323501 11441862697786397049496313)
          ·
            refine ⟨8581397023339797787122235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11441862697786397049496313 8581397023339797787122235)
            ·
              refine ⟨12872095535009696680683353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8581397023339797787122235 12872095535009696680683353)
              ·
                refine ⟨9654071651257272510512515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12872095535009696680683353 9654071651257272510512515)
                ·
                  refine ⟨14481107476885908765768773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9654071651257272510512515 14481107476885908765768773)
                  ·
                    refine ⟨2715207651916107893581645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14481107476885908765768773 2715207651916107893581645)
                    ·
                      refine ⟨1018202869468540460093117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2715207651916107893581645 1018202869468540460093117)
                      ·
                        rfl

theorem cell23_1982943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_1982943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1982943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1982943 prefixEnd_1982943 := by exact prefixLift 1982943
  have htrace : WordTrace (prefixWord ++ tailWord_1982943) baseStart_1982943 baseEnd_1982943 := by
    simpa [prefixWord, tailWord_1982943, baseEnd_1982943] using wordTrace_append hprefix tailTrace_1982943
  have hstable : (prefixWord ++ tailWord_1982943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982943).length < 2 ^ (prefixWord ++ tailWord_1982943).sum := by decide
  have hdescent : baseEnd_1982943 < baseStart_1982943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983040 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 2, 4]
def baseStart_1983040 : Nat := 118140960795 + 1983040 * 2 ^ 59
def prefixEnd_1983040 : Nat := 4983230072969 + 3 ^ 40 * 1983040 * 2
def baseEnd_1983040 : Nat := 339417559030675526860057

theorem tailTrace_1983040 : CollatzResearch.WordTrace tailWord_1983040 prefixEnd_1983040 339417559030675526860057 := by
  unfold tailWord_1983040
  simp only [CollatzResearch.WordTrace]
  refine ⟨36163705367896115556857287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48218273823861487409143049 36163705367896115556857287)
  ·
    refine ⟨54245558051844173335285931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36163705367896115556857287 54245558051844173335285931)
    ·
      refine ⟨81368337077766260002928897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54245558051844173335285931 81368337077766260002928897)
      ·
        refine ⟨61026252808324695002196673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81368337077766260002928897 61026252808324695002196673)
        ·
          refine ⟨45769689606243521251647505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61026252808324695002196673 45769689606243521251647505)
          ·
            refine ⟨34327267204682640938735629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45769689606243521251647505 34327267204682640938735629)
            ·
              refine ⟨12872725201755990352025861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34327267204682640938735629 12872725201755990352025861)
              ·
                refine ⟨2413635975329248191004849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12872725201755990352025861 2413635975329248191004849)
                ·
                  refine ⟨1810226981496936143253637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2413635975329248191004849 1810226981496936143253637)
                  ·
                    refine ⟨339417559030675526860057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1810226981496936143253637 339417559030675526860057)
                    ·
                      rfl

theorem cell23_1983040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2, 4].length) (baseStart_1983040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983040 prefixEnd_1983040 := by exact prefixLift 1983040
  have htrace : WordTrace (prefixWord ++ tailWord_1983040) baseStart_1983040 baseEnd_1983040 := by
    simpa [prefixWord, tailWord_1983040, baseEnd_1983040] using wordTrace_append hprefix tailTrace_1983040
  have hstable : (prefixWord ++ tailWord_1983040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983040).length < 2 ^ (prefixWord ++ tailWord_1983040).sum := by decide
  have hdescent : baseEnd_1983040 < baseStart_1983040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983041 : List Nat := [1, 2, 5, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_1983041 : Nat := 118140960795 + 1983041 * 2 ^ 59
def prefixEnd_1983041 : Nat := 4983230072969 + 3 ^ 40 * 1983041 * 2
def baseEnd_1983041 : Nat := 1018253190572681076667667

theorem tailTrace_1983041 : CollatzResearch.WordTrace tailWord_1983041 prefixEnd_1983041 1018253190572681076667667 := by
  unfold tailWord_1983041
  simp only [CollatzResearch.WordTrace]
  refine ⟨72327447208788608284500977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48218298139192405523000651 72327447208788608284500977)
  ·
    refine ⟨54245585406591456213375733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72327447208788608284500977 54245585406591456213375733)
    ·
      refine ⟨5085523631867949020003975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54245585406591456213375733 5085523631867949020003975)
      ·
        refine ⟨7628285447801923530005963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5085523631867949020003975 7628285447801923530005963)
        ·
          refine ⟨11442428171702885295008945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7628285447801923530005963 11442428171702885295008945)
          ·
            refine ⟨8581821128777163971256709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11442428171702885295008945 8581821128777163971256709)
            ·
              refine ⟨1609091461645718244610633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8581821128777163971256709 1609091461645718244610633)
              ·
                refine ⟨1206818596234288683457975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609091461645718244610633 1206818596234288683457975)
                ·
                  refine ⟨1810227894351433025186963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1206818596234288683457975 1810227894351433025186963)
                  ·
                    refine ⟨2715341841527149537780445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1810227894351433025186963 2715341841527149537780445)
                    ·
                      refine ⟨1018253190572681076667667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2715341841527149537780445 1018253190572681076667667)
                      ·
                        rfl

theorem cell23_1983041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_1983041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983041 prefixEnd_1983041 := by exact prefixLift 1983041
  have htrace : WordTrace (prefixWord ++ tailWord_1983041) baseStart_1983041 baseEnd_1983041 := by
    simpa [prefixWord, tailWord_1983041, baseEnd_1983041] using wordTrace_append hprefix tailTrace_1983041
  have hstable : (prefixWord ++ tailWord_1983041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983041).length < 2 ^ (prefixWord ++ tailWord_1983041).sum := by decide
  have hdescent : baseEnd_1983041 < baseStart_1983041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983050 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_1983050 : Nat := 118140960795 + 1983050 * 2 ^ 59
def prefixEnd_1983050 : Nat := 4983230072969 + 3 ^ 40 * 1983050 * 2
def baseEnd_1983050 : Nat := 1018257811898571541455125

theorem tailTrace_1983050 : CollatzResearch.WordTrace tailWord_1983050 prefixEnd_1983050 1018257811898571541455125 := by
  unfold tailWord_1983050
  simp only [CollatzResearch.WordTrace]
  refine ⟨18081943866439000705394651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48218516977170668547719069 18081943866439000705394651)
  ·
    refine ⟨27122915799658501058091977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18081943866439000705394651 27122915799658501058091977)
    ·
      refine ⟨20342186849743875793568983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27122915799658501058091977 20342186849743875793568983)
      ·
        refine ⟨30513280274615813690353475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20342186849743875793568983 30513280274615813690353475)
        ·
          refine ⟨45769920411923720535530213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30513280274615813690353475 45769920411923720535530213)
          ·
            refine ⟨8581860077235697600411915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45769920411923720535530213 8581860077235697600411915)
            ·
              refine ⟨12872790115853546400617873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8581860077235697600411915 12872790115853546400617873)
              ·
                refine ⟨9654592586890159800463405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12872790115853546400617873 9654592586890159800463405)
                ·
                  refine ⟨3620472220083809925173777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9654592586890159800463405 3620472220083809925173777)
                  ·
                    refine ⟨2715354165062857443880333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3620472220083809925173777 2715354165062857443880333)
                    ·
                      refine ⟨1018257811898571541455125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2715354165062857443880333 1018257811898571541455125)
                      ·
                        rfl

theorem cell23_1983050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_1983050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983050 prefixEnd_1983050 := by exact prefixLift 1983050
  have htrace : WordTrace (prefixWord ++ tailWord_1983050) baseStart_1983050 baseEnd_1983050 := by
    simpa [prefixWord, tailWord_1983050, baseEnd_1983050] using wordTrace_append hprefix tailTrace_1983050
  have hstable : (prefixWord ++ tailWord_1983050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983050).length < 2 ^ (prefixWord ++ tailWord_1983050).sum := by decide
  have hdescent : baseEnd_1983050 < baseStart_1983050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983060 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_1983060 : Nat := 118140960795 + 1983060 * 2 ^ 59
def prefixEnd_1983060 : Nat := 4983230072969 + 3 ^ 40 * 1983060 * 2
def baseEnd_1983060 : Nat := 1018262946705116502330079

theorem tailTrace_1983060 : CollatzResearch.WordTrace tailWord_1983060 prefixEnd_1983060 1018262946705116502330079 := by
  unfold tailWord_1983060
  simp only [CollatzResearch.WordTrace]
  refine ⟨36164070097859887264721317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48218760130479849686295089 36164070097859887264721317)
  ·
    refine ⟨6780763143348728862135247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36164070097859887264721317 6780763143348728862135247)
    ·
      refine ⟨10171144715023093293202871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6780763143348728862135247 10171144715023093293202871)
      ·
        refine ⟨15256717072534639939804307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10171144715023093293202871 15256717072534639939804307)
        ·
          refine ⟨22885075608801959909706461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15256717072534639939804307 22885075608801959909706461)
          ·
            refine ⟨8581903353300734966139923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22885075608801959909706461 8581903353300734966139923)
            ·
              refine ⟨12872855029951102449209885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8581903353300734966139923 12872855029951102449209885)
              ·
                refine ⟨4827320636231663418453707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12872855029951102449209885 4827320636231663418453707)
                ·
                  refine ⟨7240980954347495127680561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827320636231663418453707 7240980954347495127680561)
                  ·
                    refine ⟨5430735715760621345760421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7240980954347495127680561 5430735715760621345760421)
                    ·
                      refine ⟨1018262946705116502330079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5430735715760621345760421 1018262946705116502330079)
                      ·
                        rfl

theorem cell23_1983060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_1983060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983060 prefixEnd_1983060 := by exact prefixLift 1983060
  have htrace : WordTrace (prefixWord ++ tailWord_1983060) baseStart_1983060 baseEnd_1983060 := by
    simpa [prefixWord, tailWord_1983060, baseEnd_1983060] using wordTrace_append hprefix tailTrace_1983060
  have hstable : (prefixWord ++ tailWord_1983060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983060).length < 2 ^ (prefixWord ++ tailWord_1983060).sum := by decide
  have hdescent : baseEnd_1983060 < baseStart_1983060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983097 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 4, 1, 3]
def baseStart_1983097 : Nat := 118140960795 + 1983097 * 2 ^ 59
def prefixEnd_1983097 : Nat := 4983230072969 + 3 ^ 40 * 1983097 * 2
def baseEnd_1983097 : Nat := 1018281945489332857567409

theorem tailTrace_1983097 : CollatzResearch.WordTrace tailWord_1983097 prefixEnd_1983097 1018281945489332857567409 := by
  unfold tailWord_1983097
  simp only [CollatzResearch.WordTrace]
  refine ⟨72329489696585729848539545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48219659797723819899026363 72329489696585729848539545)
  ·
    refine ⟨54247117272439297386404659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72329489696585729848539545 54247117272439297386404659)
    ·
      refine ⟨81370675908658946079606989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54247117272439297386404659 81370675908658946079606989)
      ·
        refine ⟨30514003465747104779852621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81370675908658946079606989 30514003465747104779852621)
        ·
          refine ⟨11442751299655164292444733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30514003465747104779852621 11442751299655164292444733)
          ·
            refine ⟨4291031737370686609666775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11442751299655164292444733 4291031737370686609666775)
            ·
              refine ⟨6436547606056029914500163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4291031737370686609666775 6436547606056029914500163)
              ·
                refine ⟨9654821409084044871750245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6436547606056029914500163 9654821409084044871750245)
                ·
                  refine ⟨1810279014203258413453171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9654821409084044871750245 1810279014203258413453171)
                  ·
                    refine ⟨2715418521304887620179757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1810279014203258413453171 2715418521304887620179757)
                    ·
                      refine ⟨1018281945489332857567409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2715418521304887620179757 1018281945489332857567409)
                      ·
                        rfl

theorem cell23_1983097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_1983097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983097 prefixEnd_1983097 := by exact prefixLift 1983097
  have htrace : WordTrace (prefixWord ++ tailWord_1983097) baseStart_1983097 baseEnd_1983097 := by
    simpa [prefixWord, tailWord_1983097, baseEnd_1983097] using wordTrace_append hprefix tailTrace_1983097
  have hstable : (prefixWord ++ tailWord_1983097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983097).length < 2 ^ (prefixWord ++ tailWord_1983097).sum := by decide
  have hdescent : baseEnd_1983097 < baseStart_1983097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983103 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 4]
def baseStart_1983103 : Nat := 118140960795 + 1983103 * 2 ^ 59
def prefixEnd_1983103 : Nat := 4983230072969 + 3 ^ 40 * 1983103 * 2
def baseEnd_1983103 : Nat := 1018285026373259834092381

theorem tailTrace_1983103 : CollatzResearch.WordTrace tailWord_1983103 prefixEnd_1983103 1018285026373259834092381 := by
  unfold tailWord_1983103
  simp only [CollatzResearch.WordTrace]
  refine ⟨72329708534563992873257963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48219805689709328582171975 72329708534563992873257963)
  ·
    refine ⟨108494562801845989309886945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72329708534563992873257963 108494562801845989309886945)
    ·
      refine ⟨81370922101384491982415209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108494562801845989309886945 81370922101384491982415209)
      ·
        refine ⟨61028191576038368986811407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81370922101384491982415209 61028191576038368986811407)
        ·
          refine ⟨91542287364057553480217111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61028191576038368986811407 91542287364057553480217111)
          ·
            refine ⟨137313431046086330220325667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91542287364057553480217111 137313431046086330220325667)
            ·
              refine ⟨205970146569129495330488501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137313431046086330220325667 205970146569129495330488501)
              ·
                refine ⟨19309701240855890187233297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205970146569129495330488501 19309701240855890187233297)
                ·
                  refine ⟨14482275930641917640424973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19309701240855890187233297 14482275930641917640424973)
                  ·
                    refine ⟨5430853473990719115159365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14482275930641917640424973 5430853473990719115159365)
                    ·
                      refine ⟨1018285026373259834092381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5430853473990719115159365 1018285026373259834092381)
                      ·
                        rfl

theorem cell23_1983103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_1983103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983103 prefixEnd_1983103 := by exact prefixLift 1983103
  have htrace : WordTrace (prefixWord ++ tailWord_1983103) baseStart_1983103 baseEnd_1983103 := by
    simpa [prefixWord, tailWord_1983103, baseEnd_1983103] using wordTrace_append hprefix tailTrace_1983103
  have hstable : (prefixWord ++ tailWord_1983103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983103).length < 2 ^ (prefixWord ++ tailWord_1983103).sum := by decide
  have hdescent : baseEnd_1983103 < baseStart_1983103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983114 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_1983114 : Nat := 118140960795 + 1983114 * 2 ^ 59
def prefixEnd_1983114 : Nat := 4983230072969 + 3 ^ 40 * 1983114 * 2
def baseEnd_1983114 : Nat := 1018290674660459291054831

theorem tailTrace_1983114 : CollatzResearch.WordTrace tailWord_1983114 prefixEnd_1983114 1018290674660459291054831 := by
  unfold tailWord_1983114
  simp only [CollatzResearch.WordTrace]
  refine ⟨18082527434381035437977099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48220073158349427834605597 18082527434381035437977099)
  ·
    refine ⟨27123791151571553156965649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18082527434381035437977099 27123791151571553156965649)
    ·
      refine ⟨20342843363678664867724237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27123791151571553156965649 20342843363678664867724237)
      ·
        refine ⟨7628566261379499325396589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20342843363678664867724237 7628566261379499325396589)
        ·
          refine ⟨2860712348017312247023721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7628566261379499325396589 2860712348017312247023721)
          ·
            refine ⟨2145534261012984185267791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2860712348017312247023721 2145534261012984185267791)
            ·
              refine ⟨3218301391519476277901687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145534261012984185267791 3218301391519476277901687)
              ·
                refine ⟨4827452087279214416852531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218301391519476277901687 4827452087279214416852531)
                ·
                  refine ⟨7241178130918821625278797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4827452087279214416852531 7241178130918821625278797)
                  ·
                    refine ⟨2715441799094558109479549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7241178130918821625278797 2715441799094558109479549)
                    ·
                      refine ⟨1018290674660459291054831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2715441799094558109479549 1018290674660459291054831)
                      ·
                        rfl

theorem cell23_1983114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_1983114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983114 prefixEnd_1983114 := by exact prefixLift 1983114
  have htrace : WordTrace (prefixWord ++ tailWord_1983114) baseStart_1983114 baseEnd_1983114 := by
    simpa [prefixWord, tailWord_1983114, baseEnd_1983114] using wordTrace_append hprefix tailTrace_1983114
  have hstable : (prefixWord ++ tailWord_1983114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983114).length < 2 ^ (prefixWord ++ tailWord_1983114).sum := by decide
  have hdescent : baseEnd_1983114 < baseStart_1983114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983123 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 5]
def baseStart_1983123 : Nat := 118140960795 + 1983123 * 2 ^ 59
def prefixEnd_1983123 : Nat := 4983230072969 + 3 ^ 40 * 1983123 * 2
def baseEnd_1983123 : Nat := 1018295295986349755842289

theorem tailTrace_1983123 : CollatzResearch.WordTrace tailWord_1983123 prefixEnd_1983123 1018295295986349755842289 := by
  unfold tailWord_1983123
  simp only [CollatzResearch.WordTrace]
  refine ⟨72330437994491536288986023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48220291996327690859324015 72330437994491536288986023)
  ·
    refine ⟨108495656991737304433479035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72330437994491536288986023 108495656991737304433479035)
    ·
      refine ⟨162743485487605956650218553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108495656991737304433479035 162743485487605956650218553)
      ·
        refine ⟨122057614115704467487663915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162743485487605956650218553 122057614115704467487663915)
        ·
          refine ⟨183086421173556701231495873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122057614115704467487663915 183086421173556701231495873)
          ·
            refine ⟨137314815880167525923621905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183086421173556701231495873 137314815880167525923621905)
            ·
              refine ⟨102986111910125644442716429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137314815880167525923621905 102986111910125644442716429)
              ·
                refine ⟨38619791966297116666018661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102986111910125644442716429 38619791966297116666018661)
                ·
                  refine ⟨7241210993680709374878499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38619791966297116666018661 7241210993680709374878499)
                  ·
                    refine ⟨10861816490521064062317749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7241210993680709374878499 10861816490521064062317749)
                    ·
                      refine ⟨1018295295986349755842289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10861816490521064062317749 1018295295986349755842289)
                      ·
                        rfl

theorem cell23_1983123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_1983123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983123 prefixEnd_1983123 := by exact prefixLift 1983123
  have htrace : WordTrace (prefixWord ++ tailWord_1983123) baseStart_1983123 baseEnd_1983123 := by
    simpa [prefixWord, tailWord_1983123, baseEnd_1983123] using wordTrace_append hprefix tailTrace_1983123
  have hstable : (prefixWord ++ tailWord_1983123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983123).length < 2 ^ (prefixWord ++ tailWord_1983123).sum := by decide
  have hdescent : baseEnd_1983123 < baseStart_1983123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983140 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1983140 : Nat := 118140960795 + 1983140 * 2 ^ 59
def prefixEnd_1983140 : Nat := 4983230072969 + 3 ^ 40 * 1983140 * 2
def baseEnd_1983140 : Nat := 1018304025157476189329711

theorem tailTrace_1983140 : CollatzResearch.WordTrace tailWord_1983140 prefixEnd_1983140 1018304025157476189329711 := by
  unfold tailWord_1983140
  simp only [CollatzResearch.WordTrace]
  refine ⟨36165529017714974096177437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48220705356953298794903249 36165529017714974096177437)
  ·
    refine ⟨13562073381643115286066539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36165529017714974096177437 13562073381643115286066539)
    ·
      refine ⟨20343110072464672929099809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13562073381643115286066539 20343110072464672929099809)
      ·
        refine ⟨15257332554348504696824857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20343110072464672929099809 15257332554348504696824857)
        ·
          refine ⟨11442999415761378522618643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15257332554348504696824857 11442999415761378522618643)
          ·
            refine ⟨17164499123642067783927965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11442999415761378522618643 17164499123642067783927965)
            ·
              refine ⟨6436687171365775418972987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17164499123642067783927965 6436687171365775418972987)
              ·
                refine ⟨9655030757048663128459481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6436687171365775418972987 9655030757048663128459481)
                ·
                  refine ⟨7241273067786497346344611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9655030757048663128459481 7241273067786497346344611)
                  ·
                    refine ⟨10861909601679746019516917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7241273067786497346344611 10861909601679746019516917)
                    ·
                      refine ⟨1018304025157476189329711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10861909601679746019516917 1018304025157476189329711)
                      ·
                        rfl

theorem cell23_1983140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1983140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983140 prefixEnd_1983140 := by exact prefixLift 1983140
  have htrace : WordTrace (prefixWord ++ tailWord_1983140) baseStart_1983140 baseEnd_1983140 := by
    simpa [prefixWord, tailWord_1983140, baseEnd_1983140] using wordTrace_append hprefix tailTrace_1983140
  have hstable : (prefixWord ++ tailWord_1983140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983140).length < 2 ^ (prefixWord ++ tailWord_1983140).sum := by decide
  have hdescent : baseEnd_1983140 < baseStart_1983140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983154 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2]
def baseStart_1983154 : Nat := 118140960795 + 1983154 * 2 ^ 59
def prefixEnd_1983154 : Nat := 4983230072969 + 3 ^ 40 * 1983154 * 2
def baseEnd_1983154 : Nat := 1018311213886639134554647

theorem tailTrace_1983154 : CollatzResearch.WordTrace tailWord_1983154 prefixEnd_1983154 1018311213886639134554647 := by
  unfold tailWord_1983154
  simp only [CollatzResearch.WordTrace]
  refine ⟨18082892164344807145841129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48221045771586152388909677 18082892164344807145841129)
  ·
    refine ⟨13562169123258605359380847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18082892164344807145841129 13562169123258605359380847)
    ·
      refine ⟨20343253684887908039071271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13562169123258605359380847 20343253684887908039071271)
      ·
        refine ⟨30514880527331862058606907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20343253684887908039071271 30514880527331862058606907)
        ·
          refine ⟨45772320790997793087910361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30514880527331862058606907 45772320790997793087910361)
          ·
            refine ⟨34329240593248344815932771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45772320790997793087910361 34329240593248344815932771)
            ·
              refine ⟨51493860889872517223899157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34329240593248344815932771 51493860889872517223899157)
              ·
                refine ⟨2413774729212774244870273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51493860889872517223899157 2413774729212774244870273)
                ·
                  refine ⟨1810331046909580683652705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2413774729212774244870273 1810331046909580683652705)
                  ·
                    refine ⟨1357748285182185512739529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1810331046909580683652705 1357748285182185512739529)
                    ·
                      refine ⟨1018311213886639134554647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1357748285182185512739529 1018311213886639134554647)
                      ·
                        rfl

theorem cell23_1983154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_1983154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983154 prefixEnd_1983154 := by exact prefixLift 1983154
  have htrace : WordTrace (prefixWord ++ tailWord_1983154) baseStart_1983154 baseEnd_1983154 := by
    simpa [prefixWord, tailWord_1983154, baseEnd_1983154] using wordTrace_append hprefix tailTrace_1983154
  have hstable : (prefixWord ++ tailWord_1983154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983154).length < 2 ^ (prefixWord ++ tailWord_1983154).sum := by decide
  have hdescent : baseEnd_1983154 < baseStart_1983154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983210 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1983210 : Nat := 118140960795 + 1983210 * 2 ^ 59
def prefixEnd_1983210 : Nat := 4983230072969 + 3 ^ 40 * 1983210 * 2
def baseEnd_1983210 : Nat := 1018339968803290915454389

theorem tailTrace_1983210 : CollatzResearch.WordTrace tailWord_1983210 prefixEnd_1983210 1018339968803290915454389 := by
  unfold tailWord_1983210
  simp only [CollatzResearch.WordTrace]
  refine ⟨18083402786294087536850771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48222407430117566764935389 18083402786294087536850771)
  ·
    refine ⟨27125104179441131305276157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18083402786294087536850771 27125104179441131305276157)
    ·
      refine ⟨10171914067290424239478559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27125104179441131305276157 10171914067290424239478559)
      ·
        refine ⟨15257871100935636359217839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10171914067290424239478559 15257871100935636359217839)
        ·
          refine ⟨22886806651403454538826759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15257871100935636359217839 22886806651403454538826759)
          ·
            refine ⟨34330209977105181808240139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22886806651403454538826759 34330209977105181808240139)
            ·
              refine ⟨51495314965657772712360209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34330209977105181808240139 51495314965657772712360209)
              ·
                refine ⟨38621486224243329534270157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51495314965657772712360209 38621486224243329534270157)
                ·
                  refine ⟨14483057334091248575351309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38621486224243329534270157 14483057334091248575351309)
                  ·
                    refine ⟨5431146500284218215756741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14483057334091248575351309 5431146500284218215756741)
                    ·
                      refine ⟨1018339968803290915454389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5431146500284218215756741 1018339968803290915454389)
                      ·
                        rfl

theorem cell23_1983210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1983210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983210 prefixEnd_1983210 := by exact prefixLift 1983210
  have htrace : WordTrace (prefixWord ++ tailWord_1983210) baseStart_1983210 baseEnd_1983210 := by
    simpa [prefixWord, tailWord_1983210, baseEnd_1983210] using wordTrace_append hprefix tailTrace_1983210
  have hstable : (prefixWord ++ tailWord_1983210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983210).length < 2 ^ (prefixWord ++ tailWord_1983210).sum := by decide
  have hdescent : baseEnd_1983210 < baseStart_1983210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983280 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 5, 5]
def baseStart_1983280 : Nat := 118140960795 + 1983280 * 2 ^ 59
def prefixEnd_1983280 : Nat := 4983230072969 + 3 ^ 40 * 1983280 * 2
def baseEnd_1983280 : Nat := 339458637483035213859689

theorem tailTrace_1983280 : CollatzResearch.WordTrace tailWord_1983280 prefixEnd_1983280 339458637483035213859689 := by
  unfold tailWord_1983280
  simp only [CollatzResearch.WordTrace]
  refine ⟨36168082127461376051225647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48224109503281834734967529 36168082127461376051225647)
  ·
    refine ⟨54252123191192064076838471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36168082127461376051225647 54252123191192064076838471)
    ·
      refine ⟨81378184786788096115257707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54252123191192064076838471 81378184786788096115257707)
      ·
        refine ⟨122067277180182144172886561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81378184786788096115257707 122067277180182144172886561)
        ·
          refine ⟨91550457885136608129664921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122067277180182144172886561 91550457885136608129664921)
          ·
            refine ⟨68662843413852456097248691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91550457885136608129664921 68662843413852456097248691)
            ·
              refine ⟨102994265120778684145873037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68662843413852456097248691 102994265120778684145873037)
              ·
                refine ⟨38622849420292006554702389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102994265120778684145873037 38622849420292006554702389)
                ·
                  refine ⟨3620892133152375614503349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38622849420292006554702389 3620892133152375614503349)
                  ·
                    refine ⟨339458637483035213859689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3620892133152375614503349 339458637483035213859689)
                    ·
                      rfl

theorem cell23_1983280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 5].length) (baseStart_1983280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983280 prefixEnd_1983280 := by exact prefixLift 1983280
  have htrace : WordTrace (prefixWord ++ tailWord_1983280) baseStart_1983280 baseEnd_1983280 := by
    simpa [prefixWord, tailWord_1983280, baseEnd_1983280] using wordTrace_append hprefix tailTrace_1983280
  have hstable : (prefixWord ++ tailWord_1983280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983280).length < 2 ^ (prefixWord ++ tailWord_1983280).sum := by decide
  have hdescent : baseEnd_1983280 < baseStart_1983280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983287 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 3, 5, 2]
def baseStart_1983287 : Nat := 118140960795 + 1983287 * 2 ^ 59
def prefixEnd_1983287 : Nat := 4983230072969 + 3 ^ 40 * 1983287 * 2
def baseEnd_1983287 : Nat := 1018379506813687114191535

theorem tailTrace_1983287 : CollatzResearch.WordTrace tailWord_1983287 prefixEnd_1983287 1018379506813687114191535 := by
  unfold tailWord_1983287
  simp only [CollatzResearch.WordTrace]
  refine ⟨72336419565897392297956115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48224279710598261531970743 72336419565897392297956115)
  ·
    refine ⟨108504629348846088446934173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72336419565897392297956115 108504629348846088446934173)
    ·
      refine ⟨40689236005817283167600315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108504629348846088446934173 40689236005817283167600315)
      ·
        refine ⟨61033854008725924751400473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40689236005817283167600315 61033854008725924751400473)
        ·
          refine ⟨45775390506544443563550355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61033854008725924751400473 45775390506544443563550355)
          ·
            refine ⟨68663085759816665345325533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45775390506544443563550355 68663085759816665345325533)
            ·
              refine ⟨25748657159931249504497075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68663085759816665345325533 25748657159931249504497075)
              ·
                refine ⟨38622985739896874256745613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25748657159931249504497075 38622985739896874256745613)
                ·
                  refine ⟨14483619652461327846279605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38622985739896874256745613 14483619652461327846279605)
                  ·
                    refine ⟨1357839342418249485588713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14483619652461327846279605 1357839342418249485588713)
                    ·
                      refine ⟨1018379506813687114191535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1357839342418249485588713 1018379506813687114191535)
                      ·
                        rfl

theorem cell23_1983287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 5, 2].length) (baseStart_1983287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983287 prefixEnd_1983287 := by exact prefixLift 1983287
  have htrace : WordTrace (prefixWord ++ tailWord_1983287) baseStart_1983287 baseEnd_1983287 := by
    simpa [prefixWord, tailWord_1983287, baseEnd_1983287] using wordTrace_append hprefix tailTrace_1983287
  have hstable : (prefixWord ++ tailWord_1983287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983287).length < 2 ^ (prefixWord ++ tailWord_1983287).sum := by decide
  have hdescent : baseEnd_1983287 < baseStart_1983287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983304 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 2, 3, 2]
def baseStart_1983304 : Nat := 118140960795 + 1983304 * 2 ^ 59
def prefixEnd_1983304 : Nat := 4983230072969 + 3 ^ 40 * 1983304 * 2
def baseEnd_1983304 : Nat := 1018388235984813547678957

theorem tailTrace_1983304 : CollatzResearch.WordTrace tailWord_1983304 prefixEnd_1983304 1018388235984813547678957 := by
  unfold tailWord_1983304
  simp only [CollatzResearch.WordTrace]
  refine ⟨36168519803417902100662483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48224693071223869467549977 36168519803417902100662483)
  ·
    refine ⟨54252779705126853150993725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36168519803417902100662483 54252779705126853150993725)
    ·
      refine ⟨20344792389422569931622647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54252779705126853150993725 20344792389422569931622647)
      ·
        refine ⟨30517188584133854897433971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20344792389422569931622647 30517188584133854897433971)
        ·
          refine ⟨45775782876200782346150957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30517188584133854897433971 45775782876200782346150957)
          ·
            refine ⟨17165918578575293379806609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45775782876200782346150957 17165918578575293379806609)
            ·
              refine ⟨12874438933931470034854957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17165918578575293379806609 12874438933931470034854957)
              ·
                refine ⟨4827914600224301263070609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12874438933931470034854957 4827914600224301263070609)
                ·
                  refine ⟨3620935950168225947302957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4827914600224301263070609 3620935950168225947302957)
                  ·
                    refine ⟨1357850981313084730238609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3620935950168225947302957 1357850981313084730238609)
                    ·
                      refine ⟨1018388235984813547678957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1357850981313084730238609 1018388235984813547678957)
                      ·
                        rfl

theorem cell23_1983304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_1983304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983304 prefixEnd_1983304 := by exact prefixLift 1983304
  have htrace : WordTrace (prefixWord ++ tailWord_1983304) baseStart_1983304 baseEnd_1983304 := by
    simpa [prefixWord, tailWord_1983304, baseEnd_1983304] using wordTrace_append hprefix tailTrace_1983304
  have hstable : (prefixWord ++ tailWord_1983304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983304).length < 2 ^ (prefixWord ++ tailWord_1983304).sum := by decide
  have hdescent : baseEnd_1983304 < baseStart_1983304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983327 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 4, 4]
def baseStart_1983327 : Nat := 118140960795 + 1983327 * 2 ^ 59
def prefixEnd_1983327 : Nat := 4983230072969 + 3 ^ 40 * 1983327 * 2
def baseEnd_1983327 : Nat := 339466682013288985897117

theorem tailTrace_1983327 : CollatzResearch.WordTrace tailWord_1983327 prefixEnd_1983327 339466682013288985897117 := by
  unfold tailWord_1983327
  simp only [CollatzResearch.WordTrace]
  refine ⟨72337878485752479129412235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48225252323834986086274823 72337878485752479129412235)
  ·
    refine ⟨108506817728628718694118353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72337878485752479129412235 108506817728628718694118353)
    ·
      refine ⟨81380113296471539020588765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108506817728628718694118353 81380113296471539020588765)
      ·
        refine ⟨30517542486176827132720787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81380113296471539020588765 30517542486176827132720787)
        ·
          refine ⟨45776313729265240699081181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30517542486176827132720787 45776313729265240699081181)
          ·
            refine ⟨17166117648474465262155443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45776313729265240699081181 17166117648474465262155443)
            ·
              refine ⟨25749176472711697893233165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17166117648474465262155443 25749176472711697893233165)
              ·
                refine ⟨9655941177266886709962437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25749176472711697893233165 9655941177266886709962437)
                ·
                  refine ⟨1810488970737541258117957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9655941177266886709962437 1810488970737541258117957)
                  ·
                    refine ⟨339466682013288985897117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1810488970737541258117957 339466682013288985897117)
                    ·
                      rfl

theorem cell23_1983327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 4].length) (baseStart_1983327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983327 prefixEnd_1983327 := by exact prefixLift 1983327
  have htrace : WordTrace (prefixWord ++ tailWord_1983327) baseStart_1983327 baseEnd_1983327 := by
    simpa [prefixWord, tailWord_1983327, baseEnd_1983327] using wordTrace_append hprefix tailTrace_1983327
  have hstable : (prefixWord ++ tailWord_1983327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983327).length < 2 ^ (prefixWord ++ tailWord_1983327).sum := by decide
  have hdescent : baseEnd_1983327 < baseStart_1983327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983328 : List Nat := [2, 1, 1, 3, 3, 1, 5, 2, 1, 1, 3]
def baseStart_1983328 : Nat := 118140960795 + 1983328 * 2 ^ 59
def prefixEnd_1983328 : Nat := 4983230072969 + 3 ^ 40 * 1983328 * 2
def baseEnd_1983328 : Nat := 1018400559520521453778847

theorem tailTrace_1983328 : CollatzResearch.WordTrace tailWord_1983328 prefixEnd_1983328 1018400559520521453778847 := by
  unfold tailWord_1983328
  simp only [CollatzResearch.WordTrace]
  refine ⟨36168957479374428150099319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48225276639165904200132425 36168957479374428150099319)
  ·
    refine ⟨54253436219061642225148979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36168957479374428150099319 54253436219061642225148979)
    ·
      refine ⟨81380154328592463337723469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54253436219061642225148979 81380154328592463337723469)
      ·
        refine ⟨30517557873222173751646301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81380154328592463337723469 30517557873222173751646301)
        ·
          refine ⟨11444084202458315156867363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30517557873222173751646301 11444084202458315156867363)
          ·
            refine ⟨17166126303687472735301045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11444084202458315156867363 17166126303687472735301045)
            ·
              refine ⟨1609324340970700568934473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17166126303687472735301045 1609324340970700568934473)
              ·
                refine ⟨1206993255728025426700855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609324340970700568934473 1206993255728025426700855)
                ·
                  refine ⟨1810489883592038140051283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1206993255728025426700855 1810489883592038140051283)
                  ·
                    refine ⟨2715734825388057210076925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1810489883592038140051283 2715734825388057210076925)
                    ·
                      refine ⟨1018400559520521453778847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2715734825388057210076925 1018400559520521453778847)
                      ·
                        rfl

theorem cell23_1983328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_1983328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983328 prefixEnd_1983328 := by exact prefixLift 1983328
  have htrace : WordTrace (prefixWord ++ tailWord_1983328) baseStart_1983328 baseEnd_1983328 := by
    simpa [prefixWord, tailWord_1983328, baseEnd_1983328] using wordTrace_append hprefix tailTrace_1983328
  have hstable : (prefixWord ++ tailWord_1983328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983328).length < 2 ^ (prefixWord ++ tailWord_1983328).sum := by decide
  have hdescent : baseEnd_1983328 < baseStart_1983328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983378 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1983378 : Nat := 118140960795 + 1983378 * 2 ^ 59
def prefixEnd_1983378 : Nat := 4983230072969 + 3 ^ 40 * 1983378 * 2
def baseEnd_1983378 : Nat := 339475411184415419384539

theorem tailTrace_1983378 : CollatzResearch.WordTrace tailWord_1983378 prefixEnd_1983378 339475411184415419384539 := by
  unfold tailWord_1983378
  simp only [CollatzResearch.WordTrace]
  refine ⟨18084934652141928709879697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48226492405711809893012525 18084934652141928709879697)
  ·
    refine ⟨13563700989106446532409773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18084934652141928709879697 13563700989106446532409773)
    ·
      refine ⟨5086387870914917449653665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13563700989106446532409773 5086387870914917449653665)
      ·
        refine ⟨3814790903186188087240249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5086387870914917449653665 3814790903186188087240249)
        ·
          refine ⟨2861093177389641065430187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3814790903186188087240249 2861093177389641065430187)
          ·
            refine ⟨4291639766084461598145281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861093177389641065430187 4291639766084461598145281)
            ·
              refine ⟨3218729824563346198608961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4291639766084461598145281 3218729824563346198608961)
              ·
                refine ⟨2414047368422509648956721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218729824563346198608961 2414047368422509648956721)
                ·
                  refine ⟨1810535526316882236717541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2414047368422509648956721 1810535526316882236717541)
                  ·
                    refine ⟨339475411184415419384539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1810535526316882236717541 339475411184415419384539)
                    ·
                      rfl

theorem cell23_1983378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1983378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983378 prefixEnd_1983378 := by exact prefixLift 1983378
  have htrace : WordTrace (prefixWord ++ tailWord_1983378) baseStart_1983378 baseEnd_1983378 := by
    simpa [prefixWord, tailWord_1983378, baseEnd_1983378] using wordTrace_append hprefix tailTrace_1983378
  have hstable : (prefixWord ++ tailWord_1983378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983378).length < 2 ^ (prefixWord ++ tailWord_1983378).sum := by decide
  have hdescent : baseEnd_1983378 < baseStart_1983378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983427 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 3]
def baseStart_1983427 : Nat := 118140960795 + 1983427 * 2 ^ 59
def prefixEnd_1983427 : Nat := 4983230072969 + 3 ^ 40 * 1983427 * 2
def baseEnd_1983427 : Nat := 1018451394105316566440891

theorem tailTrace_1983427 : CollatzResearch.WordTrace tailWord_1983427 prefixEnd_1983427 1018451394105316566440891 := by
  unfold tailWord_1983427
  simp only [CollatzResearch.WordTrace]
  refine ⟨72341525785390196208052535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48227683856926797472035023 72341525785390196208052535)
  ·
    refine ⟨108512288678085294312078803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72341525785390196208052535 108512288678085294312078803)
    ·
      refine ⟨162768433017127941468118205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108512288678085294312078803 162768433017127941468118205)
      ·
        refine ⟨61038162381422978050544327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162768433017127941468118205 61038162381422978050544327)
        ·
          refine ⟨91557243572134467075816491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61038162381422978050544327 91557243572134467075816491)
          ·
            refine ⟨137335865358201700613724737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91557243572134467075816491 137335865358201700613724737)
            ·
              refine ⟨103001899018651275460293553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137335865358201700613724737 103001899018651275460293553)
              ·
                refine ⟨77251424263988456595220165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103001899018651275460293553 77251424263988456595220165)
                ·
                  refine ⟨14484642049497835611603781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77251424263988456595220165 14484642049497835611603781)
                  ·
                    refine ⟨2715870384280844177175709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14484642049497835611603781 2715870384280844177175709)
                    ·
                      refine ⟨1018451394105316566440891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2715870384280844177175709 1018451394105316566440891)
                      ·
                        rfl

theorem cell23_1983427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_1983427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983427 prefixEnd_1983427 := by exact prefixLift 1983427
  have htrace : WordTrace (prefixWord ++ tailWord_1983427) baseStart_1983427 baseEnd_1983427 := by
    simpa [prefixWord, tailWord_1983427, baseEnd_1983427] using wordTrace_append hprefix tailTrace_1983427
  have hstable : (prefixWord ++ tailWord_1983427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983427).length < 2 ^ (prefixWord ++ tailWord_1983427).sum := by decide
  have hdescent : baseEnd_1983427 < baseStart_1983427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983441 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 4, 2, 2]
def baseStart_1983441 : Nat := 118140960795 + 1983441 * 2 ^ 59
def prefixEnd_1983441 : Nat := 4983230072969 + 3 ^ 40 * 1983441 * 2
def baseEnd_1983441 : Nat := 1018458582834479511665827

theorem tailTrace_1983441 : CollatzResearch.WordTrace tailWord_1983441 prefixEnd_1983441 1018458582834479511665827 := by
  unfold tailWord_1983441
  simp only [CollatzResearch.WordTrace]
  refine ⟨72342036407339476599062177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48228024271559651066041451 72342036407339476599062177)
  ·
    refine ⟨54256527305504607449296633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72342036407339476599062177 54256527305504607449296633)
    ·
      refine ⟨40692395479128455586972475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54256527305504607449296633 40692395479128455586972475)
      ·
        refine ⟨61038593218692683380458713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40692395479128455586972475 61038593218692683380458713)
        ·
          refine ⟨45778944914019512535344035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61038593218692683380458713 45778944914019512535344035)
          ·
            refine ⟨68668417371029268803016053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45778944914019512535344035 68668417371029268803016053)
            ·
              refine ⟨6437664128533993950282755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68668417371029268803016053 6437664128533993950282755)
              ·
                refine ⟨9656496192800990925424133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6437664128533993950282755 9656496192800990925424133)
                ·
                  refine ⟨1810593036150185798517025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9656496192800990925424133 1810593036150185798517025)
                  ·
                    refine ⟨1357944777112639348887769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1810593036150185798517025 1357944777112639348887769)
                    ·
                      refine ⟨1018458582834479511665827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1357944777112639348887769 1018458582834479511665827)
                      ·
                        rfl

theorem cell23_1983441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 4, 2, 2].length) (baseStart_1983441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983441 prefixEnd_1983441 := by exact prefixLift 1983441
  have htrace : WordTrace (prefixWord ++ tailWord_1983441) baseStart_1983441 baseEnd_1983441 := by
    simpa [prefixWord, tailWord_1983441, baseEnd_1983441] using wordTrace_append hprefix tailTrace_1983441
  have hstable : (prefixWord ++ tailWord_1983441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983441).length < 2 ^ (prefixWord ++ tailWord_1983441).sum := by decide
  have hdescent : baseEnd_1983441 < baseStart_1983441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983498 : List Nat := [3, 1, 2, 2, 3, 2, 3, 2, 5]
def baseStart_1983498 : Nat := 118140960795 + 1983498 * 2 ^ 59
def prefixEnd_1983498 : Nat := 4983230072969 + 3 ^ 40 * 1983498 * 2
def baseEnd_1983498 : Nat := 113165316803531754294785

theorem tailTrace_1983498 : CollatzResearch.WordTrace tailWord_1983498 prefixEnd_1983498 113165316803531754294785 := by
  unfold tailWord_1983498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18086028842033243833471787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48229410245421983555924765 18086028842033243833471787)
  ·
    refine ⟨27129043263049865750207681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18086028842033243833471787 27129043263049865750207681)
    ·
      refine ⟨20346782447287399312655761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27129043263049865750207681 20346782447287399312655761)
      ·
        refine ⟨15260086835465549484491821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20346782447287399312655761 15260086835465549484491821)
        ·
          refine ⟨5722532563299581056684433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15260086835465549484491821 5722532563299581056684433)
          ·
            refine ⟨4291899422474685792513325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5722532563299581056684433 4291899422474685792513325)
            ·
              refine ⟨1609462283428007172192497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4291899422474685792513325 1609462283428007172192497)
              ·
                refine ⟨1207096712571005379144373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609462283428007172192497 1207096712571005379144373)
                ·
                  refine ⟨113165316803531754294785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1207096712571005379144373 113165316803531754294785)
                  ·
                    rfl

theorem cell23_1983498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 2, 5].length) (baseStart_1983498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983498 prefixEnd_1983498 := by exact prefixLift 1983498
  have htrace : WordTrace (prefixWord ++ tailWord_1983498) baseStart_1983498 baseEnd_1983498 := by
    simpa [prefixWord, tailWord_1983498, baseEnd_1983498] using wordTrace_append hprefix tailTrace_1983498
  have hstable : (prefixWord ++ tailWord_1983498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983498).length < 2 ^ (prefixWord ++ tailWord_1983498).sum := by decide
  have hdescent : baseEnd_1983498 < baseStart_1983498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983514 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_1983514 : Nat := 118140960795 + 1983514 * 2 ^ 59
def prefixEnd_1983514 : Nat := 4983230072969 + 3 ^ 40 * 1983514 * 2
def baseEnd_1983514 : Nat := 1018496066922257726052991

theorem tailTrace_1983514 : CollatzResearch.WordTrace tailWord_1983514 prefixEnd_1983514 1018496066922257726052991 := by
  unfold tailWord_1983514
  simp only [CollatzResearch.WordTrace]
  refine ⟨18086174734018752516617399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48229799290716673377646397 18086174734018752516617399)
  ·
    refine ⟨27129262101028128774926099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18086174734018752516617399 27129262101028128774926099)
    ·
      refine ⟨40693893151542193162389149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27129262101028128774926099 40693893151542193162389149)
      ·
        refine ⟨15260209931828322435895931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40693893151542193162389149 15260209931828322435895931)
        ·
          refine ⟨22890314897742483653843897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15260209931828322435895931 22890314897742483653843897)
          ·
            refine ⟨17167736173306862740382923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22890314897742483653843897 17167736173306862740382923)
            ·
              refine ⟨25751604259960294110574385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17167736173306862740382923 25751604259960294110574385)
              ·
                refine ⟨19313703194970220582930789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25751604259960294110574385 19313703194970220582930789)
                ·
                  refine ⟨3621319349056916359299523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19313703194970220582930789 3621319349056916359299523)
                  ·
                    refine ⟨5431979023585374538949285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3621319349056916359299523 5431979023585374538949285)
                    ·
                      refine ⟨1018496066922257726052991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5431979023585374538949285 1018496066922257726052991)
                      ·
                        rfl

theorem cell23_1983514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_1983514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983514 prefixEnd_1983514 := by exact prefixLift 1983514
  have htrace : WordTrace (prefixWord ++ tailWord_1983514) baseStart_1983514 baseEnd_1983514 := by
    simpa [prefixWord, tailWord_1983514, baseEnd_1983514] using wordTrace_append hprefix tailTrace_1983514
  have hstable : (prefixWord ++ tailWord_1983514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983514).length < 2 ^ (prefixWord ++ tailWord_1983514).sum := by decide
  have hdescent : baseEnd_1983514 < baseStart_1983514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983564 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1983564 : Nat := 118140960795 + 1983564 * 2 ^ 59
def prefixEnd_1983564 : Nat := 4983230072969 + 3 ^ 40 * 1983564 * 2
def baseEnd_1983564 : Nat := 1018521740954982530427761

theorem tailTrace_1983564 : CollatzResearch.WordTrace tailWord_1983564 prefixEnd_1983564 1018521740954982530427761 := by
  unfold tailWord_1983564
  simp only [CollatzResearch.WordTrace]
  refine ⟨36173261292946934302894873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48231015057262579070526497 36173261292946934302894873)
  ·
    refine ⟨27129945969710200727171155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36173261292946934302894873 27129945969710200727171155)
    ·
      refine ⟨40694918954565301090756733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27129945969710200727171155 40694918954565301090756733)
      ·
        refine ⟨15260594607961987909033775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40694918954565301090756733 15260594607961987909033775)
        ·
          refine ⟨22890891911942981863550663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15260594607961987909033775 22890891911942981863550663)
          ·
            refine ⟨34336337867914472795325995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22890891911942981863550663 34336337867914472795325995)
            ·
              refine ⟨51504506801871709192988993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34336337867914472795325995 51504506801871709192988993)
              ·
                refine ⟨38628380101403781894741745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51504506801871709192988993 38628380101403781894741745)
                ·
                  refine ⟨28971285076052836421056309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38628380101403781894741745 28971285076052836421056309)
                  ·
                    refine ⟨2716057975879953414474029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28971285076052836421056309 2716057975879953414474029)
                    ·
                      refine ⟨1018521740954982530427761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2716057975879953414474029 1018521740954982530427761)
                      ·
                        rfl

theorem cell23_1983564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1983564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983564 prefixEnd_1983564 := by exact prefixLift 1983564
  have htrace : WordTrace (prefixWord ++ tailWord_1983564) baseStart_1983564 baseEnd_1983564 := by
    simpa [prefixWord, tailWord_1983564, baseEnd_1983564] using wordTrace_append hprefix tailTrace_1983564
  have hstable : (prefixWord ++ tailWord_1983564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983564).length < 2 ^ (prefixWord ++ tailWord_1983564).sum := by decide
  have hdescent : baseEnd_1983564 < baseStart_1983564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983567 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 1, 11]
def baseStart_1983567 : Nat := 118140960795 + 1983567 * 2 ^ 59
def prefixEnd_1983567 : Nat := 4983230072969 + 3 ^ 40 * 1983567 * 2
def baseEnd_1983567 : Nat := 339507760465648672896749

theorem tailTrace_1983567 : CollatzResearch.WordTrace tailWord_1983567 prefixEnd_1983567 339507760465648672896749 := by
  unfold tailWord_1983567
  simp only [CollatzResearch.WordTrace]
  refine ⟨72346632004883000118148955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48231088003255333412099303 72346632004883000118148955)
  ·
    refine ⟨108519948007324500177223433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72346632004883000118148955 108519948007324500177223433)
    ·
      refine ⟨81389961005493375132917575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108519948007324500177223433 81389961005493375132917575)
      ·
        refine ⟨122084941508240062699376363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81389961005493375132917575 122084941508240062699376363)
        ·
          refine ⟨183127412262360094049064545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122084941508240062699376363 183127412262360094049064545)
          ·
            refine ⟨137345559196770070536798409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183127412262360094049064545 137345559196770070536798409)
            ·
              refine ⟨103009169397577552902598807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137345559196770070536798409 103009169397577552902598807)
              ·
                refine ⟨154513754096366329353898211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103009169397577552902598807 154513754096366329353898211)
                ·
                  refine ⟨231770631144549494030847317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154513754096366329353898211 231770631144549494030847317)
                  ·
                    refine ⟨339507760465648672896749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 231770631144549494030847317 339507760465648672896749)
                    ·
                      rfl

theorem cell23_1983567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_1983567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983567 prefixEnd_1983567 := by exact prefixLift 1983567
  have htrace : WordTrace (prefixWord ++ tailWord_1983567) baseStart_1983567 baseEnd_1983567 := by
    simpa [prefixWord, tailWord_1983567, baseEnd_1983567] using wordTrace_append hprefix tailTrace_1983567
  have hstable : (prefixWord ++ tailWord_1983567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983567).length < 2 ^ (prefixWord ++ tailWord_1983567).sum := by decide
  have hdescent : baseEnd_1983567 < baseStart_1983567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983582 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1983582 : Nat := 118140960795 + 1983582 * 2 ^ 59
def prefixEnd_1983582 : Nat := 4983230072969 + 3 ^ 40 * 1983582 * 2
def baseEnd_1983582 : Nat := 1018530983606763460002679

theorem tailTrace_1983582 : CollatzResearch.WordTrace tailWord_1983582 prefixEnd_1983582 1018530983606763460002679 := by
  unfold tailWord_1983582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9043397387478582209993125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48231452733219105119963333 9043397387478582209993125)
  ·
    refine ⟨1695637010152234164373711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9043397387478582209993125 1695637010152234164373711)
    ·
      refine ⟨2543455515228351246560567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1695637010152234164373711 2543455515228351246560567)
      ·
        refine ⟨3815183272842526869840851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543455515228351246560567 3815183272842526869840851)
        ·
          refine ⟨5722774909263790304761277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815183272842526869840851 5722774909263790304761277)
          ·
            refine ⟨2146040590973921364285479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5722774909263790304761277 2146040590973921364285479)
            ·
              refine ⟨3219060886460882046428219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146040590973921364285479 3219060886460882046428219)
              ·
                refine ⟨4828591329691323069642329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219060886460882046428219 4828591329691323069642329)
                ·
                  refine ⟨3621443497268492302231747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4828591329691323069642329 3621443497268492302231747)
                  ·
                    refine ⟨5432165245902738453347621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3621443497268492302231747 5432165245902738453347621)
                    ·
                      refine ⟨1018530983606763460002679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5432165245902738453347621 1018530983606763460002679)
                      ·
                        rfl

theorem cell23_1983582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1983582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983582 prefixEnd_1983582 := by exact prefixLift 1983582
  have htrace : WordTrace (prefixWord ++ tailWord_1983582) baseStart_1983582 baseEnd_1983582 := by
    simpa [prefixWord, tailWord_1983582, baseEnd_1983582] using wordTrace_append hprefix tailTrace_1983582
  have hstable : (prefixWord ++ tailWord_1983582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983582).length < 2 ^ (prefixWord ++ tailWord_1983582).sum := by decide
  have hdescent : baseEnd_1983582 < baseStart_1983582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983584 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 3, 5]
def baseStart_1983584 : Nat := 118140960795 + 1983584 * 2 ^ 59
def prefixEnd_1983584 : Nat := 4983230072969 + 3 ^ 40 * 1983584 * 2
def baseEnd_1983584 : Nat := 339510670189357484059223

theorem tailTrace_1983584 : CollatzResearch.WordTrace tailWord_1983584 prefixEnd_1983584 339510670189357484059223 := by
  unfold tailWord_1983584
  simp only [CollatzResearch.WordTrace]
  refine ⟨36173626022910706010758903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48231501363880941347678537 36173626022910706010758903)
  ·
    refine ⟨54260439034366059016138355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36173626022910706010758903 54260439034366059016138355)
    ·
      refine ⟨81390658551549088524207533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54260439034366059016138355 81390658551549088524207533)
      ·
        refine ⟨30521496956830908196577825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81390658551549088524207533 30521496956830908196577825)
        ·
          refine ⟨22891122717623181147433369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30521496956830908196577825 22891122717623181147433369)
          ·
            refine ⟨17168342038217385860575027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22891122717623181147433369 17168342038217385860575027)
            ·
              refine ⟨25752513057326078790862541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17168342038217385860575027 25752513057326078790862541)
              ·
                refine ⟨9657192396497279546573453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25752513057326078790862541 9657192396497279546573453)
                ·
                  refine ⟨3621447148686479829965045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9657192396497279546573453 3621447148686479829965045)
                  ·
                    refine ⟨339510670189357484059223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3621447148686479829965045 339510670189357484059223)
                    ·
                      rfl

theorem cell23_1983584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 5].length) (baseStart_1983584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983584 prefixEnd_1983584 := by exact prefixLift 1983584
  have htrace : WordTrace (prefixWord ++ tailWord_1983584) baseStart_1983584 baseEnd_1983584 := by
    simpa [prefixWord, tailWord_1983584, baseEnd_1983584] using wordTrace_append hprefix tailTrace_1983584
  have hstable : (prefixWord ++ tailWord_1983584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983584).length < 2 ^ (prefixWord ++ tailWord_1983584).sum := by decide
  have hdescent : baseEnd_1983584 < baseStart_1983584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983592 : List Nat := [2, 1, 4, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1983592 : Nat := 118140960795 + 1983592 * 2 ^ 59
def prefixEnd_1983592 : Nat := 4983230072969 + 3 ^ 40 * 1983592 * 2
def baseEnd_1983592 : Nat := 339512039471102806959211

theorem tailTrace_1983592 : CollatzResearch.WordTrace tailWord_1983592 prefixEnd_1983592 339512039471102806959211 := by
  unfold tailWord_1983592
  simp only [CollatzResearch.WordTrace]
  refine ⟨36173771914896214693904515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48231695886528286258539353 36173771914896214693904515)
  ·
    refine ⟨54260657872344322040856773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36173771914896214693904515 54260657872344322040856773)
    ·
      refine ⟨10173873351064560382660645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54260657872344322040856773 10173873351064560382660645)
      ·
        refine ⟨1907601253324605071748871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10173873351064560382660645 1907601253324605071748871)
        ·
          refine ⟨2861401879986907607623307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907601253324605071748871 2861401879986907607623307)
          ·
            refine ⟨4292102819980361411434961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861401879986907607623307 4292102819980361411434961)
            ·
              refine ⟨3219077114985271058576221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4292102819980361411434961 3219077114985271058576221)
              ·
                refine ⟨1207153918119476646966083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3219077114985271058576221 1207153918119476646966083)
                ·
                  refine ⟨1810730877179214970449125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207153918119476646966083 1810730877179214970449125)
                  ·
                    refine ⟨339512039471102806959211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1810730877179214970449125 339512039471102806959211)
                    ·
                      rfl

theorem cell23_1983592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1983592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983592 prefixEnd_1983592 := by exact prefixLift 1983592
  have htrace : WordTrace (prefixWord ++ tailWord_1983592) baseStart_1983592 baseEnd_1983592 := by
    simpa [prefixWord, tailWord_1983592, baseEnd_1983592] using wordTrace_append hprefix tailTrace_1983592
  have hstable : (prefixWord ++ tailWord_1983592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983592).length < 2 ^ (prefixWord ++ tailWord_1983592).sum := by decide
  have hdescent : baseEnd_1983592 < baseStart_1983592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983605 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 6]
def baseStart_1983605 : Nat := 118140960795 + 1983605 * 2 ^ 59
def prefixEnd_1983605 : Nat := 4983230072969 + 3 ^ 40 * 1983605 * 2
def baseEnd_1983605 : Nat := 113171421517979652223897

theorem tailTrace_1983605 : CollatzResearch.WordTrace tailWord_1983605 prefixEnd_1983605 113171421517979652223897 := by
  unfold tailWord_1983605
  simp only [CollatzResearch.WordTrace]
  refine ⟨72348017978745332608032269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48232011985830221738688179 72348017978745332608032269)
  ·
    refine ⟨27130506742029499728012101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72348017978745332608032269 27130506742029499728012101)
    ·
      refine ⟨5086970014130531199002269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27130506742029499728012101 5086970014130531199002269)
      ·
        refine ⟨1907613755298949199625851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5086970014130531199002269 1907613755298949199625851)
        ·
          refine ⟨2861420632948423799438777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907613755298949199625851 2861420632948423799438777)
          ·
            refine ⟨2146065474711317849579083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2861420632948423799438777 2146065474711317849579083)
            ·
              refine ⟨3219098212066976774368625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146065474711317849579083 3219098212066976774368625)
              ·
                refine ⟨2414323659050232580776469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219098212066976774368625 2414323659050232580776469)
                ·
                  refine ⟨113171421517979652223897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2414323659050232580776469 113171421517979652223897)
                  ·
                    rfl

theorem cell23_1983605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_1983605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983605 prefixEnd_1983605 := by exact prefixLift 1983605
  have htrace : WordTrace (prefixWord ++ tailWord_1983605) baseStart_1983605 baseEnd_1983605 := by
    simpa [prefixWord, tailWord_1983605, baseEnd_1983605] using wordTrace_append hprefix tailTrace_1983605
  have hstable : (prefixWord ++ tailWord_1983605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983605).length < 2 ^ (prefixWord ++ tailWord_1983605).sum := by decide
  have hdescent : baseEnd_1983605 < baseStart_1983605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983658 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1983658 : Nat := 118140960795 + 1983658 * 2 ^ 59
def prefixEnd_1983658 : Nat := 4983230072969 + 3 ^ 40 * 1983658 * 2
def baseEnd_1983658 : Nat := 1018570008136505162652329

theorem tailTrace_1983658 : CollatzResearch.WordTrace tailWord_1983658 prefixEnd_1983658 1018570008136505162652329 := by
  unfold tailWord_1983658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18087487761888330664927907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48233300698368881773141085 18087487761888330664927907)
  ·
    refine ⟨27131231642832495997391861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18087487761888330664927907 27131231642832495997391861)
    ·
      refine ⟨2543552966515546499755487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27131231642832495997391861 2543552966515546499755487)
      ·
        refine ⟨3815329449773319749633231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543552966515546499755487 3815329449773319749633231)
        ·
          refine ⟨5722994174659979624449847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815329449773319749633231 5722994174659979624449847)
          ·
            refine ⟨8584491261989969436674771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5722994174659979624449847 8584491261989969436674771)
            ·
              refine ⟨12876736892984954155012157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8584491261989969436674771 12876736892984954155012157)
              ·
                refine ⟨4828776334869357808129559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12876736892984954155012157 4828776334869357808129559)
                ·
                  refine ⟨7243164502304036712194339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828776334869357808129559 7243164502304036712194339)
                  ·
                    refine ⟨10864746753456055068291509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7243164502304036712194339 10864746753456055068291509)
                    ·
                      refine ⟨1018570008136505162652329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10864746753456055068291509 1018570008136505162652329)
                      ·
                        rfl

theorem cell23_1983658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1983658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983658 prefixEnd_1983658 := by exact prefixLift 1983658
  have htrace : WordTrace (prefixWord ++ tailWord_1983658) baseStart_1983658 baseEnd_1983658 := by
    simpa [prefixWord, tailWord_1983658, baseEnd_1983658] using wordTrace_append hprefix tailTrace_1983658
  have hstable : (prefixWord ++ tailWord_1983658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983658).length < 2 ^ (prefixWord ++ tailWord_1983658).sum := by decide
  have hdescent : baseEnd_1983658 < baseStart_1983658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983674 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_1983674 : Nat := 118140960795 + 1983674 * 2 ^ 59
def prefixEnd_1983674 : Nat := 4983230072969 + 3 ^ 40 * 1983674 * 2
def baseEnd_1983674 : Nat := 339526074608992366684085

theorem tailTrace_1983674 : CollatzResearch.WordTrace tailWord_1983674 prefixEnd_1983674 339526074608992366684085 := by
  unfold tailWord_1983674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18087633653873839348073519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48233689743663571594862717 18087633653873839348073519)
  ·
    refine ⟨27131450480810759022110279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18087633653873839348073519 27131450480810759022110279)
    ·
      refine ⟨40697175721216138533165419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27131450480810759022110279 40697175721216138533165419)
      ·
        refine ⟨61045763581824207799748129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40697175721216138533165419 61045763581824207799748129)
        ·
          refine ⟨45784322686368155849811097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61045763581824207799748129 45784322686368155849811097)
          ·
            refine ⟨34338242014776116887358323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45784322686368155849811097 34338242014776116887358323)
            ·
              refine ⟨51507363022164175331037485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34338242014776116887358323 51507363022164175331037485)
              ·
                refine ⟨19315261133311565749139057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51507363022164175331037485 19315261133311565749139057)
                ·
                  refine ⟨14486445849983674311854293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19315261133311565749139057 14486445849983674311854293)
                  ·
                    refine ⟨339526074608992366684085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14486445849983674311854293 339526074608992366684085)
                    ·
                      rfl

theorem cell23_1983674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_1983674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983674 prefixEnd_1983674 := by exact prefixLift 1983674
  have htrace : WordTrace (prefixWord ++ tailWord_1983674) baseStart_1983674 baseEnd_1983674 := by
    simpa [prefixWord, tailWord_1983674, baseEnd_1983674] using wordTrace_append hprefix tailTrace_1983674
  have hstable : (prefixWord ++ tailWord_1983674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983674).length < 2 ^ (prefixWord ++ tailWord_1983674).sum := by decide
  have hdescent : baseEnd_1983674 < baseStart_1983674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983686 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1983686 : Nat := 118140960795 + 1983686 * 2 ^ 59
def prefixEnd_1983686 : Nat := 4983230072969 + 3 ^ 40 * 1983686 * 2
def baseEnd_1983686 : Nat := 339528128531610351034067

theorem tailTrace_1983686 : CollatzResearch.WordTrace tailWord_1983686 prefixEnd_1983686 339528128531610351034067 := by
  unfold tailWord_1983686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2260967884107871357554091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48233981527634588961153941 2260967884107871357554091)
  ·
    refine ⟨3391451826161807036331137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2260967884107871357554091 3391451826161807036331137)
    ·
      refine ⟨2543588869621355277248353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3391451826161807036331137 2543588869621355277248353)
      ·
        refine ⟨1907691652216016457936265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2543588869621355277248353 1907691652216016457936265)
        ·
          refine ⟨1430768739162012343452199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1907691652216016457936265 1430768739162012343452199)
          ·
            refine ⟨2146153108743018515178299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430768739162012343452199 2146153108743018515178299)
            ·
              refine ⟨3219229663114527772767449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146153108743018515178299 3219229663114527772767449)
              ·
                refine ⟨2414422247335895829575587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219229663114527772767449 2414422247335895829575587)
                ·
                  refine ⟨3621633371003843744363381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414422247335895829575587 3621633371003843744363381)
                  ·
                    refine ⟨339528128531610351034067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3621633371003843744363381 339528128531610351034067)
                    ·
                      rfl

theorem cell23_1983686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1983686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983686 prefixEnd_1983686 := by exact prefixLift 1983686
  have htrace : WordTrace (prefixWord ++ tailWord_1983686) baseStart_1983686 baseEnd_1983686 := by
    simpa [prefixWord, tailWord_1983686, baseEnd_1983686] using wordTrace_append hprefix tailTrace_1983686
  have hstable : (prefixWord ++ tailWord_1983686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983686).length < 2 ^ (prefixWord ++ tailWord_1983686).sum := by decide
  have hdescent : baseEnd_1983686 < baseStart_1983686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983731 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 3]
def baseStart_1983731 : Nat := 118140960795 + 1983731 * 2 ^ 59
def prefixEnd_1983731 : Nat := 4983230072969 + 3 ^ 40 * 1983731 * 2
def baseEnd_1983731 : Nat := 1018607492224283377039493

theorem tailTrace_1983731 : CollatzResearch.WordTrace tailWord_1983731 prefixEnd_1983731 1018607492224283377039493 := by
  unfold tailWord_1983731
  simp only [CollatzResearch.WordTrace]
  refine ⟨72352613576288856127119047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48235075717525904084746031 72352613576288856127119047)
  ·
    refine ⟨108528920364433284190678571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72352613576288856127119047 108528920364433284190678571)
    ·
      refine ⟨162793380546649926286017857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108528920364433284190678571 162793380546649926286017857)
      ·
        refine ⟨122095035409987444714513393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162793380546649926286017857 122095035409987444714513393)
        ·
          refine ⟨91571276557490583535885045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122095035409987444714513393 91571276557490583535885045)
          ·
            refine ⟨8584807177264742206489223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91571276557490583535885045 8584807177264742206489223)
            ·
              refine ⟨12877210765897113309733835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8584807177264742206489223 12877210765897113309733835)
              ·
                refine ⟨19315816148845669964600753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12877210765897113309733835 19315816148845669964600753)
                ·
                  refine ⟨14486862111634252473450565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19315816148845669964600753 14486862111634252473450565)
                  ·
                    refine ⟨2716286645931422338771981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14486862111634252473450565 2716286645931422338771981)
                    ·
                      refine ⟨1018607492224283377039493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2716286645931422338771981 1018607492224283377039493)
                      ·
                        rfl

theorem cell23_1983731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 3].length) (baseStart_1983731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983731 prefixEnd_1983731 := by exact prefixLift 1983731
  have htrace : WordTrace (prefixWord ++ tailWord_1983731) baseStart_1983731 baseEnd_1983731 := by
    simpa [prefixWord, tailWord_1983731, baseEnd_1983731] using wordTrace_append hprefix tailTrace_1983731
  have hstable : (prefixWord ++ tailWord_1983731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983731).length < 2 ^ (prefixWord ++ tailWord_1983731).sum := by decide
  have hdescent : baseEnd_1983731 < baseStart_1983731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983745 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_1983745 : Nat := 118140960795 + 1983745 * 2 ^ 59
def prefixEnd_1983745 : Nat := 4983230072969 + 3 ^ 40 * 1983745 * 2
def baseEnd_1983745 : Nat := 1018614680953446322264429

theorem tailTrace_1983745 : CollatzResearch.WordTrace tailWord_1983745 prefixEnd_1983745 1018614680953446322264429 := by
  unfold tailWord_1983745
  simp only [CollatzResearch.WordTrace]
  refine ⟨72353124198238136518128689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48235416132158757678752459 72353124198238136518128689)
  ·
    refine ⟨54264843148678602388596517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72353124198238136518128689 54264843148678602388596517)
    ·
      refine ⟨10174658090377237947861847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54264843148678602388596517 10174658090377237947861847)
      ·
        refine ⟨15261987135565856921792771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174658090377237947861847 15261987135565856921792771)
        ·
          refine ⟨22892980703348785382689157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15261987135565856921792771 22892980703348785382689157)
          ·
            refine ⟨4292433881877897259254217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22892980703348785382689157 4292433881877897259254217)
            ·
              refine ⟨3219325411408422944440663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4292433881877897259254217 3219325411408422944440663)
              ·
                refine ⟨4828988117112634416660995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219325411408422944440663 4828988117112634416660995)
                ·
                  refine ⟨7243482175668951624991493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4828988117112634416660995 7243482175668951624991493)
                  ·
                    refine ⟨1358152907937928429685905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7243482175668951624991493 1358152907937928429685905)
                    ·
                      refine ⟨1018614680953446322264429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1358152907937928429685905 1018614680953446322264429)
                      ·
                        rfl

theorem cell23_1983745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_1983745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983745 prefixEnd_1983745 := by exact prefixLift 1983745
  have htrace : WordTrace (prefixWord ++ tailWord_1983745) baseStart_1983745 baseEnd_1983745 := by
    simpa [prefixWord, tailWord_1983745, baseEnd_1983745] using wordTrace_append hprefix tailTrace_1983745
  have hstable : (prefixWord ++ tailWord_1983745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983745).length < 2 ^ (prefixWord ++ tailWord_1983745).sum := by decide
  have hdescent : baseEnd_1983745 < baseStart_1983745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983761 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 3]
def baseStart_1983761 : Nat := 118140960795 + 1983761 * 2 ^ 59
def prefixEnd_1983761 : Nat := 4983230072969 + 3 ^ 40 * 1983761 * 2
def baseEnd_1983761 : Nat := 1018622896643918259664355

theorem tailTrace_1983761 : CollatzResearch.WordTrace tailWord_1983761 prefixEnd_1983761 1018622896643918259664355 := by
  unfold tailWord_1983761
  simp only [CollatzResearch.WordTrace]
  refine ⟨72353707766180171250711137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48235805177453447500474091 72353707766180171250711137)
  ·
    refine ⟨54265280824635128438033353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72353707766180171250711137 54265280824635128438033353)
    ·
      refine ⟨40698960618476346328525015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54265280824635128438033353 40698960618476346328525015)
      ·
        refine ⟨61048440927714519492787523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40698960618476346328525015 61048440927714519492787523)
        ·
          refine ⟨91572661391571779239181285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61048440927714519492787523 91572661391571779239181285)
          ·
            refine ⟨17169874010919708607346491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91572661391571779239181285 17169874010919708607346491)
            ·
              refine ⟨25754811016379562911019737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17169874010919708607346491 25754811016379562911019737)
              ·
                refine ⟨19316108262284672183264803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25754811016379562911019737 19316108262284672183264803)
                ·
                  refine ⟨28974162393427008274897205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19316108262284672183264803 28974162393427008274897205)
                  ·
                    refine ⟨2716327724383782025771613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28974162393427008274897205 2716327724383782025771613)
                    ·
                      refine ⟨1018622896643918259664355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2716327724383782025771613 1018622896643918259664355)
                      ·
                        rfl

theorem cell23_1983761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_1983761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983761 prefixEnd_1983761 := by exact prefixLift 1983761
  have htrace : WordTrace (prefixWord ++ tailWord_1983761) baseStart_1983761 baseEnd_1983761 := by
    simpa [prefixWord, tailWord_1983761, baseEnd_1983761] using wordTrace_append hprefix tailTrace_1983761
  have hstable : (prefixWord ++ tailWord_1983761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983761).length < 2 ^ (prefixWord ++ tailWord_1983761).sum := by decide
  have hdescent : baseEnd_1983761 < baseStart_1983761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983768 : List Nat := [2, 1, 2, 3, 1, 3, 1, 5, 5]
def baseStart_1983768 : Nat := 118140960795 + 1983768 * 2 ^ 59
def prefixEnd_1983768 : Nat := 4983230072969 + 3 ^ 40 * 1983768 * 2
def baseEnd_1983768 : Nat := 113180721223166636919647

theorem tailTrace_1983768 : CollatzResearch.WordTrace tailWord_1983768 prefixEnd_1983768 113180721223166636919647 := by
  unfold tailWord_1983768
  simp only [CollatzResearch.WordTrace]
  refine ⟨36176981538577405723107979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48235975384769874297477305 36176981538577405723107979)
  ·
    refine ⟨54265472307866108584661969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36176981538577405723107979 54265472307866108584661969)
    ·
      refine ⟨40699104230899581438496477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54265472307866108584661969 40699104230899581438496477)
      ·
        refine ⟨15262164086587343039436179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40699104230899581438496477 15262164086587343039436179)
        ·
          refine ⟨22893246129881014559154269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15262164086587343039436179 22893246129881014559154269)
          ·
            refine ⟨8584967298705380459682851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22893246129881014559154269 8584967298705380459682851)
            ·
              refine ⟨12877450948058070689524277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8584967298705380459682851 12877450948058070689524277)
              ·
                refine ⟨1207261026380444127142901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12877450948058070689524277 1207261026380444127142901)
                ·
                  refine ⟨113180721223166636919647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1207261026380444127142901 113180721223166636919647)
                  ·
                    rfl

theorem cell23_1983768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 5, 5].length) (baseStart_1983768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983768 prefixEnd_1983768 := by exact prefixLift 1983768
  have htrace : WordTrace (prefixWord ++ tailWord_1983768) baseStart_1983768 baseEnd_1983768 := by
    simpa [prefixWord, tailWord_1983768, baseEnd_1983768] using wordTrace_append hprefix tailTrace_1983768
  have hstable : (prefixWord ++ tailWord_1983768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983768).length < 2 ^ (prefixWord ++ tailWord_1983768).sum := by decide
  have hdescent : baseEnd_1983768 < baseStart_1983768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983818 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2]
def baseStart_1983818 : Nat := 118140960795 + 1983818 * 2 ^ 59
def prefixEnd_1983818 : Nat := 4983230072969 + 3 ^ 40 * 1983818 * 2
def baseEnd_1983818 : Nat := 1018652165041224536651593

theorem tailTrace_1983818 : CollatzResearch.WordTrace tailWord_1983818 prefixEnd_1983818 1018652165041224536651593 := by
  unfold tailWord_1983818
  simp only [CollatzResearch.WordTrace]
  refine ⟨18088946681743417496384027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48237191151315779990357405 18088946681743417496384027)
  ·
    refine ⟨27133420022615126244576041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18088946681743417496384027 27133420022615126244576041)
    ·
      refine ⟨20350065016961344683432031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27133420022615126244576041 20350065016961344683432031)
      ·
        refine ⟨30525097525442017025148047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20350065016961344683432031 30525097525442017025148047)
        ·
          refine ⟨45787646288163025537722071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30525097525442017025148047 45787646288163025537722071)
          ·
            refine ⟨68681469432244538306583107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45787646288163025537722071 68681469432244538306583107)
            ·
              refine ⟨103022204148366807459874661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68681469432244538306583107 103022204148366807459874661)
              ·
                refine ⟨19316663277818776398726499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103022204148366807459874661 19316663277818776398726499)
                ·
                  refine ⟨28974994916728164598089749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19316663277818776398726499 28974994916728164598089749)
                  ·
                    refine ⟨1358202886721632715535457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28974994916728164598089749 1358202886721632715535457)
                    ·
                      refine ⟨1018652165041224536651593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1358202886721632715535457 1018652165041224536651593)
                      ·
                        rfl

theorem cell23_1983818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_1983818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983818 prefixEnd_1983818 := by exact prefixLift 1983818
  have htrace : WordTrace (prefixWord ++ tailWord_1983818) baseStart_1983818 baseEnd_1983818 := by
    simpa [prefixWord, tailWord_1983818, baseEnd_1983818] using wordTrace_append hprefix tailTrace_1983818
  have hstable : (prefixWord ++ tailWord_1983818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983818).length < 2 ^ (prefixWord ++ tailWord_1983818).sum := by decide
  have hdescent : baseEnd_1983818 < baseStart_1983818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983858 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 6]
def baseStart_1983858 : Nat := 118140960795 + 1983858 * 2 ^ 59
def prefixEnd_1983858 : Nat := 4983230072969 + 3 ^ 40 * 1983858 * 2
def baseEnd_1983858 : Nat := 113185856029711597794601

theorem tailTrace_1983858 : CollatzResearch.WordTrace tailWord_1983858 prefixEnd_1983858 113185856029711597794601 := by
  unfold tailWord_1983858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18089311411707189204248057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48238163764552504544661485 18089311411707189204248057)
  ·
    refine ⟨13566983558780391903186043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18089311411707189204248057 13566983558780391903186043)
    ·
      refine ⟨20350475338170587854779065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13566983558780391903186043 20350475338170587854779065)
      ·
        refine ⟨15262856503627940891084299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20350475338170587854779065 15262856503627940891084299)
        ·
          refine ⟨22894284755441911336626449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15262856503627940891084299 22894284755441911336626449)
          ·
            refine ⟨17170713566581433502469837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22894284755441911336626449 17170713566581433502469837)
            ·
              refine ⟨6439017587468037563426189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17170713566581433502469837 6439017587468037563426189)
              ·
                refine ⟨2414631595300514086284821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6439017587468037563426189 2414631595300514086284821)
                ·
                  refine ⟨113185856029711597794601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2414631595300514086284821 113185856029711597794601)
                  ·
                    rfl

theorem cell23_1983858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_1983858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983858 prefixEnd_1983858 := by exact prefixLift 1983858
  have htrace : WordTrace (prefixWord ++ tailWord_1983858) baseStart_1983858 baseEnd_1983858 := by
    simpa [prefixWord, tailWord_1983858, baseEnd_1983858] using wordTrace_append hprefix tailTrace_1983858
  have hstable : (prefixWord ++ tailWord_1983858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983858).length < 2 ^ (prefixWord ++ tailWord_1983858).sum := by decide
  have hdescent : baseEnd_1983858 < baseStart_1983858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983896 : List Nat := [2, 1, 2, 5, 2, 2, 2, 2, 1, 4]
def baseStart_1983896 : Nat := 118140960795 + 1983896 * 2 ^ 59
def prefixEnd_1983896 : Nat := 4983230072969 + 3 ^ 40 * 1983896 * 2
def baseEnd_1983896 : Nat := 339564072177425077158745

theorem tailTrace_1983896 : CollatzResearch.WordTrace tailWord_1983896 prefixEnd_1983896 339564072177425077158745 := by
  unfold tailWord_1983896
  simp only [CollatzResearch.WordTrace]
  refine ⟨36179315810345544653437771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48239087747127392871250361 36179315810345544653437771)
  ·
    refine ⟨54268973715518316980156657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36179315810345544653437771 54268973715518316980156657)
    ·
      refine ⟨40701730286638737735117493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54268973715518316980156657 40701730286638737735117493)
      ·
        refine ⟨3815787214372381662667265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40701730286638737735117493 3815787214372381662667265)
        ·
          refine ⟨2861840410779286247000449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3815787214372381662667265 2861840410779286247000449)
          ·
            refine ⟨2146380308084464685250337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2861840410779286247000449 2146380308084464685250337)
            ·
              refine ⟨1609785231063348513937753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2146380308084464685250337 1609785231063348513937753)
              ·
                refine ⟨1207338923297511385453315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609785231063348513937753 1207338923297511385453315)
                ·
                  refine ⟨1811008384946267078179973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207338923297511385453315 1811008384946267078179973)
                  ·
                    refine ⟨339564072177425077158745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1811008384946267078179973 339564072177425077158745)
                    ·
                      rfl

theorem cell23_1983896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_1983896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983896 prefixEnd_1983896 := by exact prefixLift 1983896
  have htrace : WordTrace (prefixWord ++ tailWord_1983896) baseStart_1983896 baseEnd_1983896 := by
    simpa [prefixWord, tailWord_1983896, baseEnd_1983896] using wordTrace_append hprefix tailTrace_1983896
  have hstable : (prefixWord ++ tailWord_1983896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983896).length < 2 ^ (prefixWord ++ tailWord_1983896).sum := by decide
  have hdescent : baseEnd_1983896 < baseStart_1983896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983925 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1983925 : Nat := 118140960795 + 1983925 * 2 ^ 59
def prefixEnd_1983925 : Nat := 4983230072969 + 3 ^ 40 * 1983925 * 2
def baseEnd_1983925 : Nat := 1018707107471255618013601

theorem tailTrace_1983925 : CollatzResearch.WordTrace tailWord_1983925 prefixEnd_1983925 1018707107471255618013601 := by
  unfold tailWord_1983925
  simp only [CollatzResearch.WordTrace]
  refine ⟨72359689337586027259681229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48239792891724018173120819 72359689337586027259681229)
  ·
    refine ⟨27134883501594760222380461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72359689337586027259681229 27134883501594760222380461)
    ·
      refine ⟨10175581313098035083392673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27134883501594760222380461 10175581313098035083392673)
      ·
        refine ⟨7631685984823526312544505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10175581313098035083392673 7631685984823526312544505)
        ·
          refine ⟨5723764488617644734408379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7631685984823526312544505 5723764488617644734408379)
          ·
            refine ⟨8585646732926467101612569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723764488617644734408379 8585646732926467101612569)
            ·
              refine ⟨6439235049694850326209427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8585646732926467101612569 6439235049694850326209427)
              ·
                refine ⟨9658852574542275489314141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6439235049694850326209427 9658852574542275489314141)
                ·
                  refine ⟨3622069715453353308492803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9658852574542275489314141 3622069715453353308492803)
                  ·
                    refine ⟨5433104573180029962739205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3622069715453353308492803 5433104573180029962739205)
                    ·
                      refine ⟨1018707107471255618013601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5433104573180029962739205 1018707107471255618013601)
                      ·
                        rfl

theorem cell23_1983925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1983925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983925 prefixEnd_1983925 := by exact prefixLift 1983925
  have htrace : WordTrace (prefixWord ++ tailWord_1983925) baseStart_1983925 baseEnd_1983925 := by
    simpa [prefixWord, tailWord_1983925, baseEnd_1983925] using wordTrace_append hprefix tailTrace_1983925
  have hstable : (prefixWord ++ tailWord_1983925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983925).length < 2 ^ (prefixWord ++ tailWord_1983925).sum := by decide
  have hdescent : baseEnd_1983925 < baseStart_1983925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983929 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 2, 3, 2]
def baseStart_1983929 : Nat := 118140960795 + 1983929 * 2 ^ 59
def prefixEnd_1983929 : Nat := 4983230072969 + 3 ^ 40 * 1983929 * 2
def baseEnd_1983929 : Nat := 1018709161393873602363583

theorem tailTrace_1983929 : CollatzResearch.WordTrace tailWord_1983929 prefixEnd_1983929 1018709161393873602363583 := by
  unfold tailWord_1983929
  simp only [CollatzResearch.WordTrace]
  refine ⟨72359835229571535942826841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48239890153047690628551227 72359835229571535942826841)
  ·
    refine ⟨54269876422178651957120131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72359835229571535942826841 54269876422178651957120131)
    ·
      refine ⟨81404814633267977935680197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54269876422178651957120131 81404814633267977935680197)
      ·
        refine ⟨15263402743737745862940037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81404814633267977935680197 15263402743737745862940037)
        ·
          refine ⟨2861888014450827349301257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15263402743737745862940037 2861888014450827349301257)
          ·
            refine ⟨2146416010838120511975943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2861888014450827349301257 2146416010838120511975943)
            ·
              refine ⟨3219624016257180767963915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146416010838120511975943 3219624016257180767963915)
              ·
                refine ⟨4829436024385771151945873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219624016257180767963915 4829436024385771151945873)
                ·
                  refine ⟨3622077018289328363959405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4829436024385771151945873 3622077018289328363959405)
                  ·
                    refine ⟨1358278881858498136484777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3622077018289328363959405 1358278881858498136484777)
                    ·
                      refine ⟨1018709161393873602363583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1358278881858498136484777 1018709161393873602363583)
                      ·
                        rfl

theorem cell23_1983929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_1983929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983929 prefixEnd_1983929 := by exact prefixLift 1983929
  have htrace : WordTrace (prefixWord ++ tailWord_1983929) baseStart_1983929 baseEnd_1983929 := by
    simpa [prefixWord, tailWord_1983929, baseEnd_1983929] using wordTrace_append hprefix tailTrace_1983929
  have hstable : (prefixWord ++ tailWord_1983929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983929).length < 2 ^ (prefixWord ++ tailWord_1983929).sum := by decide
  have hdescent : baseEnd_1983929 < baseStart_1983929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983948 : List Nat := [2, 2, 1, 4, 2, 2, 10]
def baseStart_1983948 : Nat := 118140960795 + 1983948 * 2 ^ 59
def prefixEnd_1983948 : Nat := 4983230072969 + 3 ^ 40 * 1983948 * 2
def baseEnd_1983948 : Nat := 12576776759584062074395

theorem tailTrace_1983948 : CollatzResearch.WordTrace tailWord_1983948 prefixEnd_1983948 12576776759584062074395 := by
  unfold tailWord_1983948
  simp only [CollatzResearch.WordTrace]
  refine ⟨36180264108251351093884249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48240352144335134791845665 36180264108251351093884249)
  ·
    refine ⟨27135198081188513320413187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36180264108251351093884249 27135198081188513320413187)
    ·
      refine ⟨40702797121782769980619781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27135198081188513320413187 40702797121782769980619781)
      ·
        refine ⟨7631774460334269371366209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40702797121782769980619781 7631774460334269371366209)
        ·
          refine ⟨5723830845250702028524657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7631774460334269371366209 5723830845250702028524657)
          ·
            refine ⟨4292873133938026521393493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5723830845250702028524657 4292873133938026521393493)
            ·
              refine ⟨12576776759584062074395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4292873133938026521393493 12576776759584062074395)
              ·
                rfl

theorem cell23_1983948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 10].length) (baseStart_1983948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1983948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1983948 prefixEnd_1983948 := by exact prefixLift 1983948
  have htrace : WordTrace (prefixWord ++ tailWord_1983948) baseStart_1983948 baseEnd_1983948 := by
    simpa [prefixWord, tailWord_1983948, baseEnd_1983948] using wordTrace_append hprefix tailTrace_1983948
  have hstable : (prefixWord ++ tailWord_1983948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983948).length < 2 ^ (prefixWord ++ tailWord_1983948).sum := by decide
  have hdescent : baseEnd_1983948 < baseStart_1983948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984008 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 4, 6]
def baseStart_1984008 : Nat := 118140960795 + 1984008 * 2 ^ 59
def prefixEnd_1984008 : Nat := 4983230072969 + 3 ^ 40 * 1984008 * 2
def baseEnd_1984008 : Nat := 339583242121859597758573

theorem tailTrace_1984008 : CollatzResearch.WordTrace tailWord_1984008 prefixEnd_1984008 339583242121859597758573 := by
  unfold tailWord_1984008
  simp only [CollatzResearch.WordTrace]
  refine ⟨36181358298142666217476339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48241811064190221623301785 36181358298142666217476339)
  ·
    refine ⟨54272037447213999326214509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36181358298142666217476339 54272037447213999326214509)
    ·
      refine ⟨20352014042705249747330441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54272037447213999326214509 20352014042705249747330441)
      ·
        refine ⟨15264010532028937310497831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20352014042705249747330441 15264010532028937310497831)
        ·
          refine ⟨22896015798043405965746747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15264010532028937310497831 22896015798043405965746747)
          ·
            refine ⟨34344023697065108948620121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22896015798043405965746747 34344023697065108948620121)
            ·
              refine ⟨25758017772798831711465091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34344023697065108948620121 25758017772798831711465091)
              ·
                refine ⟨38637026659198247567197637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25758017772798831711465091 38637026659198247567197637)
                ·
                  refine ⟨7244442498599671418849557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38637026659198247567197637 7244442498599671418849557)
                  ·
                    refine ⟨339583242121859597758573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7244442498599671418849557 339583242121859597758573)
                    ·
                      rfl

theorem cell23_1984008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_1984008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984008 prefixEnd_1984008 := by exact prefixLift 1984008
  have htrace : WordTrace (prefixWord ++ tailWord_1984008) baseStart_1984008 baseEnd_1984008 := by
    simpa [prefixWord, tailWord_1984008, baseEnd_1984008] using wordTrace_append hprefix tailTrace_1984008
  have hstable : (prefixWord ++ tailWord_1984008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984008).length < 2 ^ (prefixWord ++ tailWord_1984008).sum := by decide
  have hdescent : baseEnd_1984008 < baseStart_1984008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984030 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_1984030 : Nat := 118140960795 + 1984030 * 2 ^ 59
def prefixEnd_1984030 : Nat := 4983230072969 + 3 ^ 40 * 1984030 * 2
def baseEnd_1984030 : Nat := 1018761022939977707200619

theorem tailTrace_1984030 : CollatzResearch.WordTrace tailWord_1984030 prefixEnd_1984030 1018761022939977707200619 := by
  unfold tailWord_1984030
  simp only [CollatzResearch.WordTrace]
  refine ⟨9045439875275703774031693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48242346001470420128169029 9045439875275703774031693)
  ·
    refine ⟨3392039953228388915261885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9045439875275703774031693 3392039953228388915261885)
    ·
      refine ⟨1272014982460645843223207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3392039953228388915261885 1272014982460645843223207)
      ·
        refine ⟨1908022473690968764834811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272014982460645843223207 1908022473690968764834811)
        ·
          refine ⟨2862033710536453147252217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908022473690968764834811 2862033710536453147252217)
          ·
            refine ⟨2146525282902339860439163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2862033710536453147252217 2146525282902339860439163)
            ·
              refine ⟨3219787924353509790658745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146525282902339860439163 3219787924353509790658745)
              ·
                refine ⟨2414840943265132342994059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219787924353509790658745 2414840943265132342994059)
                ·
                  refine ⟨3622261414897698514491089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414840943265132342994059 3622261414897698514491089)
                  ·
                    refine ⟨2716696061173273885868317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3622261414897698514491089 2716696061173273885868317)
                    ·
                      refine ⟨1018761022939977707200619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2716696061173273885868317 1018761022939977707200619)
                      ·
                        rfl

theorem cell23_1984030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_1984030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984030 prefixEnd_1984030 := by exact prefixLift 1984030
  have htrace : WordTrace (prefixWord ++ tailWord_1984030) baseStart_1984030 baseEnd_1984030 := by
    simpa [prefixWord, tailWord_1984030, baseEnd_1984030] using wordTrace_append hprefix tailTrace_1984030
  have hstable : (prefixWord ++ tailWord_1984030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984030).length < 2 ^ (prefixWord ++ tailWord_1984030).sum := by decide
  have hdescent : baseEnd_1984030 < baseStart_1984030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984082 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_1984082 : Nat := 118140960795 + 1984082 * 2 ^ 59
def prefixEnd_1984082 : Nat := 4983230072969 + 3 ^ 40 * 1984082 * 2
def baseEnd_1984082 : Nat := 1018787723934011503750379

theorem tailTrace_1984082 : CollatzResearch.WordTrace tailWord_1984082 prefixEnd_1984082 1018787723934011503750379 := by
  unfold tailWord_1984082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18091353899504310768286625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48243610398678162048764333 18091353899504310768286625)
  ·
    refine ⟨13568515424628233076214969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18091353899504310768286625 13568515424628233076214969)
    ·
      refine ⟨10176386568471174807161227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13568515424628233076214969 10176386568471174807161227)
      ·
        refine ⟨15264579852706762210741841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10176386568471174807161227 15264579852706762210741841)
        ·
          refine ⟨11448434889530071658056381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15264579852706762210741841 11448434889530071658056381)
          ·
            refine ⟨4293163083573776871771143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11448434889530071658056381 4293163083573776871771143)
            ·
              refine ⟨6439744625360665307656715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293163083573776871771143 6439744625360665307656715)
              ·
                refine ⟨9659616938040997961485073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6439744625360665307656715 9659616938040997961485073)
                ·
                  refine ⟨7244712703530748471113805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9659616938040997961485073 7244712703530748471113805)
                  ·
                    refine ⟨2716767263824030676667677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7244712703530748471113805 2716767263824030676667677)
                    ·
                      refine ⟨1018787723934011503750379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2716767263824030676667677 1018787723934011503750379)
                      ·
                        rfl

theorem cell23_1984082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_1984082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984082 prefixEnd_1984082 := by exact prefixLift 1984082
  have htrace : WordTrace (prefixWord ++ tailWord_1984082) baseStart_1984082 baseEnd_1984082 := by
    simpa [prefixWord, tailWord_1984082, baseEnd_1984082] using wordTrace_append hprefix tailTrace_1984082
  have hstable : (prefixWord ++ tailWord_1984082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984082).length < 2 ^ (prefixWord ++ tailWord_1984082).sum := by decide
  have hdescent : baseEnd_1984082 < baseStart_1984082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984142 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1984142 : Nat := 118140960795 + 1984142 * 2 ^ 59
def prefixEnd_1984142 : Nat := 4983230072969 + 3 ^ 40 * 1984142 * 2
def baseEnd_1984142 : Nat := 1018818532773281269000103

theorem tailTrace_1984142 : CollatzResearch.WordTrace tailWord_1984142 prefixEnd_1984142 1018818532773281269000103 := by
  unfold tailWord_1984142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9045950497224984165041335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48245069318533248880220453 9045950497224984165041335)
  ·
    refine ⟨13568925745837476247562003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9045950497224984165041335 13568925745837476247562003)
    ·
      refine ⟨20353388618756214371343005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13568925745837476247562003 20353388618756214371343005)
      ·
        refine ⟨7632520732033580389253627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20353388618756214371343005 7632520732033580389253627)
        ·
          refine ⟨11448781098050370583880441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7632520732033580389253627 11448781098050370583880441)
          ·
            refine ⟨8586585823537777937910331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11448781098050370583880441 8586585823537777937910331)
            ·
              refine ⟨12879878735306666906865497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8586585823537777937910331 12879878735306666906865497)
              ·
                refine ⟨9659909051480000180149123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12879878735306666906865497 9659909051480000180149123)
                ·
                  refine ⟨14489863577220000270223685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9659909051480000180149123 14489863577220000270223685)
                  ·
                    refine ⟨2716849420728750050666941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14489863577220000270223685 2716849420728750050666941)
                    ·
                      refine ⟨1018818532773281269000103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2716849420728750050666941 1018818532773281269000103)
                      ·
                        rfl

theorem cell23_1984142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1984142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984142 prefixEnd_1984142 := by exact prefixLift 1984142
  have htrace : WordTrace (prefixWord ++ tailWord_1984142) baseStart_1984142 baseEnd_1984142 := by
    simpa [prefixWord, tailWord_1984142, baseEnd_1984142] using wordTrace_append hprefix tailTrace_1984142
  have hstable : (prefixWord ++ tailWord_1984142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984142).length < 2 ^ (prefixWord ++ tailWord_1984142).sum := by decide
  have hdescent : baseEnd_1984142 < baseStart_1984142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984209 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 1, 5]
def baseStart_1984209 : Nat := 118140960795 + 1984209 * 2 ^ 59
def prefixEnd_1984209 : Nat := 4983230072969 + 3 ^ 40 * 1984209 * 2
def baseEnd_1984209 : Nat := 339617645325710835620765

theorem tailTrace_1984209 : CollatzResearch.WordTrace tailWord_1984209 prefixEnd_1984209 339617645325710835620765 := by
  unfold tailWord_1984209
  simp only [CollatzResearch.WordTrace]
  refine ⟨72370047668557143763019681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48246698445704762508679787 72370047668557143763019681)
  ·
    refine ⟨54277535751417857822264761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72370047668557143763019681 54277535751417857822264761)
    ·
      refine ⟨40708151813563393366698571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54277535751417857822264761 40708151813563393366698571)
      ·
        refine ⟨61062227720345090050047857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40708151813563393366698571 61062227720345090050047857)
        ·
          refine ⟨45796670790258817537535893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61062227720345090050047857 45796670790258817537535893)
          ·
            refine ⟨2146718943293382072071995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45796670790258817537535893 2146718943293382072071995)
            ·
              refine ⟨3220078414940073108107993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146718943293382072071995 3220078414940073108107993)
              ·
                refine ⟨2415058811205054831080995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3220078414940073108107993 2415058811205054831080995)
                ·
                  refine ⟨3622588216807582246621493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415058811205054831080995 3622588216807582246621493)
                  ·
                    refine ⟨339617645325710835620765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3622588216807582246621493 339617645325710835620765)
                    ·
                      rfl

theorem cell23_1984209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_1984209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984209 prefixEnd_1984209 := by exact prefixLift 1984209
  have htrace : WordTrace (prefixWord ++ tailWord_1984209) baseStart_1984209 baseEnd_1984209 := by
    simpa [prefixWord, tailWord_1984209, baseEnd_1984209] using wordTrace_append hprefix tailTrace_1984209
  have hstable : (prefixWord ++ tailWord_1984209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984209).length < 2 ^ (prefixWord ++ tailWord_1984209).sum := by decide
  have hdescent : baseEnd_1984209 < baseStart_1984209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984239 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 2, 4]
def baseStart_1984239 : Nat := 118140960795 + 1984239 * 2 ^ 59
def prefixEnd_1984239 : Nat := 4983230072969 + 3 ^ 40 * 1984239 * 2
def baseEnd_1984239 : Nat := 339622780132255796495719

theorem tailTrace_1984239 : CollatzResearch.WordTrace tailWord_1984239 prefixEnd_1984239 339622780132255796495719 := by
  unfold tailWord_1984239
  simp only [CollatzResearch.WordTrace]
  refine ⟨72371141858448458886611771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48247427905632305924407847 72371141858448458886611771)
  ·
    refine ⟨108556712787672688329917657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72371141858448458886611771 108556712787672688329917657)
    ·
      refine ⟨81417534590754516247438243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108556712787672688329917657 81417534590754516247438243)
      ·
        refine ⟨122126301886131774371157365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81417534590754516247438243 122126301886131774371157365)
        ·
          refine ⟨11449340801824853847296003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122126301886131774371157365 11449340801824853847296003)
          ·
            refine ⟨17174011202737280770944005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11449340801824853847296003 17174011202737280770944005)
            ·
              refine ⟨3220127100513240144552001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17174011202737280770944005 3220127100513240144552001)
              ·
                refine ⟨2415095325384930108414001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3220127100513240144552001 2415095325384930108414001)
                ·
                  refine ⟨1811321494038697581310501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2415095325384930108414001 1811321494038697581310501)
                  ·
                    refine ⟨339622780132255796495719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1811321494038697581310501 339622780132255796495719)
                    ·
                      rfl

theorem cell23_1984239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 4].length) (baseStart_1984239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984239 prefixEnd_1984239 := by exact prefixLift 1984239
  have htrace : WordTrace (prefixWord ++ tailWord_1984239) baseStart_1984239 baseEnd_1984239 := by
    simpa [prefixWord, tailWord_1984239, baseEnd_1984239] using wordTrace_append hprefix tailTrace_1984239
  have hstable : (prefixWord ++ tailWord_1984239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984239).length < 2 ^ (prefixWord ++ tailWord_1984239).sum := by decide
  have hdescent : baseEnd_1984239 < baseStart_1984239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984242 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1984242 : Nat := 118140960795 + 1984242 * 2 ^ 59
def prefixEnd_1984242 : Nat := 4983230072969 + 3 ^ 40 * 1984242 * 2
def baseEnd_1984242 : Nat := 1018869880838730877749643

theorem tailTrace_1984242 : CollatzResearch.WordTrace tailWord_1984242 prefixEnd_1984242 1018869880838730877749643 := by
  unfold tailWord_1984242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18092812819359397599742745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48247500851625060265980653 18092812819359397599742745)
  ·
    refine ⟨13569609614519548199807059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18092812819359397599742745 13569609614519548199807059)
    ·
      refine ⟨20354414421779322299710589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13569609614519548199807059 20354414421779322299710589)
      ·
        refine ⟨7632905408167245862391471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20354414421779322299710589 7632905408167245862391471)
        ·
          refine ⟨11449358112250868793587207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7632905408167245862391471 11449358112250868793587207)
          ·
            refine ⟨17174037168376303190380811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11449358112250868793587207 17174037168376303190380811)
            ·
              refine ⟨25761055752564454785571217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17174037168376303190380811 25761055752564454785571217)
              ·
                refine ⟨19320791814423341089178413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25761055752564454785571217 19320791814423341089178413)
                ·
                  refine ⟨7245296930408752908441905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19320791814423341089178413 7245296930408752908441905)
                  ·
                    refine ⟨5433972697806564681331429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7245296930408752908441905 5433972697806564681331429)
                    ·
                      refine ⟨1018869880838730877749643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5433972697806564681331429 1018869880838730877749643)
                      ·
                        rfl

theorem cell23_1984242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1984242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984242 prefixEnd_1984242 := by exact prefixLift 1984242
  have htrace : WordTrace (prefixWord ++ tailWord_1984242) baseStart_1984242 baseEnd_1984242 := by
    simpa [prefixWord, tailWord_1984242, baseEnd_1984242] using wordTrace_append hprefix tailTrace_1984242
  have hstable : (prefixWord ++ tailWord_1984242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984242).length < 2 ^ (prefixWord ++ tailWord_1984242).sum := by decide
  have hdescent : baseEnd_1984242 < baseStart_1984242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984255 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_1984255 : Nat := 118140960795 + 1984255 * 2 ^ 59
def prefixEnd_1984255 : Nat := 4983230072969 + 3 ^ 40 * 1984255 * 2
def baseEnd_1984255 : Nat := 1018876556087239326887083

theorem tailTrace_1984255 : CollatzResearch.WordTrace tailWord_1984255 prefixEnd_1984255 1018876556087239326887083 := by
  unfold tailWord_1984255
  simp only [CollatzResearch.WordTrace]
  refine ⟨72371725426390493619194219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48247816950926995746129479 72371725426390493619194219)
  ·
    refine ⟨108557588139585740428791329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72371725426390493619194219 108557588139585740428791329)
    ·
      refine ⟨81418191104689305321593497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108557588139585740428791329 81418191104689305321593497)
      ·
        refine ⟨61063643328516978991195123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81418191104689305321593497 61063643328516978991195123)
        ·
          refine ⟨91595464992775468486792685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61063643328516978991195123 91595464992775468486792685)
          ·
            refine ⟨34348299372290800682547257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91595464992775468486792685 34348299372290800682547257)
            ·
              refine ⟨25761224529218100511910443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34348299372290800682547257 25761224529218100511910443)
              ·
                refine ⟨38641836793827150767865665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25761224529218100511910443 38641836793827150767865665)
                ·
                  refine ⟨28981377595370363075899249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38641836793827150767865665 28981377595370363075899249)
                  ·
                    refine ⟨21736033196527772306924437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28981377595370363075899249 21736033196527772306924437)
                    ·
                      refine ⟨1018876556087239326887083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21736033196527772306924437 1018876556087239326887083)
                      ·
                        rfl

theorem cell23_1984255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_1984255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984255 prefixEnd_1984255 := by exact prefixLift 1984255
  have htrace : WordTrace (prefixWord ++ tailWord_1984255) baseStart_1984255 baseEnd_1984255 := by
    simpa [prefixWord, tailWord_1984255, baseEnd_1984255] using wordTrace_append hprefix tailTrace_1984255
  have hstable : (prefixWord ++ tailWord_1984255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984255).length < 2 ^ (prefixWord ++ tailWord_1984255).sum := by decide
  have hdescent : baseEnd_1984255 < baseStart_1984255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984263 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 3, 2, 2]
def baseStart_1984263 : Nat := 118140960795 + 1984263 * 2 ^ 59
def prefixEnd_1984263 : Nat := 4983230072969 + 3 ^ 40 * 1984263 * 2
def baseEnd_1984263 : Nat := 1018880663932475295587047

theorem tailTrace_1984263 : CollatzResearch.WordTrace tailWord_1984263 prefixEnd_1984263 1018880663932475295587047 := by
  unfold tailWord_1984263
  simp only [CollatzResearch.WordTrace]
  refine ⟨72372017210361510985485443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48248011473574340656990295 72372017210361510985485443)
  ·
    refine ⟨108558025815542266478228165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72372017210361510985485443 108558025815542266478228165)
    ·
      refine ⟨20354629840414174964667781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108558025815542266478228165 20354629840414174964667781)
      ·
        refine ⟨3816493095077657805875209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20354629840414174964667781 3816493095077657805875209)
        ·
          refine ⟨2862369821308243354406407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3816493095077657805875209 2862369821308243354406407)
          ·
            refine ⟨4293554731962365031609611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862369821308243354406407 4293554731962365031609611)
            ·
              refine ⟨6440332097943547547414417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293554731962365031609611 6440332097943547547414417)
              ·
                refine ⟨4830249073457660660560813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6440332097943547547414417 4830249073457660660560813)
                ·
                  refine ⟨1811343402546622747710305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4830249073457660660560813 1811343402546622747710305)
                  ·
                    refine ⟨1358507551909967060782729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1811343402546622747710305 1358507551909967060782729)
                    ·
                      refine ⟨1018880663932475295587047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1358507551909967060782729 1018880663932475295587047)
                      ·
                        rfl

theorem cell23_1984263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_1984263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984263 prefixEnd_1984263 := by exact prefixLift 1984263
  have htrace : WordTrace (prefixWord ++ tailWord_1984263) baseStart_1984263 baseEnd_1984263 := by
    simpa [prefixWord, tailWord_1984263, baseEnd_1984263] using wordTrace_append hprefix tailTrace_1984263
  have hstable : (prefixWord ++ tailWord_1984263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984263).length < 2 ^ (prefixWord ++ tailWord_1984263).sum := by decide
  have hdescent : baseEnd_1984263 < baseStart_1984263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984265 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 4, 7]
def baseStart_1984265 : Nat := 118140960795 + 1984265 * 2 ^ 59
def prefixEnd_1984265 : Nat := 4983230072969 + 3 ^ 40 * 1984265 * 2
def baseEnd_1984265 : Nat := 339627230297928095920679

theorem tailTrace_1984265 : CollatzResearch.WordTrace tailWord_1984265 prefixEnd_1984265 339627230297928095920679 := by
  unfold tailWord_1984265
  simp only [CollatzResearch.WordTrace]
  refine ⟨72372090156354265327058249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48248060104236176884705499 72372090156354265327058249)
  ·
    refine ⟨54279067617265698995293687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72372090156354265327058249 54279067617265698995293687)
    ·
      refine ⟨81418601425898548492940531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54279067617265698995293687 81418601425898548492940531)
      ·
        refine ⟨122127902138847822739410797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81418601425898548492940531 122127902138847822739410797)
        ·
          refine ⟨45797963302067933527279049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122127902138847822739410797 45797963302067933527279049)
          ·
            refine ⟨34348472476550950145459287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45797963302067933527279049 34348472476550950145459287)
            ·
              refine ⟨51522708714826425218188931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34348472476550950145459287 51522708714826425218188931)
              ·
                refine ⟨77284063072239637827283397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51522708714826425218188931 77284063072239637827283397)
                ·
                  refine ⟨14490761826044932092615637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77284063072239637827283397 14490761826044932092615637)
                  ·
                    refine ⟨339627230297928095920679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14490761826044932092615637 339627230297928095920679)
                    ·
                      rfl

theorem cell23_1984265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_1984265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984265 prefixEnd_1984265 := by exact prefixLift 1984265
  have htrace : WordTrace (prefixWord ++ tailWord_1984265) baseStart_1984265 baseEnd_1984265 := by
    simpa [prefixWord, tailWord_1984265, baseEnd_1984265] using wordTrace_append hprefix tailTrace_1984265
  have hstable : (prefixWord ++ tailWord_1984265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984265).length < 2 ^ (prefixWord ++ tailWord_1984265).sum := by decide
  have hdescent : baseEnd_1984265 < baseStart_1984265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984279 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1984279 : Nat := 118140960795 + 1984279 * 2 ^ 59
def prefixEnd_1984279 : Nat := 4983230072969 + 3 ^ 40 * 1984279 * 2
def baseEnd_1984279 : Nat := 1018888879622947232986973

theorem tailTrace_1984279 : CollatzResearch.WordTrace tailWord_1984279 prefixEnd_1984279 1018888879622947232986973 := by
  unfold tailWord_1984279
  simp only [CollatzResearch.WordTrace]
  refine ⟨72372600778303545718067891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48248400518869030478711927 72372600778303545718067891)
  ·
    refine ⟨108558901167455318577101837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72372600778303545718067891 108558901167455318577101837)
    ·
      refine ⟨40709587937795744466413189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108558901167455318577101837 40709587937795744466413189)
      ·
        refine ⟨7633047738336702087452473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40709587937795744466413189 7633047738336702087452473)
        ·
          refine ⟨5724785803752526565589355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7633047738336702087452473 5724785803752526565589355)
          ·
            refine ⟨8587178705628789848384033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5724785803752526565589355 8587178705628789848384033)
            ·
              refine ⟨6440384029221592386288025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8587178705628789848384033 6440384029221592386288025)
              ·
                refine ⟨4830288021916194289716019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6440384029221592386288025 4830288021916194289716019)
                ·
                  refine ⟨7245432032874291434574029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830288021916194289716019 7245432032874291434574029)
                  ·
                    refine ⟨2717037012327859287965261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7245432032874291434574029 2717037012327859287965261)
                    ·
                      refine ⟨1018888879622947232986973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2717037012327859287965261 1018888879622947232986973)
                      ·
                        rfl

theorem cell23_1984279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1984279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984279 prefixEnd_1984279 := by exact prefixLift 1984279
  have htrace : WordTrace (prefixWord ++ tailWord_1984279) baseStart_1984279 baseEnd_1984279 := by
    simpa [prefixWord, tailWord_1984279, baseEnd_1984279] using wordTrace_append hprefix tailTrace_1984279
  have hstable : (prefixWord ++ tailWord_1984279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984279).length < 2 ^ (prefixWord ++ tailWord_1984279).sum := by decide
  have hdescent : baseEnd_1984279 < baseStart_1984279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984286 : List Nat := [4, 3, 2, 2, 1, 1, 10]
def baseStart_1984286 : Nat := 118140960795 + 1984286 * 2 ^ 59
def prefixEnd_1984286 : Nat := 4983230072969 + 3 ^ 40 * 1984286 * 2
def baseEnd_1984286 : Nat := 12578919431944798834561

theorem tailTrace_1984286 : CollatzResearch.WordTrace tailWord_1984286 prefixEnd_1984286 12578919431944798834561 := by
  unfold tailWord_1984286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9046607011159773239196589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48248570726185457275715141 9046607011159773239196589)
  ·
    refine ⟨3392477629184914964698721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9046607011159773239196589 3392477629184914964698721)
    ·
      refine ⟨2544358221888686223524041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3392477629184914964698721 2544358221888686223524041)
      ·
        refine ⟨1908268666416514667643031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2544358221888686223524041 1908268666416514667643031)
        ·
          refine ⟨2862402999624772001464547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908268666416514667643031 2862402999624772001464547)
          ·
            refine ⟨4293604499437158002196821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862402999624772001464547 4293604499437158002196821)
            ·
              refine ⟨12578919431944798834561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4293604499437158002196821 12578919431944798834561)
              ·
                rfl

theorem cell23_1984286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 10].length) (baseStart_1984286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984286 prefixEnd_1984286 := by exact prefixLift 1984286
  have htrace : WordTrace (prefixWord ++ tailWord_1984286) baseStart_1984286 baseEnd_1984286 := by
    simpa [prefixWord, tailWord_1984286, baseEnd_1984286] using wordTrace_append hprefix tailTrace_1984286
  have hstable : (prefixWord ++ tailWord_1984286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984286).length < 2 ^ (prefixWord ++ tailWord_1984286).sum := by decide
  have hdescent : baseEnd_1984286 < baseStart_1984286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984296 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_1984296 : Nat := 118140960795 + 1984296 * 2 ^ 59
def prefixEnd_1984296 : Nat := 4983230072969 + 3 ^ 40 * 1984296 * 2
def baseEnd_1984296 : Nat := 1018897608794073666474395

theorem tailTrace_1984296 : CollatzResearch.WordTrace tailWord_1984296 prefixEnd_1984296 1018897608794073666474395 := by
  unfold tailWord_1984296
  simp only [CollatzResearch.WordTrace]
  refine ⟨36186610409620978810718371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48248813879494638414291161 36186610409620978810718371)
  ·
    refine ⟨54279915614431468216077557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36186610409620978810718371 54279915614431468216077557)
    ·
      refine ⟨5088742088852950145257271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54279915614431468216077557 5088742088852950145257271)
      ·
        refine ⟨7633113133279425217885907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088742088852950145257271 7633113133279425217885907)
        ·
          refine ⟨11449669699919137826828861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7633113133279425217885907 11449669699919137826828861)
          ·
            refine ⟨4293626137469676685060823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11449669699919137826828861 4293626137469676685060823)
            ·
              refine ⟨6440439206204515027591235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293626137469676685060823 6440439206204515027591235)
              ·
                refine ⟨9660658809306772541386853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440439206204515027591235 9660658809306772541386853)
                ·
                  refine ⟨1811373526745019851510035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9660658809306772541386853 1811373526745019851510035)
                  ·
                    refine ⟨2717060290117529777265053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1811373526745019851510035 2717060290117529777265053)
                    ·
                      refine ⟨1018897608794073666474395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2717060290117529777265053 1018897608794073666474395)
                      ·
                        rfl

theorem cell23_1984296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_1984296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984296 prefixEnd_1984296 := by exact prefixLift 1984296
  have htrace : WordTrace (prefixWord ++ tailWord_1984296) baseStart_1984296 baseEnd_1984296 := by
    simpa [prefixWord, tailWord_1984296, baseEnd_1984296] using wordTrace_append hprefix tailTrace_1984296
  have hstable : (prefixWord ++ tailWord_1984296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984296).length < 2 ^ (prefixWord ++ tailWord_1984296).sum := by decide
  have hdescent : baseEnd_1984296 < baseStart_1984296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984312 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 2, 6]
def baseStart_1984312 : Nat := 118140960795 + 1984312 * 2 ^ 59
def prefixEnd_1984312 : Nat := 4983230072969 + 3 ^ 40 * 1984312 * 2
def baseEnd_1984312 : Nat := 339635274828181867958107

theorem tailTrace_1984312 : CollatzResearch.WordTrace tailWord_1984312 prefixEnd_1984312 339635274828181867958107 := by
  unfold tailWord_1984312
  simp only [CollatzResearch.WordTrace]
  refine ⟨36186902193591996177009595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48249202924789328236012793 36186902193591996177009595)
  ·
    refine ⟨54280353290387994265514393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36186902193591996177009595 54280353290387994265514393)
    ·
      refine ⟨40710264967790995699135795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54280353290387994265514393 40710264967790995699135795)
      ·
        refine ⟨61065397451686493548703693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40710264967790995699135795 61065397451686493548703693)
        ·
          refine ⟨22899524044382435080763885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61065397451686493548703693 22899524044382435080763885)
          ·
            refine ⟨8587321516643413155286457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22899524044382435080763885 8587321516643413155286457)
            ·
              refine ⟨6440491137482559866464843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8587321516643413155286457 6440491137482559866464843)
              ·
                refine ⟨9660736706223839799697265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440491137482559866464843 9660736706223839799697265)
                ·
                  refine ⟨7245552529667879849772949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9660736706223839799697265 7245552529667879849772949)
                  ·
                    refine ⟨339635274828181867958107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7245552529667879849772949 339635274828181867958107)
                    ·
                      rfl

theorem cell23_1984312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_1984312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984312 prefixEnd_1984312 := by exact prefixLift 1984312
  have htrace : WordTrace (prefixWord ++ tailWord_1984312) baseStart_1984312 baseEnd_1984312 := by
    simpa [prefixWord, tailWord_1984312, baseEnd_1984312] using wordTrace_append hprefix tailTrace_1984312
  have hstable : (prefixWord ++ tailWord_1984312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984312).length < 2 ^ (prefixWord ++ tailWord_1984312).sum := by decide
  have hdescent : baseEnd_1984312 < baseStart_1984312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984313 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1984313 : Nat := 118140960795 + 1984313 * 2 ^ 59
def prefixEnd_1984313 : Nat := 4983230072969 + 3 ^ 40 * 1984313 * 2
def baseEnd_1984313 : Nat := 1018906337965200099961817

theorem tailTrace_1984313 : CollatzResearch.WordTrace tailWord_1984313 prefixEnd_1984313 1018906337965200099961817 := by
  unfold tailWord_1984313
  simp only [CollatzResearch.WordTrace]
  refine ⟨72373840860180369524805593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48249227240120246349870395 72373840860180369524805593)
  ·
    refine ⟨54280380645135277143604195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72373840860180369524805593 54280380645135277143604195)
    ·
      refine ⟨81420570967702915715406293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54280380645135277143604195 81420570967702915715406293)
      ·
        refine ⟨1908294632055537087079835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 81420570967702915715406293 1908294632055537087079835)
        ·
          refine ⟨2862441948083305630619753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908294632055537087079835 2862441948083305630619753)
          ·
            refine ⟨2146831461062479222964815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2862441948083305630619753 2146831461062479222964815)
            ·
              refine ⟨3220247191593718834447223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146831461062479222964815 3220247191593718834447223)
              ·
                refine ⟨4830370787390578251670835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220247191593718834447223 4830370787390578251670835)
                ·
                  refine ⟨7245556181085867377506253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830370787390578251670835 7245556181085867377506253)
                  ·
                    refine ⟨2717083567907200266564845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7245556181085867377506253 2717083567907200266564845)
                    ·
                      refine ⟨1018906337965200099961817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2717083567907200266564845 1018906337965200099961817)
                      ·
                        rfl

theorem cell23_1984313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1984313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984313 prefixEnd_1984313 := by exact prefixLift 1984313
  have htrace : WordTrace (prefixWord ++ tailWord_1984313) baseStart_1984313 baseEnd_1984313 := by
    simpa [prefixWord, tailWord_1984313, baseEnd_1984313] using wordTrace_append hprefix tailTrace_1984313
  have hstable : (prefixWord ++ tailWord_1984313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984313).length < 2 ^ (prefixWord ++ tailWord_1984313).sum := by decide
  have hdescent : baseEnd_1984313 < baseStart_1984313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984315 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 12]
def baseStart_1984315 : Nat := 118140960795 + 1984315 * 2 ^ 59
def prefixEnd_1984315 : Nat := 4983230072969 + 3 ^ 40 * 1984315 * 2
def baseEnd_1984315 : Nat := 1018907364926509092136807

theorem tailTrace_1984315 : CollatzResearch.WordTrace tailWord_1984315 prefixEnd_1984315 1018907364926509092136807 := by
  unfold tailWord_1984315
  simp only [CollatzResearch.WordTrace]
  refine ⟨72373913806173123866378399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48249275870782082577585599 72373913806173123866378399)
  ·
    refine ⟨108560870709259685799567599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72373913806173123866378399 108560870709259685799567599)
    ·
      refine ⟨162841306063889528699351399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108560870709259685799567599 162841306063889528699351399)
      ·
        refine ⟨244261959095834293049027099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162841306063889528699351399 244261959095834293049027099)
        ·
          refine ⟨366392938643751439573540649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244261959095834293049027099 366392938643751439573540649)
          ·
            refine ⟨274794703982813579680155487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366392938643751439573540649 274794703982813579680155487)
            ·
              refine ⟨412192055974220369520233231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274794703982813579680155487 412192055974220369520233231)
              ·
                refine ⟨618288083961330554280349847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412192055974220369520233231 618288083961330554280349847)
                ·
                  refine ⟨927432125941995831420524771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618288083961330554280349847 927432125941995831420524771)
                  ·
                    refine ⟨1391148188912993747130787157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 927432125941995831420524771 1391148188912993747130787157)
                    ·
                      refine ⟨1018907364926509092136807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 12 1391148188912993747130787157 1018907364926509092136807)
                      ·
                        rfl

theorem cell23_1984315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_1984315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984315 prefixEnd_1984315 := by exact prefixLift 1984315
  have htrace : WordTrace (prefixWord ++ tailWord_1984315) baseStart_1984315 baseEnd_1984315 := by
    simpa [prefixWord, tailWord_1984315, baseEnd_1984315] using wordTrace_append hprefix tailTrace_1984315
  have hstable : (prefixWord ++ tailWord_1984315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984315).length < 2 ^ (prefixWord ++ tailWord_1984315).sum := by decide
  have hdescent : baseEnd_1984315 < baseStart_1984315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984326 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1984326 : Nat := 118140960795 + 1984326 * 2 ^ 59
def prefixEnd_1984326 : Nat := 4983230072969 + 3 ^ 40 * 1984326 * 2
def baseEnd_1984326 : Nat := 1018913013213708549099257

theorem tailTrace_1984326 : CollatzResearch.WordTrace tailWord_1984326 prefixEnd_1984326 1018913013213708549099257 := by
  unfold tailWord_1984326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261697344035414773282151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48249543339422181830019221 2261697344035414773282151)
  ·
    refine ⟨3392546016053122159923227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2261697344035414773282151 3392546016053122159923227)
    ·
      refine ⟨5088819024079683239884841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392546016053122159923227 5088819024079683239884841)
      ·
        refine ⟨3816614268059762429913631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5088819024079683239884841 3816614268059762429913631)
        ·
          refine ⟨5724921402089643644870447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3816614268059762429913631 5724921402089643644870447)
          ·
            refine ⟨8587382103134465467305671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5724921402089643644870447 8587382103134465467305671)
            ·
              refine ⟨12881073154701698200958507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8587382103134465467305671 12881073154701698200958507)
              ·
                refine ⟨19321609732052547301437761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12881073154701698200958507 19321609732052547301437761)
                ·
                  refine ⟨14491207299039410476078321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19321609732052547301437761 14491207299039410476078321)
                  ·
                    refine ⟨10868405474279557857058741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14491207299039410476078321 10868405474279557857058741)
                    ·
                      refine ⟨1018913013213708549099257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10868405474279557857058741 1018913013213708549099257)
                      ·
                        rfl

theorem cell23_1984326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1984326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984326 prefixEnd_1984326 := by exact prefixLift 1984326
  have htrace : WordTrace (prefixWord ++ tailWord_1984326) baseStart_1984326 baseEnd_1984326 := by
    simpa [prefixWord, tailWord_1984326, baseEnd_1984326] using wordTrace_append hprefix tailTrace_1984326
  have hstable : (prefixWord ++ tailWord_1984326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984326).length < 2 ^ (prefixWord ++ tailWord_1984326).sum := by decide
  have hdescent : baseEnd_1984326 < baseStart_1984326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984389 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 2, 5]
def baseStart_1984389 : Nat := 118140960795 + 1984389 * 2 ^ 59
def prefixEnd_1984389 : Nat := 4983230072969 + 3 ^ 40 * 1984389 * 2
def baseEnd_1984389 : Nat := 339648454164980600870489

theorem tailTrace_1984389 : CollatzResearch.WordTrace tailWord_1984389 prefixEnd_1984389 339648454164980600870489 := by
  unfold tailWord_1984389
  simp only [CollatzResearch.WordTrace]
  refine ⟨72376612807905034504572221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48251075205270023003048147 72376612807905034504572221)
  ·
    refine ⟨27141229802964387939214583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72376612807905034504572221 27141229802964387939214583)
    ·
      refine ⟨40711844704446581908821875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27141229802964387939214583 40711844704446581908821875)
      ·
        refine ⟨61067767056669872863232813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40711844704446581908821875 61067767056669872863232813)
        ·
          refine ⟨22900412646251202323712305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61067767056669872863232813 22900412646251202323712305)
          ·
            refine ⟨17175309484688401742784229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22900412646251202323712305 17175309484688401742784229)
            ·
              refine ⟨3220370528379075326772043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17175309484688401742784229 3220370528379075326772043)
              ·
                refine ⟨4830555792568612990158065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220370528379075326772043 4830555792568612990158065)
                ·
                  refine ⟨3622916844426459742618549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4830555792568612990158065 3622916844426459742618549)
                  ·
                    refine ⟨339648454164980600870489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3622916844426459742618549 339648454164980600870489)
                    ·
                      rfl

theorem cell23_1984389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_1984389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984389 prefixEnd_1984389 := by exact prefixLift 1984389
  have htrace : WordTrace (prefixWord ++ tailWord_1984389) baseStart_1984389 baseEnd_1984389 := by
    simpa [prefixWord, tailWord_1984389, baseEnd_1984389] using wordTrace_append hprefix tailTrace_1984389
  have hstable : (prefixWord ++ tailWord_1984389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984389).length < 2 ^ (prefixWord ++ tailWord_1984389).sum := by decide
  have hdescent : baseEnd_1984389 < baseStart_1984389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984409 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 4]
def baseStart_1984409 : Nat := 118140960795 + 1984409 * 2 ^ 59
def prefixEnd_1984409 : Nat := 4983230072969 + 3 ^ 40 * 1984409 * 2
def baseEnd_1984409 : Nat := 1018955632108031724361375

theorem tailTrace_1984409 : CollatzResearch.WordTrace tailWord_1984409 prefixEnd_1984409 1018955632108031724361375 := by
  unfold tailWord_1984409
  simp only [CollatzResearch.WordTrace]
  refine ⟨72377342267832577920300281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48251561511888385280200187 72377342267832577920300281)
  ·
    refine ⟨54283006700874433440225211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72377342267832577920300281 54283006700874433440225211)
    ·
      refine ⟨81424510051311650160337817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54283006700874433440225211 81424510051311650160337817)
      ·
        refine ⟨61068382538483737620253363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81424510051311650160337817 61068382538483737620253363)
        ·
          refine ⟨91602573807725606430380045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61068382538483737620253363 91602573807725606430380045)
          ·
            refine ⟨34350965177897102411392517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91602573807725606430380045 34350965177897102411392517)
            ·
              refine ⟨6440805970855706702136097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34350965177897102411392517 6440805970855706702136097)
              ·
                refine ⟨4830604478141780026602073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6440805970855706702136097 4830604478141780026602073)
                ·
                  refine ⟨3622953358606335019951555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4830604478141780026602073 3622953358606335019951555)
                  ·
                    refine ⟨5434430037909502529927333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3622953358606335019951555 5434430037909502529927333)
                    ·
                      refine ⟨1018955632108031724361375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5434430037909502529927333 1018955632108031724361375)
                      ·
                        rfl

theorem cell23_1984409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_1984409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984409 prefixEnd_1984409 := by exact prefixLift 1984409
  have htrace : WordTrace (prefixWord ++ tailWord_1984409) baseStart_1984409 baseEnd_1984409 := by
    simpa [prefixWord, tailWord_1984409, baseEnd_1984409] using wordTrace_append hprefix tailTrace_1984409
  have hstable : (prefixWord ++ tailWord_1984409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984409).length < 2 ^ (prefixWord ++ tailWord_1984409).sum := by decide
  have hdescent : baseEnd_1984409 < baseStart_1984409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984419 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 3, 4]
def baseStart_1984419 : Nat := 118140960795 + 1984419 * 2 ^ 59
def prefixEnd_1984419 : Nat := 4983230072969 + 3 ^ 40 * 1984419 * 2
def baseEnd_1984419 : Nat := 339653588971525561745443

theorem tailTrace_1984419 : CollatzResearch.WordTrace tailWord_1984419 prefixEnd_1984419 339653588971525561745443 := by
  unfold tailWord_1984419
  simp only [CollatzResearch.WordTrace]
  refine ⟨72377706997796349628164311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48251804665197566418776207 72377706997796349628164311)
  ·
    refine ⟨108566560496694524442246467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72377706997796349628164311 108566560496694524442246467)
    ·
      refine ⟨162849840745041786663369701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108566560496694524442246467 162849840745041786663369701)
      ·
        refine ⟨30534345139695334999381819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162849840745041786663369701 30534345139695334999381819)
        ·
          refine ⟨45801517709543002499072729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30534345139695334999381819 45801517709543002499072729)
          ·
            refine ⟨34351138282157251874304547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45801517709543002499072729 34351138282157251874304547)
            ·
              refine ⟨51526707423235877811456821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34351138282157251874304547 51526707423235877811456821)
              ·
                refine ⟨4830628820928363544824077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51526707423235877811456821 4830628820928363544824077)
                ·
                  refine ⟨1811485807848136329309029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4830628820928363544824077 1811485807848136329309029)
                  ·
                    refine ⟨339653588971525561745443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1811485807848136329309029 339653588971525561745443)
                    ·
                      rfl

theorem cell23_1984419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 4].length) (baseStart_1984419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984419 prefixEnd_1984419 := by exact prefixLift 1984419
  have htrace : WordTrace (prefixWord ++ tailWord_1984419) baseStart_1984419 baseEnd_1984419 := by
    simpa [prefixWord, tailWord_1984419, baseEnd_1984419] using wordTrace_append hprefix tailTrace_1984419
  have hstable : (prefixWord ++ tailWord_1984419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984419).length < 2 ^ (prefixWord ++ tailWord_1984419).sum := by decide
  have hdescent : baseEnd_1984419 < baseStart_1984419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984446 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_1984446 : Nat := 118140960795 + 1984446 * 2 ^ 59
def prefixEnd_1984446 : Nat := 4983230072969 + 3 ^ 40 * 1984446 * 2
def baseEnd_1984446 : Nat := 1018974630892248079598705

theorem tailTrace_1984446 : CollatzResearch.WordTrace tailWord_1984446 prefixEnd_1984446 1018974630892248079598705 := by
  unfold tailWord_1984446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9047336471087316654924649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48252461179132355492931461 9047336471087316654924649)
  ·
    refine ⟨6785502353315487491193487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9047336471087316654924649 6785502353315487491193487)
    ·
      refine ⟨10178253529973231236790231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6785502353315487491193487 10178253529973231236790231)
      ·
        refine ⟨15267380294959846855185347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10178253529973231236790231 15267380294959846855185347)
        ·
          refine ⟨22901070442439770282778021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15267380294959846855185347 22901070442439770282778021)
          ·
            refine ⟨4293950707957456928020879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22901070442439770282778021 4293950707957456928020879)
            ·
              refine ⟨6440926061936185392031319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293950707957456928020879 6440926061936185392031319)
              ·
                refine ⟨9661389092904278088046979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440926061936185392031319 9661389092904278088046979)
                ·
                  refine ⟨14492083639356417132070469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9661389092904278088046979 14492083639356417132070469)
                  ·
                    refine ⟨2717265682379328212263213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14492083639356417132070469 2717265682379328212263213)
                    ·
                      refine ⟨1018974630892248079598705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2717265682379328212263213 1018974630892248079598705)
                      ·
                        rfl

theorem cell23_1984446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_1984446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984446 prefixEnd_1984446 := by exact prefixLift 1984446
  have htrace : WordTrace (prefixWord ++ tailWord_1984446) baseStart_1984446 baseEnd_1984446 := by
    simpa [prefixWord, tailWord_1984446, baseEnd_1984446] using wordTrace_append hprefix tailTrace_1984446
  have hstable : (prefixWord ++ tailWord_1984446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984446).length < 2 ^ (prefixWord ++ tailWord_1984446).sum := by decide
  have hdescent : baseEnd_1984446 < baseStart_1984446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984466 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 8]
def baseStart_1984466 : Nat := 118140960795 + 1984466 * 2 ^ 59
def prefixEnd_1984466 : Nat := 4983230072969 + 3 ^ 40 * 1984466 * 2
def baseEnd_1984466 : Nat := 113220544500593111260957

theorem tailTrace_1984466 : CollatzResearch.WordTrace tailWord_1984466 prefixEnd_1984466 113220544500593111260957 := by
  unfold tailWord_1984466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18094855307156519163781313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48252947485750717770083501 18094855307156519163781313)
  ·
    refine ⟨13571141480367389372835985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18094855307156519163781313 13571141480367389372835985)
    ·
      refine ⟨10178356110275542029626989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13571141480367389372835985 10178356110275542029626989)
      ·
        refine ⟨3816883541353328261110121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10178356110275542029626989 3816883541353328261110121)
        ·
          refine ⟨2862662656014996195832591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3816883541353328261110121 2862662656014996195832591)
          ·
            refine ⟨4293993984022494293748887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862662656014996195832591 4293993984022494293748887)
            ·
              refine ⟨6440990976033741440623331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293993984022494293748887 6440990976033741440623331)
              ·
                refine ⟨9661486464050612160934997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440990976033741440623331 9661486464050612160934997)
                ·
                  refine ⟨113220544500593111260957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9661486464050612160934997 113220544500593111260957)
                  ·
                    rfl

theorem cell23_1984466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_1984466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984466 prefixEnd_1984466 := by exact prefixLift 1984466
  have htrace : WordTrace (prefixWord ++ tailWord_1984466) baseStart_1984466 baseEnd_1984466 := by
    simpa [prefixWord, tailWord_1984466, baseEnd_1984466] using wordTrace_append hprefix tailTrace_1984466
  have hstable : (prefixWord ++ tailWord_1984466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984466).length < 2 ^ (prefixWord ++ tailWord_1984466).sum := by decide
  have hdescent : baseEnd_1984466 < baseStart_1984466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984469 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1984469 : Nat := 118140960795 + 1984469 * 2 ^ 59
def prefixEnd_1984469 : Nat := 4983230072969 + 3 ^ 40 * 1984469 * 2
def baseEnd_1984469 : Nat := 1018986440947301489611099

theorem tailTrace_1984469 : CollatzResearch.WordTrace tailWord_1984469 prefixEnd_1984469 1018986440947301489611099 := by
  unfold tailWord_1984469
  simp only [CollatzResearch.WordTrace]
  refine ⟨72379530647615208167484461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48253020431743472111656307 72379530647615208167484461)
  ·
    refine ⟨27142323992855703062806673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72379530647615208167484461 27142323992855703062806673)
    ·
      refine ⟨20356742994641777297105005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27142323992855703062806673 20356742994641777297105005)
      ·
        refine ⟨7633778622990666486414377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20356742994641777297105005 7633778622990666486414377)
        ·
          refine ⟨5725333967242999864810783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7633778622990666486414377 5725333967242999864810783)
          ·
            refine ⟨8588000950864499797216175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5725333967242999864810783 8588000950864499797216175)
            ·
              refine ⟨12882001426296749695824263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8588000950864499797216175 12882001426296749695824263)
              ·
                refine ⟨19323002139445124543736395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12882001426296749695824263 19323002139445124543736395)
                ·
                  refine ⟨28984503209167686815604593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19323002139445124543736395 28984503209167686815604593)
                  ·
                    refine ⟨21738377406875765111703445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28984503209167686815604593 21738377406875765111703445)
                    ·
                      refine ⟨1018986440947301489611099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21738377406875765111703445 1018986440947301489611099)
                      ·
                        rfl

theorem cell23_1984469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1984469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984469 prefixEnd_1984469 := by exact prefixLift 1984469
  have htrace : WordTrace (prefixWord ++ tailWord_1984469) baseStart_1984469 baseEnd_1984469 := by
    simpa [prefixWord, tailWord_1984469, baseEnd_1984469] using wordTrace_append hprefix tailTrace_1984469
  have hstable : (prefixWord ++ tailWord_1984469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984469).length < 2 ^ (prefixWord ++ tailWord_1984469).sum := by decide
  have hdescent : baseEnd_1984469 < baseStart_1984469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984470 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1984470 : Nat := 118140960795 + 1984470 * 2 ^ 59
def prefixEnd_1984470 : Nat := 4983230072969 + 3 ^ 40 * 1984470 * 2
def baseEnd_1984470 : Nat := 339662318142651995232865

theorem tailTrace_1984470 : CollatzResearch.WordTrace tailWord_1984470 prefixEnd_1984470 339662318142651995232865 := by
  unfold tailWord_1984470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523722945038224083641929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48253044747074390225513909 4523722945038224083641929)
  ·
    refine ⟨3392792208778668062731447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4523722945038224083641929 3392792208778668062731447)
    ·
      refine ⟨5089188313168002094097171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392792208778668062731447 5089188313168002094097171)
      ·
        refine ⟨7633782469752003141145757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5089188313168002094097171 7633782469752003141145757)
        ·
          refine ⟨2862668426157001177929659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7633782469752003141145757 2862668426157001177929659)
          ·
            refine ⟨4294002639235501766894489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862668426157001177929659 4294002639235501766894489)
            ·
              refine ⟨3220501979426626325170867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4294002639235501766894489 3220501979426626325170867)
              ·
                refine ⟨4830752969139939487756301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220501979426626325170867 4830752969139939487756301)
                ·
                  refine ⟨1811532363427477307908613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4830752969139939487756301 1811532363427477307908613)
                  ·
                    refine ⟨339662318142651995232865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1811532363427477307908613 339662318142651995232865)
                    ·
                      rfl

theorem cell23_1984470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1984470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984470 prefixEnd_1984470 := by exact prefixLift 1984470
  have htrace : WordTrace (prefixWord ++ tailWord_1984470) baseStart_1984470 baseEnd_1984470 := by
    simpa [prefixWord, tailWord_1984470, baseEnd_1984470] using wordTrace_append hprefix tailTrace_1984470
  have hstable : (prefixWord ++ tailWord_1984470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984470).length < 2 ^ (prefixWord ++ tailWord_1984470).sum := by decide
  have hdescent : baseEnd_1984470 < baseStart_1984470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984499 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 4]
def baseStart_1984499 : Nat := 118140960795 + 1984499 * 2 ^ 59
def prefixEnd_1984499 : Nat := 4983230072969 + 3 ^ 40 * 1984499 * 2
def baseEnd_1984499 : Nat := 1019001845366936372235961

theorem tailTrace_1984499 : CollatzResearch.WordTrace tailWord_1984499 prefixEnd_1984499 1019001845366936372235961 := by
  unfold tailWord_1984499
  simp only [CollatzResearch.WordTrace]
  refine ⟨72380624837506523291076551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48253749891671015527384367 72380624837506523291076551)
  ·
    refine ⟨108570937256259784936614827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72380624837506523291076551 108570937256259784936614827)
    ·
      refine ⟨162856405884389677404922241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108570937256259784936614827 162856405884389677404922241)
      ·
        refine ⟨122142304413292258053691681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162856405884389677404922241 122142304413292258053691681)
        ·
          refine ⟨91606728309969193540268761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122142304413292258053691681 91606728309969193540268761)
          ·
            refine ⟨68705046232476895155201571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91606728309969193540268761 68705046232476895155201571)
            ·
              refine ⟨103057569348715342732802357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68705046232476895155201571 103057569348715342732802357)
              ·
                refine ⟨9661647126442063381200221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103057569348715342732802357 9661647126442063381200221)
                ·
                  refine ⟨3623117672415773767950083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9661647126442063381200221 3623117672415773767950083)
                  ·
                    refine ⟨5434676508623660651925125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3623117672415773767950083 5434676508623660651925125)
                    ·
                      refine ⟨1019001845366936372235961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5434676508623660651925125 1019001845366936372235961)
                      ·
                        rfl

theorem cell23_1984499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_1984499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984499 prefixEnd_1984499 := by exact prefixLift 1984499
  have htrace : WordTrace (prefixWord ++ tailWord_1984499) baseStart_1984499 baseEnd_1984499 := by
    simpa [prefixWord, tailWord_1984499, baseEnd_1984499] using wordTrace_append hprefix tailTrace_1984499
  have hstable : (prefixWord ++ tailWord_1984499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984499).length < 2 ^ (prefixWord ++ tailWord_1984499).sum := by decide
  have hdescent : baseEnd_1984499 < baseStart_1984499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984509 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_1984509 : Nat := 118140960795 + 1984509 * 2 ^ 59
def prefixEnd_1984509 : Nat := 4983230072969 + 3 ^ 40 * 1984509 * 2
def baseEnd_1984509 : Nat := 339668993391160444370305

theorem tailTrace_1984509 : CollatzResearch.WordTrace tailWord_1984509 prefixEnd_1984509 339668993391160444370305 := by
  unfold tailWord_1984509
  simp only [CollatzResearch.WordTrace]
  refine ⟨72380989567470294998940581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48253993044980196665960387 72380989567470294998940581)
  ·
    refine ⟨13571435543900680312301359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72380989567470294998940581 13571435543900680312301359)
    ·
      refine ⟨20357153315851020468452039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13571435543900680312301359 20357153315851020468452039)
      ·
        refine ⟨30535729973776530702678059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20357153315851020468452039 30535729973776530702678059)
        ·
          refine ⟨45803594960664796054017089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30535729973776530702678059 45803594960664796054017089)
          ·
            refine ⟨34352696220498597040512817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45803594960664796054017089 34352696220498597040512817)
            ·
              refine ⟨25764522165373947780384613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34352696220498597040512817 25764522165373947780384613)
              ·
                refine ⟨4830847906007615208822115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25764522165373947780384613 4830847906007615208822115)
                ·
                  refine ⟨7246271859011422813233173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830847906007615208822115 7246271859011422813233173)
                  ·
                    refine ⟨339668993391160444370305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7246271859011422813233173 339668993391160444370305)
                    ·
                      rfl

theorem cell23_1984509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_1984509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984509 prefixEnd_1984509 := by exact prefixLift 1984509
  have htrace : WordTrace (prefixWord ++ tailWord_1984509) baseStart_1984509 baseEnd_1984509 := by
    simpa [prefixWord, tailWord_1984509, baseEnd_1984509] using wordTrace_append hprefix tailTrace_1984509
  have hstable : (prefixWord ++ tailWord_1984509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984509).length < 2 ^ (prefixWord ++ tailWord_1984509).sum := by decide
  have hdescent : baseEnd_1984509 < baseStart_1984509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984526 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_1984526 : Nat := 118140960795 + 1984526 * 2 ^ 59
def prefixEnd_1984526 : Nat := 4983230072969 + 3 ^ 40 * 1984526 * 2
def baseEnd_1984526 : Nat := 339671903114869255532779

theorem tailTrace_1984526 : CollatzResearch.WordTrace tailWord_1984526 prefixEnd_1984526 339671903114869255532779 := by
  unfold tailWord_1984526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9047701201051088362788679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48254406405605804601539621 9047701201051088362788679)
  ·
    refine ⟨13571551801576632544183019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9047701201051088362788679 13571551801576632544183019)
    ·
      refine ⟨20357327702364948816274529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13571551801576632544183019 20357327702364948816274529)
      ·
        refine ⟨15267995776773711612205897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20357327702364948816274529 15267995776773711612205897)
        ·
          refine ⟨11450996832580283709154423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15267995776773711612205897 11450996832580283709154423)
          ·
            refine ⟨17176495248870425563731635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11450996832580283709154423 17176495248870425563731635)
            ·
              refine ⟨25764742873305638345597453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17176495248870425563731635 25764742873305638345597453)
              ·
                refine ⟨9661778577489614379599045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25764742873305638345597453 9661778577489614379599045)
                ·
                  refine ⟨1811583483279302696174821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9661778577489614379599045 1811583483279302696174821)
                  ·
                    refine ⟨339671903114869255532779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1811583483279302696174821 339671903114869255532779)
                    ·
                      rfl

theorem cell23_1984526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_1984526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984526 prefixEnd_1984526 := by exact prefixLift 1984526
  have htrace : WordTrace (prefixWord ++ tailWord_1984526) baseStart_1984526 baseEnd_1984526 := by
    simpa [prefixWord, tailWord_1984526, baseEnd_1984526] using wordTrace_append hprefix tailTrace_1984526
  have hstable : (prefixWord ++ tailWord_1984526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984526).length < 2 ^ (prefixWord ++ tailWord_1984526).sum := by decide
  have hdescent : baseEnd_1984526 < baseStart_1984526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984536 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1984536 : Nat := 118140960795 + 1984536 * 2 ^ 59
def prefixEnd_1984536 : Nat := 4983230072969 + 3 ^ 40 * 1984536 * 2
def baseEnd_1984536 : Nat := 1019020844151152727473291

theorem tailTrace_1984536 : CollatzResearch.WordTrace tailWord_1984536 prefixEnd_1984536 1019020844151152727473291 := by
  unfold tailWord_1984536
  simp only [CollatzResearch.WordTrace]
  refine ⟨36190987169186239305086731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48254649558914985740115641 36190987169186239305086731)
  ·
    refine ⟨54286480753779358957630097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36190987169186239305086731 54286480753779358957630097)
    ·
      refine ⟨40714860565334519218222573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54286480753779358957630097 40714860565334519218222573)
      ·
        refine ⟨15268072712000444706833465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40714860565334519218222573 15268072712000444706833465)
        ·
          refine ⟨11451054534000333530125099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15268072712000444706833465 11451054534000333530125099)
          ·
            refine ⟨17176581801000500295187649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11451054534000333530125099 17176581801000500295187649)
            ·
              refine ⟨12882436350750375221390737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17176581801000500295187649 12882436350750375221390737)
              ·
                refine ⟨9661827263062781416043053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12882436350750375221390737 9661827263062781416043053)
                ·
                  refine ⟨3623185223648543031016145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9661827263062781416043053 3623185223648543031016145)
                  ·
                    refine ⟨2717388917736407273262109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3623185223648543031016145 2717388917736407273262109)
                    ·
                      refine ⟨1019020844151152727473291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2717388917736407273262109 1019020844151152727473291)
                      ·
                        rfl

theorem cell23_1984536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1984536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984536 prefixEnd_1984536 := by exact prefixLift 1984536
  have htrace : WordTrace (prefixWord ++ tailWord_1984536) baseStart_1984536 baseEnd_1984536 := by
    simpa [prefixWord, tailWord_1984536, baseEnd_1984536] using wordTrace_append hprefix tailTrace_1984536
  have hstable : (prefixWord ++ tailWord_1984536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984536).length < 2 ^ (prefixWord ++ tailWord_1984536).sum := by decide
  have hdescent : baseEnd_1984536 < baseStart_1984536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984546 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_1984546 : Nat := 118140960795 + 1984546 * 2 ^ 59
def prefixEnd_1984546 : Nat := 4983230072969 + 3 ^ 40 * 1984546 * 2
def baseEnd_1984546 : Nat := 1019025978957697688348245

theorem tailTrace_1984546 : CollatzResearch.WordTrace tailWord_1984546 prefixEnd_1984546 1019025978957697688348245 := by
  unfold tailWord_1984546
  simp only [CollatzResearch.WordTrace]
  refine ⟨18095584767084062579509373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48254892712224166878691661 18095584767084062579509373)
  ·
    refine ⟨6785844287656523467316015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18095584767084062579509373 6785844287656523467316015)
    ·
      refine ⟨10178766431484785200974023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6785844287656523467316015 10178766431484785200974023)
      ·
        refine ⟨15268149647227177801461035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10178766431484785200974023 15268149647227177801461035)
        ·
          refine ⟨22902224470840766702191553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15268149647227177801461035 22902224470840766702191553)
          ·
            refine ⟨17176668353130575026643665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22902224470840766702191553 17176668353130575026643665)
            ·
              refine ⟨12882501264847931269982749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17176668353130575026643665 12882501264847931269982749)
              ·
                refine ⟨4830937974317974226243531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12882501264847931269982749 4830937974317974226243531)
                ·
                  refine ⟨7246406961476961339365297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830937974317974226243531 7246406961476961339365297)
                  ·
                    refine ⟨5434805221107721004523973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7246406961476961339365297 5434805221107721004523973)
                    ·
                      refine ⟨1019025978957697688348245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5434805221107721004523973 1019025978957697688348245)
                      ·
                        rfl

theorem cell23_1984546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_1984546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984546 prefixEnd_1984546 := by exact prefixLift 1984546
  have htrace : WordTrace (prefixWord ++ tailWord_1984546) baseStart_1984546 baseEnd_1984546 := by
    simpa [prefixWord, tailWord_1984546, baseEnd_1984546] using wordTrace_append hprefix tailTrace_1984546
  have hstable : (prefixWord ++ tailWord_1984546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984546).length < 2 ^ (prefixWord ++ tailWord_1984546).sum := by decide
  have hdescent : baseEnd_1984546 < baseStart_1984546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984599 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 1, 8]
def baseStart_1984599 : Nat := 118140960795 + 1984599 * 2 ^ 59
def prefixEnd_1984599 : Nat := 4983230072969 + 3 ^ 40 * 1984599 * 2
def baseEnd_1984599 : Nat := 339684397810795326995167

theorem tailTrace_1984599 : CollatzResearch.WordTrace tailWord_1984599 prefixEnd_1984599 339684397810795326995167 := by
  unfold tailWord_1984599
  simp only [CollatzResearch.WordTrace]
  refine ⟨72384272137144240369716851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48256181424762826913144567 72384272137144240369716851)
  ·
    refine ⟨108576408205716360554575277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72384272137144240369716851 108576408205716360554575277)
    ·
      refine ⟨40716153077143635207965729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108576408205716360554575277 40716153077143635207965729)
      ·
        refine ⟨30537114807857726405974297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40716153077143635207965729 30537114807857726405974297)
        ·
          refine ⟨22902836105893294804480723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30537114807857726405974297 22902836105893294804480723)
          ·
            refine ⟨34354254158839942206721085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22902836105893294804480723 34354254158839942206721085)
            ·
              refine ⟨12882845309564978327520407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34354254158839942206721085 12882845309564978327520407)
              ·
                refine ⟨19324267964347467491280611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12882845309564978327520407 19324267964347467491280611)
                ·
                  refine ⟨28986401946521201236920917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19324267964347467491280611 28986401946521201236920917)
                  ·
                    refine ⟨339684397810795326995167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28986401946521201236920917 339684397810795326995167)
                    ·
                      rfl

theorem cell23_1984599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_1984599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984599 prefixEnd_1984599 := by exact prefixLift 1984599
  have htrace : WordTrace (prefixWord ++ tailWord_1984599) baseStart_1984599 baseEnd_1984599 := by
    simpa [prefixWord, tailWord_1984599, baseEnd_1984599] using wordTrace_append hprefix tailTrace_1984599
  have hstable : (prefixWord ++ tailWord_1984599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984599).length < 2 ^ (prefixWord ++ tailWord_1984599).sum := by decide
  have hdescent : baseEnd_1984599 < baseStart_1984599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984623 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 1, 4, 2]
def baseStart_1984623 : Nat := 118140960795 + 1984623 * 2 ^ 59
def prefixEnd_1984623 : Nat := 4983230072969 + 3 ^ 40 * 1984623 * 2
def baseEnd_1984623 : Nat := 1019065516968093887085391

theorem tailTrace_1984623 : CollatzResearch.WordTrace tailWord_1984623 prefixEnd_1984623 1019065516968093887085391 := by
  unfold tailWord_1984623
  simp only [CollatzResearch.WordTrace]
  refine ⟨72385147489057292468590523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48256764992704861645727015 72385147489057292468590523)
  ·
    refine ⟨108577721233585938702885785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72385147489057292468590523 108577721233585938702885785)
    ·
      refine ⟨81433290925189454027164339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108577721233585938702885785 81433290925189454027164339)
      ·
        refine ⟨122149936387784181040746509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81433290925189454027164339 122149936387784181040746509)
        ·
          refine ⟨45806226145419067890279941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122149936387784181040746509 45806226145419067890279941)
          ·
            refine ⟨8588667402266075229427489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45806226145419067890279941 8588667402266075229427489)
            ·
              refine ⟨6441500551699556422070617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8588667402266075229427489 6441500551699556422070617)
              ·
                refine ⟨4831125413774667316552963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6441500551699556422070617 4831125413774667316552963)
                ·
                  refine ⟨7246688120662000974829445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4831125413774667316552963 7246688120662000974829445)
                  ·
                    refine ⟨1358754022624125182780521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7246688120662000974829445 1358754022624125182780521)
                    ·
                      refine ⟨1019065516968093887085391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1358754022624125182780521 1019065516968093887085391)
                      ·
                        rfl

theorem cell23_1984623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 4, 2].length) (baseStart_1984623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984623 prefixEnd_1984623 := by exact prefixLift 1984623
  have htrace : WordTrace (prefixWord ++ tailWord_1984623) baseStart_1984623 baseEnd_1984623 := by
    simpa [prefixWord, tailWord_1984623, baseEnd_1984623] using wordTrace_append hprefix tailTrace_1984623
  have hstable : (prefixWord ++ tailWord_1984623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984623).length < 2 ^ (prefixWord ++ tailWord_1984623).sum := by decide
  have hdescent : baseEnd_1984623 < baseStart_1984623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984636 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_1984636 : Nat := 118140960795 + 1984636 * 2 ^ 59
def prefixEnd_1984636 : Nat := 4983230072969 + 3 ^ 40 * 1984636 * 2
def baseEnd_1984636 : Nat := 1019072192216602336222831

theorem tailTrace_1984636 : CollatzResearch.WordTrace tailWord_1984636 prefixEnd_1984636 1019072192216602336222831 := by
  unfold tailWord_1984636
  simp only [CollatzResearch.WordTrace]
  refine ⟨36192810819005097844406881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48257081092006797125875841 36192810819005097844406881)
  ·
    refine ⟨27144608114253823383305161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36192810819005097844406881 27144608114253823383305161)
    ·
      refine ⟨20358456085690367537478871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27144608114253823383305161 20358456085690367537478871)
      ·
        refine ⟨30537684128535551306218307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20358456085690367537478871 30537684128535551306218307)
        ·
          refine ⟨45806526192803326959327461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30537684128535551306218307 45806526192803326959327461)
          ·
            refine ⟨8588723661150623804873899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45806526192803326959327461 8588723661150623804873899)
            ·
              refine ⟨12883085491725935707310849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8588723661150623804873899 12883085491725935707310849)
              ·
                refine ⟨9662314118794451780483137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12883085491725935707310849 9662314118794451780483137)
                ·
                  refine ⟨7246735589095838835362353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9662314118794451780483137 7246735589095838835362353)
                  ·
                    refine ⟨5435051691821879126521765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7246735589095838835362353 5435051691821879126521765)
                    ·
                      refine ⟨1019072192216602336222831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5435051691821879126521765 1019072192216602336222831)
                      ·
                        rfl

theorem cell23_1984636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_1984636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984636 prefixEnd_1984636 := by exact prefixLift 1984636
  have htrace : WordTrace (prefixWord ++ tailWord_1984636) baseStart_1984636 baseEnd_1984636 := by
    simpa [prefixWord, tailWord_1984636, baseEnd_1984636] using wordTrace_append hprefix tailTrace_1984636
  have hstable : (prefixWord ++ tailWord_1984636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984636).length < 2 ^ (prefixWord ++ tailWord_1984636).sum := by decide
  have hdescent : baseEnd_1984636 < baseStart_1984636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984656 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 3]
def baseStart_1984656 : Nat := 118140960795 + 1984656 * 2 ^ 59
def prefixEnd_1984656 : Nat := 4983230072969 + 3 ^ 40 * 1984656 * 2
def baseEnd_1984656 : Nat := 1019082461829692257972739

theorem tailTrace_1984656 : CollatzResearch.WordTrace tailWord_1984656 prefixEnd_1984656 1019082461829692257972739 := by
  unfold tailWord_1984656
  simp only [CollatzResearch.WordTrace]
  refine ⟨36193175548968869552270911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48257567398625159403027881 36193175548968869552270911)
  ·
    refine ⟨54289763323453304328406367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36193175548968869552270911 54289763323453304328406367)
    ·
      refine ⟨81434644985179956492609551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54289763323453304328406367 81434644985179956492609551)
      ·
        refine ⟨122151967477769934738914327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81434644985179956492609551 122151967477769934738914327)
        ·
          refine ⟨183227951216654902108371491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122151967477769934738914327 183227951216654902108371491)
          ·
            refine ⟨274841926824982353162557237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183227951216654902108371491 274841926824982353162557237)
            ·
              refine ⟨25766430639842095608989741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274841926824982353162557237 25766430639842095608989741)
              ·
                refine ⟨9662411489940785853371153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25766430639842095608989741 9662411489940785853371153)
                ·
                  refine ⟨7246808617455589390028365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9662411489940785853371153 7246808617455589390028365)
                  ·
                    refine ⟨2717553231545846021260637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7246808617455589390028365 2717553231545846021260637)
                    ·
                      refine ⟨1019082461829692257972739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2717553231545846021260637 1019082461829692257972739)
                      ·
                        rfl

theorem cell23_1984656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 3].length) (baseStart_1984656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984656 prefixEnd_1984656 := by exact prefixLift 1984656
  have htrace : WordTrace (prefixWord ++ tailWord_1984656) baseStart_1984656 baseEnd_1984656 := by
    simpa [prefixWord, tailWord_1984656, baseEnd_1984656] using wordTrace_append hprefix tailTrace_1984656
  have hstable : (prefixWord ++ tailWord_1984656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984656).length < 2 ^ (prefixWord ++ tailWord_1984656).sum := by decide
  have hdescent : baseEnd_1984656 < baseStart_1984656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984740 : List Nat := [2, 3, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_1984740 : Nat := 118140960795 + 1984740 * 2 ^ 59
def prefixEnd_1984740 : Nat := 4983230072969 + 3 ^ 40 * 1984740 * 2
def baseEnd_1984740 : Nat := 339708531401556643107451

theorem tailTrace_1984740 : CollatzResearch.WordTrace tailWord_1984740 prefixEnd_1984740 339708531401556643107451 := by
  unfold tailWord_1984740
  simp only [CollatzResearch.WordTrace]
  refine ⟨36194707414816710725299837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48259609886422280967066449 36194707414816710725299837)
  ·
    refine ⟨13573015280556266521987439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36194707414816710725299837 13573015280556266521987439)
    ·
      refine ⟨20359522920834399782981159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13573015280556266521987439 20359522920834399782981159)
      ·
        refine ⟨30539284381251599674471739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20359522920834399782981159 30539284381251599674471739)
        ·
          refine ⟨45808926571877399511707609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30539284381251599674471739 45808926571877399511707609)
          ·
            refine ⟨34356694928908049633780707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45808926571877399511707609 34356694928908049633780707)
            ·
              refine ⟨51535042393362074450671061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34356694928908049633780707 51535042393362074450671061)
              ·
                refine ⟨1207852556094423619937603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51535042393362074450671061 1207852556094423619937603)
                ·
                  refine ⟨1811778834141635429906405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207852556094423619937603 1811778834141635429906405)
                  ·
                    refine ⟨339708531401556643107451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1811778834141635429906405 339708531401556643107451)
                    ·
                      rfl

theorem cell23_1984740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_1984740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984740 prefixEnd_1984740 := by exact prefixLift 1984740
  have htrace : WordTrace (prefixWord ++ tailWord_1984740) baseStart_1984740 baseEnd_1984740 := by
    simpa [prefixWord, tailWord_1984740, baseEnd_1984740] using wordTrace_append hprefix tailTrace_1984740
  have hstable : (prefixWord ++ tailWord_1984740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984740).length < 2 ^ (prefixWord ++ tailWord_1984740).sum := by decide
  have hdescent : baseEnd_1984740 < baseStart_1984740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984763 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 9, 1, 3]
def baseStart_1984763 : Nat := 118140960795 + 1984763 * 2 ^ 59
def prefixEnd_1984763 : Nat := 4983230072969 + 3 ^ 40 * 1984763 * 2
def baseEnd_1984763 : Nat := 1019137404259723339334747

theorem tailTrace_1984763 : CollatzResearch.WordTrace tailWord_1984763 prefixEnd_1984763 1019137404259723339334747 := by
  unfold tailWord_1984763
  simp only [CollatzResearch.WordTrace]
  refine ⟨72390253708550096378686943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48260169139033397585791295 72390253708550096378686943)
  ·
    refine ⟨108585380562825144568030415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72390253708550096378686943 108585380562825144568030415)
    ·
      refine ⟨162878070844237716852045623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108585380562825144568030415 162878070844237716852045623)
      ·
        refine ⟨244317106266356575278068435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162878070844237716852045623 244317106266356575278068435)
        ·
          refine ⟨366475659399534862917102653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244317106266356575278068435 366475659399534862917102653)
          ·
            refine ⟨137428372274825573593913495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366475659399534862917102653 137428372274825573593913495)
            ·
              refine ⟨206142558412238360390870243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137428372274825573593913495 206142558412238360390870243)
              ·
                refine ⟨309213837618357540586305365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206142558412238360390870243 309213837618357540586305365)
                ·
                  refine ⟨1811799829795063714372883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 309213837618357540586305365 1811799829795063714372883)
                  ·
                    refine ⟨2717699744692595571559325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1811799829795063714372883 2717699744692595571559325)
                    ·
                      refine ⟨1019137404259723339334747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2717699744692595571559325 1019137404259723339334747)
                      ·
                        rfl

theorem cell23_1984763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 1, 3].length) (baseStart_1984763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984763 prefixEnd_1984763 := by exact prefixLift 1984763
  have htrace : WordTrace (prefixWord ++ tailWord_1984763) baseStart_1984763 baseEnd_1984763 := by
    simpa [prefixWord, tailWord_1984763, baseEnd_1984763] using wordTrace_append hprefix tailTrace_1984763
  have hstable : (prefixWord ++ tailWord_1984763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984763).length < 2 ^ (prefixWord ++ tailWord_1984763).sum := by decide
  have hdescent : baseEnd_1984763 < baseStart_1984763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984770 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1984770 : Nat := 118140960795 + 1984770 * 2 ^ 59
def prefixEnd_1984770 : Nat := 4983230072969 + 3 ^ 40 * 1984770 * 2
def baseEnd_1984770 : Nat := 113237888736033867994135

theorem tailTrace_1984770 : CollatzResearch.WordTrace tailWord_1984770 prefixEnd_1984770 113237888736033867994135 := by
  unfold tailWord_1984770
  simp only [CollatzResearch.WordTrace]
  refine ⟨18097627254881184143547941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48260339346349824382794509 18097627254881184143547941)
  ·
    refine ⟨3393305110290222026915239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18097627254881184143547941 3393305110290222026915239)
    ·
      refine ⟨5089957665435333040372859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3393305110290222026915239 5089957665435333040372859)
      ·
        refine ⟨7634936498152999560559289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5089957665435333040372859 7634936498152999560559289)
        ·
          refine ⟨5726202373614749670419467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7634936498152999560559289 5726202373614749670419467)
          ·
            refine ⟨8589303560422124505629201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726202373614749670419467 8589303560422124505629201)
            ·
              refine ⟨6441977670316593379221901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8589303560422124505629201 6441977670316593379221901)
              ·
                refine ⟨2415741626368722517208213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6441977670316593379221901 2415741626368722517208213)
                ·
                  refine ⟨113237888736033867994135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2415741626368722517208213 113237888736033867994135)
                  ·
                    rfl

theorem cell23_1984770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1984770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984770 prefixEnd_1984770 := by exact prefixLift 1984770
  have htrace : WordTrace (prefixWord ++ tailWord_1984770) baseStart_1984770 baseEnd_1984770 := by
    simpa [prefixWord, tailWord_1984770, baseEnd_1984770] using wordTrace_append hprefix tailTrace_1984770
  have hstable : (prefixWord ++ tailWord_1984770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984770).length < 2 ^ (prefixWord ++ tailWord_1984770).sum := by decide
  have hdescent : baseEnd_1984770 < baseStart_1984770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984780 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 3, 1, 3]
def baseStart_1984780 : Nat := 118140960795 + 1984780 * 2 ^ 59
def prefixEnd_1984780 : Nat := 4983230072969 + 3 ^ 40 * 1984780 * 2
def baseEnd_1984780 : Nat := 1019146133430849772822169

theorem tailTrace_1984780 : CollatzResearch.WordTrace tailWord_1984780 prefixEnd_1984780 1019146133430849772822169 := by
  unfold tailWord_1984780
  simp only [CollatzResearch.WordTrace]
  refine ⟨36195436874744254141027897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48260582499659005521370529 36195436874744254141027897)
  ·
    refine ⟨27146577656058190605770923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36195436874744254141027897 27146577656058190605770923)
    ·
      refine ⟨40719866484087285908656385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27146577656058190605770923 40719866484087285908656385)
      ·
        refine ⟨30539899863065464431492289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40719866484087285908656385 30539899863065464431492289)
        ·
          refine ⟨22904924897299098323619217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30539899863065464431492289 22904924897299098323619217)
          ·
            refine ⟨17178693672974323742714413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22904924897299098323619217 17178693672974323742714413)
            ·
              refine ⟨6442010127365371403517905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17178693672974323742714413 6442010127365371403517905)
              ·
                refine ⟨4831507595524028552638429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6442010127365371403517905 4831507595524028552638429)
                ·
                  refine ⟨1811815348321510707239411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4831507595524028552638429 1811815348321510707239411)
                  ·
                    refine ⟨2717723022482266060859117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1811815348321510707239411 2717723022482266060859117)
                    ·
                      refine ⟨1019146133430849772822169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2717723022482266060859117 1019146133430849772822169)
                      ·
                        rfl

theorem cell23_1984780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_1984780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984780 prefixEnd_1984780 := by exact prefixLift 1984780
  have htrace : WordTrace (prefixWord ++ tailWord_1984780) baseStart_1984780 baseEnd_1984780 := by
    simpa [prefixWord, tailWord_1984780, baseEnd_1984780] using wordTrace_append hprefix tailTrace_1984780
  have hstable : (prefixWord ++ tailWord_1984780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984780).length < 2 ^ (prefixWord ++ tailWord_1984780).sum := by decide
  have hdescent : baseEnd_1984780 < baseStart_1984780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984800 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 1, 5]
def baseStart_1984800 : Nat := 118140960795 + 1984800 * 2 ^ 59
def prefixEnd_1984800 : Nat := 4983230072969 + 3 ^ 40 * 1984800 * 2
def baseEnd_1984800 : Nat := 339718801014646564857359

theorem tailTrace_1984800 : CollatzResearch.WordTrace tailWord_1984800 prefixEnd_1984800 339718801014646564857359 := by
  unfold tailWord_1984800
  simp only [CollatzResearch.WordTrace]
  refine ⟨36195801604708025848891927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48261068806277367798522569 36195801604708025848891927)
  ·
    refine ⟨54293702407062038773337891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36195801604708025848891927 54293702407062038773337891)
    ·
      refine ⟨81440553610593058160006837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54293702407062038773337891 81440553610593058160006837)
      ·
        refine ⟨7635051900993099202500641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81440553610593058160006837 7635051900993099202500641)
        ·
          refine ⟨5726288925744824401875481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7635051900993099202500641 5726288925744824401875481)
          ·
            refine ⟨4294716694308618301406611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5726288925744824401875481 4294716694308618301406611)
            ·
              refine ⟨6442075041462927452109917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294716694308618301406611 6442075041462927452109917)
              ·
                refine ⟨2415778140548597794541219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6442075041462927452109917 2415778140548597794541219)
                ·
                  refine ⟨3623667210822896691811829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415778140548597794541219 3623667210822896691811829)
                  ·
                    refine ⟨339718801014646564857359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3623667210822896691811829 339718801014646564857359)
                    ·
                      rfl

theorem cell23_1984800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 5].length) (baseStart_1984800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984800 prefixEnd_1984800 := by exact prefixLift 1984800
  have htrace : WordTrace (prefixWord ++ tailWord_1984800) baseStart_1984800 baseEnd_1984800 := by
    simpa [prefixWord, tailWord_1984800, baseEnd_1984800] using wordTrace_append hprefix tailTrace_1984800
  have hstable : (prefixWord ++ tailWord_1984800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984800).length < 2 ^ (prefixWord ++ tailWord_1984800).sum := by decide
  have hdescent : baseEnd_1984800 < baseStart_1984800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984823 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 3]
def baseStart_1984823 : Nat := 118140960795 + 1984823 * 2 ^ 59
def prefixEnd_1984823 : Nat := 4983230072969 + 3 ^ 40 * 1984823 * 2
def baseEnd_1984823 : Nat := 1019168213098993104584471

theorem tailTrace_1984823 : CollatzResearch.WordTrace tailWord_1984823 prefixEnd_1984823 1019168213098993104584471 := by
  unfold tailWord_1984823
  simp only [CollatzResearch.WordTrace]
  refine ⟨72392442088332726625871123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48261628058888484417247415 72392442088332726625871123)
  ·
    refine ⟨108588663132499089938806685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72392442088332726625871123 108588663132499089938806685)
    ·
      refine ⟨40720748674687158727052507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108588663132499089938806685 40720748674687158727052507)
      ·
        refine ⟨61081123012030738090578761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40720748674687158727052507 61081123012030738090578761)
        ·
          refine ⟨45810842259023053567934071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61081123012030738090578761 45810842259023053567934071)
          ·
            refine ⟨68716263388534580351901107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45810842259023053567934071 68716263388534580351901107)
            ·
              refine ⟨103074395082801870527851661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68716263388534580351901107 103074395082801870527851661)
              ·
                refine ⟨38652898156050701447944373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103074395082801870527851661 38652898156050701447944373)
                ·
                  refine ⟨3623709202129753260744785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38652898156050701447944373 3623709202129753260744785)
                  ·
                    refine ⟨2717781901597314945558589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3623709202129753260744785 2717781901597314945558589)
                    ·
                      refine ⟨1019168213098993104584471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2717781901597314945558589 1019168213098993104584471)
                      ·
                        rfl

theorem cell23_1984823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_1984823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984823 prefixEnd_1984823 := by exact prefixLift 1984823
  have htrace : WordTrace (prefixWord ++ tailWord_1984823) baseStart_1984823 baseEnd_1984823 := by
    simpa [prefixWord, tailWord_1984823, baseEnd_1984823] using wordTrace_append hprefix tailTrace_1984823
  have hstable : (prefixWord ++ tailWord_1984823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984823).length < 2 ^ (prefixWord ++ tailWord_1984823).sum := by decide
  have hdescent : baseEnd_1984823 < baseStart_1984823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984830 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1984830 : Nat := 118140960795 + 1984830 * 2 ^ 59
def prefixEnd_1984830 : Nat := 4983230072969 + 3 ^ 40 * 1984830 * 2
def baseEnd_1984830 : Nat := 339723935821191525732313

theorem tailTrace_1984830 : CollatzResearch.WordTrace tailWord_1984830 prefixEnd_1984830 339723935821191525732313 := by
  unfold tailWord_1984830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049087174913420852671993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48261798266204911214250629 9049087174913420852671993)
  ·
    refine ⟨6786815381185065639503995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9049087174913420852671993 6786815381185065639503995)
    ·
      refine ⟨10180223071777598459255993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6786815381185065639503995 10180223071777598459255993)
      ·
        refine ⟨7635167303833198844441995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10180223071777598459255993 7635167303833198844441995)
        ·
          refine ⟨11452750955749798266662993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7635167303833198844441995 11452750955749798266662993)
          ·
            refine ⟨8589563216812348699997245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11452750955749798266662993 8589563216812348699997245)
            ·
              refine ⟨3221086206304630762498967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8589563216812348699997245 3221086206304630762498967)
              ·
                refine ⟨4831629309456946143748451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3221086206304630762498967 4831629309456946143748451)
                ·
                  refine ⟨7247443964185419215622677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4831629309456946143748451 7247443964185419215622677)
                  ·
                    refine ⟨339723935821191525732313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7247443964185419215622677 339723935821191525732313)
                    ·
                      rfl

theorem cell23_1984830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1984830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984830 prefixEnd_1984830 := by exact prefixLift 1984830
  have htrace : WordTrace (prefixWord ++ tailWord_1984830) baseStart_1984830 baseEnd_1984830 := by
    simpa [prefixWord, tailWord_1984830, baseEnd_1984830] using wordTrace_append hprefix tailTrace_1984830
  have hstable : (prefixWord ++ tailWord_1984830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984830).length < 2 ^ (prefixWord ++ tailWord_1984830).sum := by decide
  have hdescent : baseEnd_1984830 < baseStart_1984830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984840 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_1984840 : Nat := 118140960795 + 1984840 * 2 ^ 59
def prefixEnd_1984840 : Nat := 4983230072969 + 3 ^ 40 * 1984840 * 2
def baseEnd_1984840 : Nat := 1019176942270119538071893

theorem tailTrace_1984840 : CollatzResearch.WordTrace tailWord_1984840 prefixEnd_1984840 1019176942270119538071893 := by
  unfold tailWord_1984840
  simp only [CollatzResearch.WordTrace]
  refine ⟨36196531064635569264619987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48262041419514092352826649 36196531064635569264619987)
  ·
    refine ⟨54294796596953353896929981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36196531064635569264619987 54294796596953353896929981)
    ·
      refine ⟨20360548723857507711348743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54294796596953353896929981 20360548723857507711348743)
      ·
        refine ⟨30540823085786261567023115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20360548723857507711348743 30540823085786261567023115)
        ·
          refine ⟨45811234628679392350534673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30540823085786261567023115 45811234628679392350534673)
          ·
            refine ⟨34358425971509544262901005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45811234628679392350534673 34358425971509544262901005)
            ·
              refine ⟨12884409739316079098587877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34358425971509544262901005 12884409739316079098587877)
              ·
                refine ⟨2415826826121764830985227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12884409739316079098587877 2415826826121764830985227)
                ·
                  refine ⟨3623740239182647246477841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415826826121764830985227 3623740239182647246477841)
                  ·
                    refine ⟨2717805179386985434858381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3623740239182647246477841 2717805179386985434858381)
                    ·
                      refine ⟨1019176942270119538071893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2717805179386985434858381 1019176942270119538071893)
                      ·
                        rfl

theorem cell23_1984840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_1984840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984840 prefixEnd_1984840 := by exact prefixLift 1984840
  have htrace : WordTrace (prefixWord ++ tailWord_1984840) baseStart_1984840 baseEnd_1984840 := by
    simpa [prefixWord, tailWord_1984840, baseEnd_1984840] using wordTrace_append hprefix tailTrace_1984840
  have hstable : (prefixWord ++ tailWord_1984840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984840).length < 2 ^ (prefixWord ++ tailWord_1984840).sum := by decide
  have hdescent : baseEnd_1984840 < baseStart_1984840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984913 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 3]
def baseStart_1984913 : Nat := 118140960795 + 1984913 * 2 ^ 59
def prefixEnd_1984913 : Nat := 4983230072969 + 3 ^ 40 * 1984913 * 2
def baseEnd_1984913 : Nat := 1019214426357897752459057

theorem tailTrace_1984913 : CollatzResearch.WordTrace tailWord_1984913 prefixEnd_1984913 1019214426357897752459057 := by
  unfold tailWord_1984913
  simp only [CollatzResearch.WordTrace]
  refine ⟨72395724658006671996647393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48263816438671114664431595 72395724658006671996647393)
  ·
    refine ⟨54296793493505003997485545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72395724658006671996647393 54296793493505003997485545)
    ·
      refine ⟨40722595120128752998114159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54296793493505003997485545 40722595120128752998114159)
      ·
        refine ⟨61083892680193129497171239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40722595120128752998114159 61083892680193129497171239)
        ·
          refine ⟨91625839020289694245756859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61083892680193129497171239 91625839020289694245756859)
          ·
            refine ⟨137438758530434541368635289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91625839020289694245756859 137438758530434541368635289)
            ·
              refine ⟨103079068897825906026476467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137438758530434541368635289 103079068897825906026476467)
              ·
                refine ⟨154618603346738859039714701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103079068897825906026476467 154618603346738859039714701)
                ·
                  refine ⟨57981976255027072139893013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154618603346738859039714701 57981976255027072139893013)
                  ·
                    refine ⟨2717905136954394006557485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57981976255027072139893013 2717905136954394006557485)
                    ·
                      refine ⟨1019214426357897752459057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2717905136954394006557485 1019214426357897752459057)
                      ·
                        rfl

theorem cell23_1984913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_1984913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984913 prefixEnd_1984913 := by exact prefixLift 1984913
  have htrace : WordTrace (prefixWord ++ tailWord_1984913) baseStart_1984913 baseEnd_1984913 := by
    simpa [prefixWord, tailWord_1984913, baseEnd_1984913] using wordTrace_append hprefix tailTrace_1984913
  have hstable : (prefixWord ++ tailWord_1984913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984913).length < 2 ^ (prefixWord ++ tailWord_1984913).sum := by decide
  have hdescent : baseEnd_1984913 < baseStart_1984913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984930 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1984930 : Nat := 118140960795 + 1984930 * 2 ^ 59
def prefixEnd_1984930 : Nat := 4983230072969 + 3 ^ 40 * 1984930 * 2
def baseEnd_1984930 : Nat := 1019223155529024185946479

theorem tailTrace_1984930 : CollatzResearch.WordTrace tailWord_1984930 prefixEnd_1984930 1019223155529024185946479 := by
  unfold tailWord_1984930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18099086174736270975004061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48264229799296722600010829 18099086174736270975004061)
  ·
    refine ⟨6787157315526101615626523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18099086174736270975004061 6787157315526101615626523)
    ·
      refine ⟨10180735973289152423439785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6787157315526101615626523 10180735973289152423439785)
      ·
        refine ⟨7635551979966864317579839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10180735973289152423439785 7635551979966864317579839)
        ·
          refine ⟨11453327969950296476369759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7635551979966864317579839 11453327969950296476369759)
          ·
            refine ⟨17179991954925444714554639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11453327969950296476369759 17179991954925444714554639)
            ·
              refine ⟨25769987932388167071831959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17179991954925444714554639 25769987932388167071831959)
              ·
                refine ⟨38654981898582250607747939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25769987932388167071831959 38654981898582250607747939)
                ·
                  refine ⟨57982472847873375911621909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38654981898582250607747939 57982472847873375911621909)
                  ·
                    refine ⟨2717928414744064495857277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57982472847873375911621909 2717928414744064495857277)
                    ·
                      refine ⟨1019223155529024185946479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2717928414744064495857277 1019223155529024185946479)
                      ·
                        rfl

theorem cell23_1984930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1984930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984930 prefixEnd_1984930 := by exact prefixLift 1984930
  have htrace : WordTrace (prefixWord ++ tailWord_1984930) baseStart_1984930 baseEnd_1984930 := by
    simpa [prefixWord, tailWord_1984930, baseEnd_1984930] using wordTrace_append hprefix tailTrace_1984930
  have hstable : (prefixWord ++ tailWord_1984930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984930).length < 2 ^ (prefixWord ++ tailWord_1984930).sum := by decide
  have hdescent : baseEnd_1984930 < baseStart_1984930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984933 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 7]
def baseStart_1984933 : Nat := 118140960795 + 1984933 * 2 ^ 59
def prefixEnd_1984933 : Nat := 4983230072969 + 3 ^ 40 * 1984933 * 2
def baseEnd_1984933 : Nat := 113247188441220852689885

theorem tailTrace_1984933 : CollatzResearch.WordTrace tailWord_1984933 prefixEnd_1984933 113247188441220852689885 := by
  unfold tailWord_1984933
  simp only [CollatzResearch.WordTrace]
  refine ⟨72396454117934215412375453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48264302745289476941583635 72396454117934215412375453)
  ·
    refine ⟨27148670294225330779640795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72396454117934215412375453 27148670294225330779640795)
    ·
      refine ⟨40723005441337996169461193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27148670294225330779640795 40723005441337996169461193)
      ·
        refine ⟨30542254081003497127095895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40723005441337996169461193 30542254081003497127095895)
        ·
          refine ⟨45813381121505245690643843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30542254081003497127095895 45813381121505245690643843)
          ·
            refine ⟨68720071682257868535965765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45813381121505245690643843 68720071682257868535965765)
            ·
              refine ⟨12885013440423350350493581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68720071682257868535965765 12885013440423350350493581)
              ·
                refine ⟨4831880040158756381435093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12885013440423350350493581 4831880040158756381435093)
                ·
                  refine ⟨113247188441220852689885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4831880040158756381435093 113247188441220852689885)
                  ·
                    rfl

theorem cell23_1984933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_1984933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984933 prefixEnd_1984933 := by exact prefixLift 1984933
  have htrace : WordTrace (prefixWord ++ tailWord_1984933) baseStart_1984933 baseEnd_1984933 := by
    simpa [prefixWord, tailWord_1984933, baseEnd_1984933] using wordTrace_append hprefix tailTrace_1984933
  have hstable : (prefixWord ++ tailWord_1984933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984933).length < 2 ^ (prefixWord ++ tailWord_1984933).sum := by decide
  have hdescent : baseEnd_1984933 < baseStart_1984933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984967 : List Nat := [1, 1, 4, 1, 1, 5, 2, 3, 5]
def baseStart_1984967 : Nat := 118140960795 + 1984967 * 2 ^ 59
def prefixEnd_1984967 : Nat := 4983230072969 + 3 ^ 40 * 1984967 * 2
def baseEnd_1984967 : Nat := 113249128257026726798201

theorem tailTrace_1984967 : CollatzResearch.WordTrace tailWord_1984967 prefixEnd_1984967 113249128257026726798201 := by
  unfold tailWord_1984967
  simp only [CollatzResearch.WordTrace]
  refine ⟨72397694199811039219113155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48265129466540692812742103 72397694199811039219113155)
  ·
    refine ⟨108596541299716558828669733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72397694199811039219113155 108596541299716558828669733)
    ·
      refine ⟨20361851493696854780375575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108596541299716558828669733 20361851493696854780375575)
      ·
        refine ⟨30542777240545282170563363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20361851493696854780375575 30542777240545282170563363)
        ·
          refine ⟨45814165860817923255845045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30542777240545282170563363 45814165860817923255845045)
          ·
            refine ⟨4295078049451680305235473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45814165860817923255845045 4295078049451680305235473)
            ·
              refine ⟨3221308537088760228926605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4295078049451680305235473 3221308537088760228926605)
              ·
                refine ⟨1207990701408285085847477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3221308537088760228926605 1207990701408285085847477)
                ·
                  refine ⟨113249128257026726798201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1207990701408285085847477 113249128257026726798201)
                  ·
                    rfl

theorem cell23_1984967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 5].length) (baseStart_1984967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1984967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1984967 prefixEnd_1984967 := by exact prefixLift 1984967
  have htrace : WordTrace (prefixWord ++ tailWord_1984967) baseStart_1984967 baseEnd_1984967 := by
    simpa [prefixWord, tailWord_1984967, baseEnd_1984967] using wordTrace_append hprefix tailTrace_1984967
  have hstable : (prefixWord ++ tailWord_1984967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984967).length < 2 ^ (prefixWord ++ tailWord_1984967).sum := by decide
  have hdescent : baseEnd_1984967 < baseStart_1984967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985000 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1985000 : Nat := 118140960795 + 1985000 * 2 ^ 59
def prefixEnd_1985000 : Nat := 4983230072969 + 3 ^ 40 * 1985000 * 2
def baseEnd_1985000 : Nat := 1019259099174838912071157

theorem tailTrace_1985000 : CollatzResearch.WordTrace tailWord_1985000 prefixEnd_1985000 1019259099174838912071157 := by
  unfold tailWord_1985000
  simp only [CollatzResearch.WordTrace]
  refine ⟨36199448904345742927532227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48265931872460990570042969 36199448904345742927532227)
  ·
    refine ⟨54299173356518614391298341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36199448904345742927532227 54299173356518614391298341)
    ·
      refine ⟨10181095004347240198368439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54299173356518614391298341 10181095004347240198368439)
      ·
        refine ⟨15271642506520860297552659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10181095004347240198368439 15271642506520860297552659)
        ·
          refine ⟨22907463759781290446328989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15271642506520860297552659 22907463759781290446328989)
          ·
            refine ⟨8590298909917983917373371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22907463759781290446328989 8590298909917983917373371)
            ·
              refine ⟨12885448364876975876060057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8590298909917983917373371 12885448364876975876060057)
              ·
                refine ⟨9664086273657731907045043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12885448364876975876060057 9664086273657731907045043)
                ·
                  refine ⟨14496129410486597860567565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9664086273657731907045043 14496129410486597860567565)
                  ·
                    refine ⟨5436048528932474197712837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14496129410486597860567565 5436048528932474197712837)
                    ·
                      refine ⟨1019259099174838912071157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5436048528932474197712837 1019259099174838912071157)
                      ·
                        rfl

theorem cell23_1985000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1985000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985000 prefixEnd_1985000 := by exact prefixLift 1985000
  have htrace : WordTrace (prefixWord ++ tailWord_1985000) baseStart_1985000 baseEnd_1985000 := by
    simpa [prefixWord, tailWord_1985000, baseEnd_1985000] using wordTrace_append hprefix tailTrace_1985000
  have hstable : (prefixWord ++ tailWord_1985000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985000).length < 2 ^ (prefixWord ++ tailWord_1985000).sum := by decide
  have hdescent : baseEnd_1985000 < baseStart_1985000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985023 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 10]
def baseStart_1985023 : Nat := 118140960795 + 1985023 * 2 ^ 59
def prefixEnd_1985023 : Nat := 4983230072969 + 3 ^ 40 * 1985023 * 2
def baseEnd_1985023 : Nat := 113252323247765813564839

theorem tailTrace_1985023 : CollatzResearch.WordTrace tailWord_1985023 prefixEnd_1985023 113252323247765813564839 := by
  unfold tailWord_1985023
  simp only [CollatzResearch.WordTrace]
  refine ⟨72399736687608160783151723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48266491125072107188767815 72399736687608160783151723)
  ·
    refine ⟨108599605031412241174727585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72399736687608160783151723 108599605031412241174727585)
    ·
      refine ⟨81449703773559180881045689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108599605031412241174727585 81449703773559180881045689)
      ·
        refine ⟨61087277830169385660784267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81449703773559180881045689 61087277830169385660784267)
        ·
          refine ⟨91630916745254078491176401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61087277830169385660784267 91630916745254078491176401)
          ·
            refine ⟨68723187558940558868382301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91630916745254078491176401 68723187558940558868382301)
            ·
              refine ⟨25771195334602709575643363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68723187558940558868382301 25771195334602709575643363)
              ·
                refine ⟨38656793001904064363465045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25771195334602709575643363 38656793001904064363465045)
                ·
                  refine ⟨113252323247765813564839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 38656793001904064363465045 113252323247765813564839)
                  ·
                    rfl

theorem cell23_1985023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 10].length) (baseStart_1985023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985023 prefixEnd_1985023 := by exact prefixLift 1985023
  have htrace : WordTrace (prefixWord ++ tailWord_1985023) baseStart_1985023 baseEnd_1985023 := by
    simpa [prefixWord, tailWord_1985023, baseEnd_1985023] using wordTrace_append hprefix tailTrace_1985023
  have hstable : (prefixWord ++ tailWord_1985023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985023).length < 2 ^ (prefixWord ++ tailWord_1985023).sum := by decide
  have hdescent : baseEnd_1985023 < baseStart_1985023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985067 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 3, 1, 3]
def baseStart_1985067 : Nat := 118140960795 + 1985067 * 2 ^ 59
def prefixEnd_1985067 : Nat := 4983230072969 + 3 ^ 40 * 1985067 * 2
def baseEnd_1985067 : Nat := 1019293502378690149933349

theorem tailTrace_1985067 : CollatzResearch.WordTrace tailWord_1985067 prefixEnd_1985067 1019293502378690149933349 := by
  unfold tailWord_1985067
  simp only [CollatzResearch.WordTrace]
  refine ⟨72401341499448756297753455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48267560999632504198502303 72401341499448756297753455)
  ·
    refine ⟨108602012249173134446630183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72401341499448756297753455 108602012249173134446630183)
    ·
      refine ⟨162903018373759701669945275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108602012249173134446630183 162903018373759701669945275)
      ·
        refine ⟨244354527560639552504917913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162903018373759701669945275 244354527560639552504917913)
        ·
          refine ⟨183265895670479664378688435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244354527560639552504917913 183265895670479664378688435)
          ·
            refine ⟨274898843505719496568032653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183265895670479664378688435 274898843505719496568032653)
            ·
              refine ⟨103087066314644811213012245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274898843505719496568032653 103087066314644811213012245)
              ·
                refine ⟨4832206233498975525609949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103087066314644811213012245 4832206233498975525609949)
                ·
                  refine ⟨1812077337562115822103731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4832206233498975525609949 1812077337562115822103731)
                  ·
                    refine ⟨2718116006343173733155597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1812077337562115822103731 2718116006343173733155597)
                    ·
                      refine ⟨1019293502378690149933349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2718116006343173733155597 1019293502378690149933349)
                      ·
                        rfl

theorem cell23_1985067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 1, 3].length) (baseStart_1985067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985067 prefixEnd_1985067 := by exact prefixLift 1985067
  have htrace : WordTrace (prefixWord ++ tailWord_1985067) baseStart_1985067 baseEnd_1985067 := by
    simpa [prefixWord, tailWord_1985067, baseEnd_1985067] using wordTrace_append hprefix tailTrace_1985067
  have hstable : (prefixWord ++ tailWord_1985067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985067).length < 2 ^ (prefixWord ++ tailWord_1985067).sum := by decide
  have hdescent : baseEnd_1985067 < baseStart_1985067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985100 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_1985100 : Nat := 118140960795 + 1985100 * 2 ^ 59
def prefixEnd_1985100 : Nat := 4983230072969 + 3 ^ 40 * 1985100 * 2
def baseEnd_1985100 : Nat := 339770149080096173606899

theorem tailTrace_1985100 : CollatzResearch.WordTrace tailWord_1985100 prefixEnd_1985100 339770149080096173606899 := by
  unfold tailWord_1985100
  simp only [CollatzResearch.WordTrace]
  refine ⟨36201272554164601466852377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48268363405552801955803169 36201272554164601466852377)
  ·
    refine ⟨27150954415623451100139283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36201272554164601466852377 27150954415623451100139283)
    ·
      refine ⟨40726431623435176650208925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27150954415623451100139283 40726431623435176650208925)
      ·
        refine ⟨15272411858788191243828347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40726431623435176650208925 15272411858788191243828347)
        ·
          refine ⟨22908617788182286865742521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15272411858788191243828347 22908617788182286865742521)
          ·
            refine ⟨17181463341136715149306891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22908617788182286865742521 17181463341136715149306891)
            ·
              refine ⟨25772195011705072723960337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17181463341136715149306891 25772195011705072723960337)
              ·
                refine ⟨19329146258778804542970253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25772195011705072723960337 19329146258778804542970253)
                ·
                  refine ⟨7248429847042051703613845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19329146258778804542970253 7248429847042051703613845)
                  ·
                    refine ⟨339770149080096173606899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7248429847042051703613845 339770149080096173606899)
                    ·
                      rfl

theorem cell23_1985100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_1985100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985100 prefixEnd_1985100 := by exact prefixLift 1985100
  have htrace : WordTrace (prefixWord ++ tailWord_1985100) baseStart_1985100 baseEnd_1985100 := by
    simpa [prefixWord, tailWord_1985100, baseEnd_1985100] using wordTrace_append hprefix tailTrace_1985100
  have hstable : (prefixWord ++ tailWord_1985100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985100).length < 2 ^ (prefixWord ++ tailWord_1985100).sum := by decide
  have hdescent : baseEnd_1985100 < baseStart_1985100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985120 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1985120 : Nat := 118140960795 + 1985120 * 2 ^ 59
def prefixEnd_1985120 : Nat := 4983230072969 + 3 ^ 40 * 1985120 * 2
def baseEnd_1985120 : Nat := 1019320716853378442570605

theorem tailTrace_1985120 : CollatzResearch.WordTrace tailWord_1985120 prefixEnd_1985120 1019320716853378442570605 := by
  unfold tailWord_1985120
  simp only [CollatzResearch.WordTrace]
  refine ⟨36201637284128373174716407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48268849712171164232955209 36201637284128373174716407)
  ·
    refine ⟨54302455926192559762074611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36201637284128373174716407 54302455926192559762074611)
    ·
      refine ⟨81453683889288839643111917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54302455926192559762074611 81453683889288839643111917)
      ·
        refine ⟨30545131458483314866166969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81453683889288839643111917 30545131458483314866166969)
        ·
          refine ⟨22908848593862486149625227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30545131458483314866166969 22908848593862486149625227)
          ·
            refine ⟨34363272890793729224437841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22908848593862486149625227 34363272890793729224437841)
            ·
              refine ⟨25772454668095296918328381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34363272890793729224437841 25772454668095296918328381)
              ·
                refine ⟨9664670500535736344373143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25772454668095296918328381 9664670500535736344373143)
                ·
                  refine ⟨14497005750803604516559715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9664670500535736344373143 14497005750803604516559715)
                  ·
                    refine ⟨21745508626205406774839573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14497005750803604516559715 21745508626205406774839573)
                    ·
                      refine ⟨1019320716853378442570605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21745508626205406774839573 1019320716853378442570605)
                      ·
                        rfl

theorem cell23_1985120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1985120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985120 prefixEnd_1985120 := by exact prefixLift 1985120
  have htrace : WordTrace (prefixWord ++ tailWord_1985120) baseStart_1985120 baseEnd_1985120 := by
    simpa [prefixWord, tailWord_1985120, baseEnd_1985120] using wordTrace_append hprefix tailTrace_1985120
  have hstable : (prefixWord ++ tailWord_1985120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985120).length < 2 ^ (prefixWord ++ tailWord_1985120).sum := by decide
  have hdescent : baseEnd_1985120 < baseStart_1985120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985128 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_1985128 : Nat := 118140960795 + 1985128 * 2 ^ 59
def prefixEnd_1985128 : Nat := 4983230072969 + 3 ^ 40 * 1985128 * 2
def baseEnd_1985128 : Nat := 1019324824698614411270569

theorem tailTrace_1985128 : CollatzResearch.WordTrace tailWord_1985128 prefixEnd_1985128 1019324824698614411270569 := by
  unfold tailWord_1985128
  simp only [CollatzResearch.WordTrace]
  refine ⟨36201783176113881857862019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48269044234818509143816025 36201783176113881857862019)
  ·
    refine ⟨54302674764170822786793029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36201783176113881857862019 54302674764170822786793029)
    ·
      refine ⟨10181751518282029272523693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54302674764170822786793029 10181751518282029272523693)
      ·
        refine ⟨3818156819355760977196385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10181751518282029272523693 3818156819355760977196385)
        ·
          refine ⟨2863617614516820732897289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3818156819355760977196385 2863617614516820732897289)
          ·
            refine ⟨2147713210887615549672967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2863617614516820732897289 2147713210887615549672967)
            ·
              refine ⟨3221569816331423324509451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147713210887615549672967 3221569816331423324509451)
              ·
                refine ⟨4832354724497134986764177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3221569816331423324509451 4832354724497134986764177)
                ·
                  refine ⟨3624266043372851240073133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4832354724497134986764177 3624266043372851240073133)
                  ·
                    refine ⟨1359099766264819215027425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624266043372851240073133 1359099766264819215027425)
                    ·
                      refine ⟨1019324824698614411270569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1359099766264819215027425 1019324824698614411270569)
                      ·
                        rfl

theorem cell23_1985128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_1985128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985128 prefixEnd_1985128 := by exact prefixLift 1985128
  have htrace : WordTrace (prefixWord ++ tailWord_1985128) baseStart_1985128 baseEnd_1985128 := by
    simpa [prefixWord, tailWord_1985128, baseEnd_1985128] using wordTrace_append hprefix tailTrace_1985128
  have hstable : (prefixWord ++ tailWord_1985128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985128).length < 2 ^ (prefixWord ++ tailWord_1985128).sum := by decide
  have hdescent : baseEnd_1985128 < baseStart_1985128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985138 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_1985138 : Nat := 118140960795 + 1985138 * 2 ^ 59
def prefixEnd_1985138 : Nat := 4983230072969 + 3 ^ 40 * 1985138 * 2
def baseEnd_1985138 : Nat := 339776653168386457381841

theorem tailTrace_1985138 : CollatzResearch.WordTrace tailWord_1985138 prefixEnd_1985138 339776653168386457381841 := by
  unfold tailWord_1985138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18100982770547883855897017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48269287388127690282392045 18100982770547883855897017)
  ·
    refine ⟨13575737077910912891922763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18100982770547883855897017 13575737077910912891922763)
    ·
      refine ⟨20363605616866369337884145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13575737077910912891922763 20363605616866369337884145)
      ·
        refine ⟨15272704212649777003413109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20363605616866369337884145 15272704212649777003413109)
        ·
          refine ⟨1431816019935916594069979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15272704212649777003413109 1431816019935916594069979)
          ·
            refine ⟨2147724029903874891104969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431816019935916594069979 2147724029903874891104969)
            ·
              refine ⟨1610793022427906168328727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147724029903874891104969 1610793022427906168328727)
              ·
                refine ⟨2416189533641859252493091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610793022427906168328727 2416189533641859252493091)
                ·
                  refine ⟨3624284300462788878739637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416189533641859252493091 3624284300462788878739637)
                  ·
                    refine ⟨339776653168386457381841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3624284300462788878739637 339776653168386457381841)
                    ·
                      rfl

theorem cell23_1985138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_1985138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985138 prefixEnd_1985138 := by exact prefixLift 1985138
  have htrace : WordTrace (prefixWord ++ tailWord_1985138) baseStart_1985138 baseEnd_1985138 := by
    simpa [prefixWord, tailWord_1985138, baseEnd_1985138] using wordTrace_append hprefix tailTrace_1985138
  have hstable : (prefixWord ++ tailWord_1985138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985138).length < 2 ^ (prefixWord ++ tailWord_1985138).sum := by decide
  have hdescent : baseEnd_1985138 < baseStart_1985138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985141 : List Nat := [1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1985141 : Nat := 118140960795 + 1985141 * 2 ^ 59
def prefixEnd_1985141 : Nat := 4983230072969 + 3 ^ 40 * 1985141 * 2
def baseEnd_1985141 : Nat := 1019331499947122860408009

theorem tailTrace_1985141 : CollatzResearch.WordTrace tailWord_1985141 prefixEnd_1985141 1019331499947122860408009 := by
  unfold tailWord_1985141
  simp only [CollatzResearch.WordTrace]
  refine ⟨72404040501180666935947277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48269360334120444623964851 72404040501180666935947277)
  ·
    refine ⟨27151515187942750100980229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72404040501180666935947277 27151515187942750100980229)
    ·
      refine ⟨5090909097739265643933793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27151515187942750100980229 5090909097739265643933793)
      ·
        refine ⟨3818181823304449232950345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5090909097739265643933793 3818181823304449232950345)
        ·
          refine ⟨2863636367478336924712759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3818181823304449232950345 2863636367478336924712759)
          ·
            refine ⟨4295454551217505387069139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863636367478336924712759 4295454551217505387069139)
            ·
              refine ⟨6443181826826258080603709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4295454551217505387069139 6443181826826258080603709)
              ·
                refine ⟨2416193185059846780226391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6443181826826258080603709 2416193185059846780226391)
                ·
                  refine ⟨3624289777589770170339587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416193185059846780226391 3624289777589770170339587)
                  ·
                    refine ⟨5436434666384655255509381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3624289777589770170339587 5436434666384655255509381)
                    ·
                      refine ⟨1019331499947122860408009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5436434666384655255509381 1019331499947122860408009)
                      ·
                        rfl

theorem cell23_1985141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1985141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985141 prefixEnd_1985141 := by exact prefixLift 1985141
  have htrace : WordTrace (prefixWord ++ tailWord_1985141) baseStart_1985141 baseEnd_1985141 := by
    simpa [prefixWord, tailWord_1985141, baseEnd_1985141] using wordTrace_append hprefix tailTrace_1985141
  have hstable : (prefixWord ++ tailWord_1985141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985141).length < 2 ^ (prefixWord ++ tailWord_1985141).sum := by decide
  have hdescent : baseEnd_1985141 < baseStart_1985141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985178 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1985178 : Nat := 118140960795 + 1985178 * 2 ^ 59
def prefixEnd_1985178 : Nat := 4983230072969 + 3 ^ 40 * 1985178 * 2
def baseEnd_1985178 : Nat := 1019350498731339215645339

theorem tailTrace_1985178 : CollatzResearch.WordTrace tailWord_1985178 prefixEnd_1985178 1019350498731339215645339 := by
  unfold tailWord_1985178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18101347500511655563761047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48270260001364414836696125 18101347500511655563761047)
  ·
    refine ⟨27152021250767483345641571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18101347500511655563761047 27152021250767483345641571)
    ·
      refine ⟨40728031876151225018462357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27152021250767483345641571 40728031876151225018462357)
      ·
        refine ⟨1909126494194588672740423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40728031876151225018462357 1909126494194588672740423)
        ·
          refine ⟨2863689741291883009110635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909126494194588672740423 2863689741291883009110635)
          ·
            refine ⟨4295534611937824513665953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863689741291883009110635 4295534611937824513665953)
            ·
              refine ⟨3221650958953368385249465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4295534611937824513665953 3221650958953368385249465)
              ·
                refine ⟨2416238219215026288937099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3221650958953368385249465 2416238219215026288937099)
                ·
                  refine ⟨3624357328822539433405649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416238219215026288937099 3624357328822539433405649)
                  ·
                    refine ⟨2718267996616904575054237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3624357328822539433405649 2718267996616904575054237)
                    ·
                      refine ⟨1019350498731339215645339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2718267996616904575054237 1019350498731339215645339)
                      ·
                        rfl

theorem cell23_1985178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1985178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985178 prefixEnd_1985178 := by exact prefixLift 1985178
  have htrace : WordTrace (prefixWord ++ tailWord_1985178) baseStart_1985178 baseEnd_1985178 := by
    simpa [prefixWord, tailWord_1985178, baseEnd_1985178] using wordTrace_append hprefix tailTrace_1985178
  have hstable : (prefixWord ++ tailWord_1985178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985178).length < 2 ^ (prefixWord ++ tailWord_1985178).sum := by decide
  have hdescent : baseEnd_1985178 < baseStart_1985178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985274 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2]
def baseStart_1985274 : Nat := 118140960795 + 1985274 * 2 ^ 59
def prefixEnd_1985274 : Nat := 4983230072969 + 3 ^ 40 * 1985274 * 2
def baseEnd_1985274 : Nat := 1019399792874170840044897

theorem tailTrace_1985274 : CollatzResearch.WordTrace tailWord_1985274 prefixEnd_1985274 1019399792874170840044897 := by
  unfold tailWord_1985274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18102222852424707662634719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48272594273132553767025917 18102222852424707662634719)
  ·
    refine ⟨27153334278637061493952079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18102222852424707662634719 27153334278637061493952079)
    ·
      refine ⟨40730001417955592240928119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27153334278637061493952079 40730001417955592240928119)
      ·
        refine ⟨61095002126933388361392179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40730001417955592240928119 61095002126933388361392179)
        ·
          refine ⟨91642503190400082542088269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61095002126933388361392179 91642503190400082542088269)
          ·
            refine ⟨34365938696400030953283101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91642503190400082542088269 34365938696400030953283101)
            ·
              refine ⟨12887227011150011607481163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34365938696400030953283101 12887227011150011607481163)
              ·
                refine ⟨19330840516725017411221745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12887227011150011607481163 19330840516725017411221745)
                ·
                  refine ⟨14498130387543763058416309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19330840516725017411221745 14498130387543763058416309)
                  ·
                    refine ⟨1359199723832227786726529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14498130387543763058416309 1359199723832227786726529)
                    ·
                      refine ⟨1019399792874170840044897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1359199723832227786726529 1019399792874170840044897)
                      ·
                        rfl

theorem cell23_1985274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2].length) (baseStart_1985274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985274 prefixEnd_1985274 := by exact prefixLift 1985274
  have htrace : WordTrace (prefixWord ++ tailWord_1985274) baseStart_1985274 baseEnd_1985274 := by
    simpa [prefixWord, tailWord_1985274, baseEnd_1985274] using wordTrace_append hprefix tailTrace_1985274
  have hstable : (prefixWord ++ tailWord_1985274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985274).length < 2 ^ (prefixWord ++ tailWord_1985274).sum := by decide
  have hdescent : baseEnd_1985274 < baseStart_1985274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985277 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_1985277 : Nat := 118140960795 + 1985277 * 2 ^ 59
def prefixEnd_1985277 : Nat := 4983230072969 + 3 ^ 40 * 1985277 * 2
def baseEnd_1985277 : Nat := 1019401333316134328307383

theorem tailTrace_1985277 : CollatzResearch.WordTrace tailWord_1985277 prefixEnd_1985277 1019401333316134328307383 := by
  unfold tailWord_1985277
  simp only [CollatzResearch.WordTrace]
  refine ⟨72409000828687962162898085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48272667219125308108598723 72409000828687962162898085)
  ·
    refine ⟨13576687655378992905543391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72409000828687962162898085 13576687655378992905543391)
    ·
      refine ⟨20365031483068489358315087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13576687655378992905543391 20365031483068489358315087)
      ·
        refine ⟨30547547224602734037472631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20365031483068489358315087 30547547224602734037472631)
        ·
          refine ⟨45821320836904101056208947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30547547224602734037472631 45821320836904101056208947)
          ·
            refine ⟨68731981255356151584313421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45821320836904101056208947 68731981255356151584313421)
            ·
              refine ⟨25774492970758556844117533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68731981255356151584313421 25774492970758556844117533)
              ·
                refine ⟨9665434864034458816544075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25774492970758556844117533 9665434864034458816544075)
                ·
                  refine ⟨14498152296051688224816113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9665434864034458816544075 14498152296051688224816113)
                  ·
                    refine ⟨10873614222038766168612085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14498152296051688224816113 10873614222038766168612085)
                    ·
                      refine ⟨1019401333316134328307383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10873614222038766168612085 1019401333316134328307383)
                      ·
                        rfl

theorem cell23_1985277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_1985277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985277 prefixEnd_1985277 := by exact prefixLift 1985277
  have htrace : WordTrace (prefixWord ++ tailWord_1985277) baseStart_1985277 baseEnd_1985277 := by
    simpa [prefixWord, tailWord_1985277, baseEnd_1985277] using wordTrace_append hprefix tailTrace_1985277
  have hstable : (prefixWord ++ tailWord_1985277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985277).length < 2 ^ (prefixWord ++ tailWord_1985277).sum := by decide
  have hdescent : baseEnd_1985277 < baseStart_1985277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985304 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 3, 6, 2]
def baseStart_1985304 : Nat := 118140960795 + 1985304 * 2 ^ 59
def prefixEnd_1985304 : Nat := 4983230072969 + 3 ^ 40 * 1985304 * 2
def baseEnd_1985304 : Nat := 1019415197293805722669759

theorem tailTrace_1985304 : CollatzResearch.WordTrace tailWord_1985304 prefixEnd_1985304 1019415197293805722669759 := by
  unfold tailWord_1985304
  simp only [CollatzResearch.WordTrace]
  refine ⟨36204992799795072887065483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48273323733060097182753977 36204992799795072887065483)
  ·
    refine ⟨54307489199692609330598225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36204992799795072887065483 54307489199692609330598225)
    ·
      refine ⟨40730616899769456997948669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54307489199692609330598225 40730616899769456997948669)
      ·
        refine ⟨15273981337413546374230751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40730616899769456997948669 15273981337413546374230751)
        ·
          refine ⟨22910972006120319561346127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15273981337413546374230751 22910972006120319561346127)
          ·
            refine ⟨34366458009180479342019191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22910972006120319561346127 34366458009180479342019191)
            ·
              refine ⟨51549687013770719013028787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34366458009180479342019191 51549687013770719013028787)
              ·
                refine ⟨77324530520656078519543181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51549687013770719013028787 77324530520656078519543181)
                ·
                  refine ⟨28996698945246029444828693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77324530520656078519543181 28996698945246029444828693)
                  ·
                    refine ⟨1359220263058407630226345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28996698945246029444828693 1359220263058407630226345)
                    ·
                      refine ⟨1019415197293805722669759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1359220263058407630226345 1019415197293805722669759)
                      ·
                        rfl

theorem cell23_1985304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_1985304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985304 prefixEnd_1985304 := by exact prefixLift 1985304
  have htrace : WordTrace (prefixWord ++ tailWord_1985304) baseStart_1985304 baseEnd_1985304 := by
    simpa [prefixWord, tailWord_1985304, baseEnd_1985304] using wordTrace_append hprefix tailTrace_1985304
  have hstable : (prefixWord ++ tailWord_1985304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985304).length < 2 ^ (prefixWord ++ tailWord_1985304).sum := by decide
  have hdescent : baseEnd_1985304 < baseStart_1985304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985317 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_1985317 : Nat := 118140960795 + 1985317 * 2 ^ 59
def prefixEnd_1985317 : Nat := 4983230072969 + 3 ^ 40 * 1985317 * 2
def baseEnd_1985317 : Nat := 1019421872542314171807199

theorem tailTrace_1985317 : CollatzResearch.WordTrace tailWord_1985317 prefixEnd_1985317 1019421872542314171807199 := by
  unfold tailWord_1985317
  simp only [CollatzResearch.WordTrace]
  refine ⟨72410459748543048994354205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48273639832362032662902803 72410459748543048994354205)
  ·
    refine ⟨27153922405703643372882827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72410459748543048994354205 27153922405703643372882827)
    ·
      refine ⟨40730883608555465059324241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27153922405703643372882827 40730883608555465059324241)
      ·
        refine ⟨30548162706416598794493181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40730883608555465059324241 30548162706416598794493181)
        ·
          refine ⟨11455561014906224547934943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30548162706416598794493181 11455561014906224547934943)
          ·
            refine ⟨17183341522359336821902415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11455561014906224547934943 17183341522359336821902415)
            ·
              refine ⟨25775012283539005232853623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17183341522359336821902415 25775012283539005232853623)
              ·
                refine ⟨38662518425308507849280435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25775012283539005232853623 38662518425308507849280435)
                ·
                  refine ⟨57993777637962761773920653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38662518425308507849280435 57993777637962761773920653)
                  ·
                    refine ⟨21747666614236035665220245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57993777637962761773920653 21747666614236035665220245)
                    ·
                      refine ⟨1019421872542314171807199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21747666614236035665220245 1019421872542314171807199)
                      ·
                        rfl

theorem cell23_1985317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_1985317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985317 prefixEnd_1985317 := by exact prefixLift 1985317
  have htrace : WordTrace (prefixWord ++ tailWord_1985317) baseStart_1985317 baseEnd_1985317 := by
    simpa [prefixWord, tailWord_1985317, baseEnd_1985317] using wordTrace_append hprefix tailTrace_1985317
  have hstable : (prefixWord ++ tailWord_1985317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985317).length < 2 ^ (prefixWord ++ tailWord_1985317).sum := by decide
  have hdescent : baseEnd_1985317 < baseStart_1985317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985324 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 3]
def baseStart_1985324 : Nat := 118140960795 + 1985324 * 2 ^ 59
def prefixEnd_1985324 : Nat := 4983230072969 + 3 ^ 40 * 1985324 * 2
def baseEnd_1985324 : Nat := 1019425466906895644419667

theorem tailTrace_1985324 : CollatzResearch.WordTrace tailWord_1985324 prefixEnd_1985324 1019425466906895644419667 := by
  unfold tailWord_1985324
  simp only [CollatzResearch.WordTrace]
  refine ⟨36205357529758844594929513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48273810039678459459906017 36205357529758844594929513)
  ·
    refine ⟨27154018147319133446197135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36205357529758844594929513 27154018147319133446197135)
    ·
      refine ⟨40731027220978700169295703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27154018147319133446197135 40731027220978700169295703)
      ·
        refine ⟨61096540831468050253943555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40731027220978700169295703 61096540831468050253943555)
        ·
          refine ⟨91644811247202075380915333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61096540831468050253943555 91644811247202075380915333)
          ·
            refine ⟨17183402108850389133921625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91644811247202075380915333 17183402108850389133921625)
            ·
              refine ⟨12887551581637791850441219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17183402108850389133921625 12887551581637791850441219)
              ·
                refine ⟨19331327372456687775661829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12887551581637791850441219 19331327372456687775661829)
                ·
                  refine ⟨3624623882335628957936593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19331327372456687775661829 3624623882335628957936593)
                  ·
                    refine ⟨2718467911751721718452445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3624623882335628957936593 2718467911751721718452445)
                    ·
                      refine ⟨1019425466906895644419667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2718467911751721718452445 1019425466906895644419667)
                      ·
                        rfl

theorem cell23_1985324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_1985324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985324 prefixEnd_1985324 := by exact prefixLift 1985324
  have htrace : WordTrace (prefixWord ++ tailWord_1985324) baseStart_1985324 baseEnd_1985324 := by
    simpa [prefixWord, tailWord_1985324, baseEnd_1985324] using wordTrace_append hprefix tailTrace_1985324
  have hstable : (prefixWord ++ tailWord_1985324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985324).length < 2 ^ (prefixWord ++ tailWord_1985324).sum := by decide
  have hdescent : baseEnd_1985324 < baseStart_1985324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985331 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 3, 4]
def baseStart_1985331 : Nat := 118140960795 + 1985331 * 2 ^ 59
def prefixEnd_1985331 : Nat := 4983230072969 + 3 ^ 40 * 1985331 * 2
def baseEnd_1985331 : Nat := 339809687090492372344045

theorem tailTrace_1985331 : CollatzResearch.WordTrace tailWord_1985331 prefixEnd_1985331 339809687090492372344045 := by
  unfold tailWord_1985331
  simp only [CollatzResearch.WordTrace]
  refine ⟨72410970370492329385363847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48273980246994886256909231 72410970370492329385363847)
  ·
    refine ⟨108616455555738494078045771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72410970370492329385363847 108616455555738494078045771)
    ·
      refine ⟨162924683333607741117068657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108616455555738494078045771 162924683333607741117068657)
      ·
        refine ⟨122193512500205805837801493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162924683333607741117068657 122193512500205805837801493)
        ·
          refine ⟨5727820898447147148646945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122193512500205805837801493 5727820898447147148646945)
          ·
            refine ⟨4295865673835360361485209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5727820898447147148646945 4295865673835360361485209)
            ·
              refine ⟨3221899255376520271113907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4295865673835360361485209 3221899255376520271113907)
              ·
                refine ⟨4832848883064780406670861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3221899255376520271113907 4832848883064780406670861)
                ·
                  refine ⟨1812318331149292652501573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4832848883064780406670861 1812318331149292652501573)
                  ·
                    refine ⟨339809687090492372344045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1812318331149292652501573 339809687090492372344045)
                    ·
                      rfl

theorem cell23_1985331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 4].length) (baseStart_1985331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985331 prefixEnd_1985331 := by exact prefixLift 1985331
  have htrace : WordTrace (prefixWord ++ tailWord_1985331) baseStart_1985331 baseEnd_1985331 := by
    simpa [prefixWord, tailWord_1985331, baseEnd_1985331] using wordTrace_append hprefix tailTrace_1985331
  have hstable : (prefixWord ++ tailWord_1985331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985331).length < 2 ^ (prefixWord ++ tailWord_1985331).sum := by decide
  have hdescent : baseEnd_1985331 < baseStart_1985331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985347 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 6]
def baseStart_1985347 : Nat := 118140960795 + 1985347 * 2 ^ 59
def prefixEnd_1985347 : Nat := 4983230072969 + 3 ^ 40 * 1985347 * 2
def baseEnd_1985347 : Nat := 1019437276961949054432061

theorem tailTrace_1985347 : CollatzResearch.WordTrace tailWord_1985347 prefixEnd_1985347 1019437276961949054432061 := by
  unfold tailWord_1985347
  simp only [CollatzResearch.WordTrace]
  refine ⟨72411553938434364117946295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48274369292289576078630863 72411553938434364117946295)
  ·
    refine ⟨108617330907651546176919443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72411553938434364117946295 108617330907651546176919443)
    ·
      refine ⟨162925996361477319265379165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108617330907651546176919443 162925996361477319265379165)
      ·
        refine ⟨61097248635553994724517187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162925996361477319265379165 61097248635553994724517187)
        ·
          refine ⟨91645872953330992086775781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61097248635553994724517187 91645872953330992086775781)
          ·
            refine ⟨17183601178749561016270459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91645872953330992086775781 17183601178749561016270459)
            ·
              refine ⟨25775401768124341524405689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17183601178749561016270459 25775401768124341524405689)
              ·
                refine ⟨19331551326093256143304267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25775401768124341524405689 19331551326093256143304267)
                ·
                  refine ⟨28997326989139884214956401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19331551326093256143304267 28997326989139884214956401)
                  ·
                    refine ⟨21747995241854913161217301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28997326989139884214956401 21747995241854913161217301)
                    ·
                      refine ⟨1019437276961949054432061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21747995241854913161217301 1019437276961949054432061)
                      ·
                        rfl

theorem cell23_1985347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_1985347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985347 prefixEnd_1985347 := by exact prefixLift 1985347
  have htrace : WordTrace (prefixWord ++ tailWord_1985347) baseStart_1985347 baseEnd_1985347 := by
    simpa [prefixWord, tailWord_1985347, baseEnd_1985347] using wordTrace_append hprefix tailTrace_1985347
  have hstable : (prefixWord ++ tailWord_1985347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985347).length < 2 ^ (prefixWord ++ tailWord_1985347).sum := by decide
  have hdescent : baseEnd_1985347 < baseStart_1985347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985381 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 4, 3, 2]
def baseStart_1985381 : Nat := 118140960795 + 1985381 * 2 ^ 59
def prefixEnd_1985381 : Nat := 4983230072969 + 3 ^ 40 * 1985381 * 2
def baseEnd_1985381 : Nat := 1019454735304201921406905

theorem tailTrace_1985381 : CollatzResearch.WordTrace tailWord_1985381 prefixEnd_1985381 1019454735304201921406905 := by
  unfold tailWord_1985381
  simp only [CollatzResearch.WordTrace]
  refine ⟨72412794020311187924683997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48275196013540791949789331 72412794020311187924683997)
  ·
    refine ⟨27154797757616695471756499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72412794020311187924683997 27154797757616695471756499)
    ·
      refine ⟨40732196636425043207634749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27154797757616695471756499 40732196636425043207634749)
      ·
        refine ⟨15274573738659391202863031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40732196636425043207634749 15274573738659391202863031)
        ·
          refine ⟨22911860607989086804294547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15274573738659391202863031 22911860607989086804294547)
          ·
            refine ⟨34367790911983630206441821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22911860607989086804294547 34367790911983630206441821)
            ·
              refine ⟨12887921591993861327415683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34367790911983630206441821 12887921591993861327415683)
              ·
                refine ⟨19331882387990791991123525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12887921591993861327415683 19331882387990791991123525)
                ·
                  refine ⟨3624727947748273498335661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19331882387990791991123525 3624727947748273498335661)
                  ·
                    refine ⟨1359272980405602561875873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624727947748273498335661 1359272980405602561875873)
                    ·
                      refine ⟨1019454735304201921406905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1359272980405602561875873 1019454735304201921406905)
                      ·
                        rfl

theorem cell23_1985381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_1985381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985381 prefixEnd_1985381 := by exact prefixLift 1985381
  have htrace : WordTrace (prefixWord ++ tailWord_1985381) baseStart_1985381 baseEnd_1985381 := by
    simpa [prefixWord, tailWord_1985381, baseEnd_1985381] using wordTrace_append hprefix tailTrace_1985381
  have hstable : (prefixWord ++ tailWord_1985381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985381).length < 2 ^ (prefixWord ++ tailWord_1985381).sum := by decide
  have hdescent : baseEnd_1985381 < baseStart_1985381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985434 : List Nat := [3, 1, 1, 4, 3, 11]
def baseStart_1985434 : Nat := 118140960795 + 1985434 * 2 ^ 59
def prefixEnd_1985434 : Nat := 4983230072969 + 3 ^ 40 * 1985434 * 2
def baseEnd_1985434 : Nat := 4195398970283498823227

theorem tailTrace_1985434 : CollatzResearch.WordTrace tailWord_1985434 prefixEnd_1985434 4195398970283498823227 := by
  unfold tailWord_1985434
  simp only [CollatzResearch.WordTrace]
  refine ⟨18103681772279794494090839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48276484726079451984242237 18103681772279794494090839)
  ·
    refine ⟨27155522658419691741136259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18103681772279794494090839 27155522658419691741136259)
    ·
      refine ⟨40733283987629537611704389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27155522658419691741136259 40733283987629537611704389)
      ·
        refine ⟨7637490747680538302194573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40733283987629537611704389 7637490747680538302194573)
        ·
          refine ⟨2864059030380201863322965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7637490747680538302194573 2864059030380201863322965)
          ·
            refine ⟨4195398970283498823227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2864059030380201863322965 4195398970283498823227)
            ·
              rfl

theorem cell23_1985434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 11].length) (baseStart_1985434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985434 prefixEnd_1985434 := by exact prefixLift 1985434
  have htrace : WordTrace (prefixWord ++ tailWord_1985434) baseStart_1985434 baseEnd_1985434 := by
    simpa [prefixWord, tailWord_1985434, baseEnd_1985434] using wordTrace_append hprefix tailTrace_1985434
  have hstable : (prefixWord ++ tailWord_1985434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985434).length < 2 ^ (prefixWord ++ tailWord_1985434).sum := by decide
  have hdescent : baseEnd_1985434 < baseStart_1985434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985485 : List Nat := [1, 6, 3, 1, 1, 1, 10]
def baseStart_1985485 : Nat := 118140960795 + 1985485 * 2 ^ 59
def prefixEnd_1985485 : Nat := 4983230072969 + 3 ^ 40 * 1985485 * 2
def baseEnd_1985485 : Nat := 12586520213484808821067

theorem tailTrace_1985485 : CollatzResearch.WordTrace tailWord_1985485 prefixEnd_1985485 12586520213484808821067 := by
  unfold tailWord_1985485
  simp only [CollatzResearch.WordTrace]
  refine ⟨72416587211934413686469909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48277724807956275790979939 72416587211934413686469909)
  ·
    refine ⟨3394527525559425641553277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72416587211934413686469909 3394527525559425641553277)
    ·
      refine ⟨1272947822084784615582479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3394527525559425641553277 1272947822084784615582479)
      ·
        refine ⟨1909421733127176923373719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272947822084784615582479 1909421733127176923373719)
        ·
          refine ⟨2864132599690765385060579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909421733127176923373719 2864132599690765385060579)
          ·
            refine ⟨4296198899536148077590869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864132599690765385060579 4296198899536148077590869)
            ·
              refine ⟨12586520213484808821067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4296198899536148077590869 12586520213484808821067)
              ·
                rfl

theorem cell23_1985485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 10].length) (baseStart_1985485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985485 prefixEnd_1985485 := by exact prefixLift 1985485
  have htrace : WordTrace (prefixWord ++ tailWord_1985485) baseStart_1985485 baseEnd_1985485 := by
    simpa [prefixWord, tailWord_1985485, baseEnd_1985485] using wordTrace_append hprefix tailTrace_1985485
  have hstable : (prefixWord ++ tailWord_1985485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985485).length < 2 ^ (prefixWord ++ tailWord_1985485).sum := by decide
  have hdescent : baseEnd_1985485 < baseStart_1985485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985504 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 5]
def baseStart_1985504 : Nat := 118140960795 + 1985504 * 2 ^ 59
def prefixEnd_1985504 : Nat := 4983230072969 + 3 ^ 40 * 1985504 * 2
def baseEnd_1985504 : Nat := 1019517893424704940168839

theorem tailTrace_1985504 : CollatzResearch.WordTrace tailWord_1985504 prefixEnd_1985504 1019517893424704940168839 := by
  unfold tailWord_1985504
  simp only [CollatzResearch.WordTrace]
  refine ⟨36208640099432789965705783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48278186799243719954274377 36208640099432789965705783)
  ·
    refine ⟨54312960149149184948558675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36208640099432789965705783 54312960149149184948558675)
    ·
      refine ⟨81469440223723777422838013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54312960149149184948558675 81469440223723777422838013)
      ·
        refine ⟨30551040083896416533564255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81469440223723777422838013 30551040083896416533564255)
        ·
          refine ⟨45826560125844624800346383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30551040083896416533564255 45826560125844624800346383)
          ·
            refine ⟨68739840188766937200519575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45826560125844624800346383 68739840188766937200519575)
            ·
              refine ⟨103109760283150405800779363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68739840188766937200519575 103109760283150405800779363)
              ·
                refine ⟨154664640424725608701169045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103109760283150405800779363 154664640424725608701169045)
                ·
                  refine ⟨7249905019909012907867299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154664640424725608701169045 7249905019909012907867299)
                  ·
                    refine ⟨10874857529863519361800949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7249905019909012907867299 10874857529863519361800949)
                    ·
                      refine ⟨1019517893424704940168839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10874857529863519361800949 1019517893424704940168839)
                      ·
                        rfl

theorem cell23_1985504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_1985504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985504 prefixEnd_1985504 := by exact prefixLift 1985504
  have htrace : WordTrace (prefixWord ++ tailWord_1985504) baseStart_1985504 baseEnd_1985504 := by
    simpa [prefixWord, tailWord_1985504, baseEnd_1985504] using wordTrace_append hprefix tailTrace_1985504
  have hstable : (prefixWord ++ tailWord_1985504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985504).length < 2 ^ (prefixWord ++ tailWord_1985504).sum := by decide
  have hdescent : baseEnd_1985504 < baseStart_1985504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985511 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 2, 6]
def baseStart_1985511 : Nat := 118140960795 + 1985511 * 2 ^ 59
def prefixEnd_1985511 : Nat := 4983230072969 + 3 ^ 40 * 1985511 * 2
def baseEnd_1985511 : Nat := 339840495929762137593769

theorem tailTrace_1985511 : CollatzResearch.WordTrace tailWord_1985511 prefixEnd_1985511 339840495929762137593769 := by
  unfold tailWord_1985511
  simp only [CollatzResearch.WordTrace]
  refine ⟨72417535509840220126916387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48278357006560146751277591 72417535509840220126916387)
  ·
    refine ⟨108626303264760330190374581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72417535509840220126916387 108626303264760330190374581)
    ·
      refine ⟨10183715931071280955347617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108626303264760330190374581 10183715931071280955347617)
      ·
        refine ⟨7637786948303460716510713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10183715931071280955347617 7637786948303460716510713)
        ·
          refine ⟨5728340211227595537383035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7637786948303460716510713 5728340211227595537383035)
          ·
            refine ⟨8592510316841393306074553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728340211227595537383035 8592510316841393306074553)
            ·
              refine ⟨6444382737631044979555915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8592510316841393306074553 6444382737631044979555915)
              ·
                refine ⟨9666574106446567469333873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444382737631044979555915 9666574106446567469333873)
                ·
                  refine ⟨7249930579834925602000405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9666574106446567469333873 7249930579834925602000405)
                  ·
                    refine ⟨339840495929762137593769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7249930579834925602000405 339840495929762137593769)
                    ·
                      rfl

theorem cell23_1985511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_1985511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985511 prefixEnd_1985511 := by exact prefixLift 1985511
  have htrace : WordTrace (prefixWord ++ tailWord_1985511) baseStart_1985511 baseEnd_1985511 := by
    simpa [prefixWord, tailWord_1985511, baseEnd_1985511] using wordTrace_append hprefix tailTrace_1985511
  have hstable : (prefixWord ++ tailWord_1985511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985511).length < 2 ^ (prefixWord ++ tailWord_1985511).sum := by decide
  have hdescent : baseEnd_1985511 < baseStart_1985511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985569 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 2, 2, 2]
def baseStart_1985569 : Nat := 118140960795 + 1985569 * 2 ^ 59
def prefixEnd_1985569 : Nat := 4983230072969 + 3 ^ 40 * 1985569 * 2
def baseEnd_1985569 : Nat := 1019551269667247185856041

theorem tailTrace_1985569 : CollatzResearch.WordTrace tailWord_1985569 prefixEnd_1985569 1019551269667247185856041 := by
  unfold tailWord_1985569
  simp only [CollatzResearch.WordTrace]
  refine ⟨72419650943630096032527761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48279767295753397355018507 72419650943630096032527761)
  ·
    refine ⟨54314738207722572024395821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72419650943630096032527761 54314738207722572024395821)
    ·
      refine ⟨20368026827895964509148433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54314738207722572024395821 20368026827895964509148433)
      ·
        refine ⟨15276020120921973381861325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20368026827895964509148433 15276020120921973381861325)
        ·
          refine ⟨5728507545345740018197997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15276020120921973381861325 5728507545345740018197997)
          ·
            refine ⟨2148190329504652506824249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5728507545345740018197997 2148190329504652506824249)
            ·
              refine ⟨1611142747128489380118187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148190329504652506824249 1611142747128489380118187)
              ·
                refine ⟨2416714120692734070177281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611142747128489380118187 2416714120692734070177281)
                ·
                  refine ⟨1812535590519550552632961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2416714120692734070177281 1812535590519550552632961)
                  ·
                    refine ⟨1359401692889662914474721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1812535590519550552632961 1359401692889662914474721)
                    ·
                      refine ⟨1019551269667247185856041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1359401692889662914474721 1019551269667247185856041)
                      ·
                        rfl

theorem cell23_1985569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_1985569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985569 prefixEnd_1985569 := by exact prefixLift 1985569
  have htrace : WordTrace (prefixWord ++ tailWord_1985569) baseStart_1985569 baseEnd_1985569 := by
    simpa [prefixWord, tailWord_1985569, baseEnd_1985569] using wordTrace_append hprefix tailTrace_1985569
  have hstable : (prefixWord ++ tailWord_1985569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985569).length < 2 ^ (prefixWord ++ tailWord_1985569).sum := by decide
  have hdescent : baseEnd_1985569 < baseStart_1985569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985598 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1985598 : Nat := 118140960795 + 1985598 * 2 ^ 59
def prefixEnd_1985598 : Nat := 4983230072969 + 3 ^ 40 * 1985598 * 2
def baseEnd_1985598 : Nat := 1019566160606227572393407

theorem tailTrace_1985598 : CollatzResearch.WordTrace tailWord_1985598 prefixEnd_1985598 1019566160606227572393407 := by
  unfold tailWord_1985598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9052588582565629248166681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48280472440350022656888965 9052588582565629248166681)
  ·
    refine ⟨6789441436924221936125011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9052588582565629248166681 6789441436924221936125011)
    ·
      refine ⟨10184162155386332904187517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6789441436924221936125011 10184162155386332904187517)
      ·
        refine ⟨3819060808269874839070319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10184162155386332904187517 3819060808269874839070319)
        ·
          refine ⟨5728591212404812258605479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819060808269874839070319 5728591212404812258605479)
          ·
            refine ⟨8592886818607218387908219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728591212404812258605479 8592886818607218387908219)
            ·
              refine ⟨12889330227910827581862329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8592886818607218387908219 12889330227910827581862329)
              ·
                refine ⟨9666997670933120686396747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12889330227910827581862329 9666997670933120686396747)
                ·
                  refine ⟨14500496506399681029595121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9666997670933120686396747 14500496506399681029595121)
                  ·
                    refine ⟨10875372379799760772196341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14500496506399681029595121 10875372379799760772196341)
                    ·
                      refine ⟨1019566160606227572393407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10875372379799760772196341 1019566160606227572393407)
                      ·
                        rfl

theorem cell23_1985598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1985598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985598 prefixEnd_1985598 := by exact prefixLift 1985598
  have htrace : WordTrace (prefixWord ++ tailWord_1985598) baseStart_1985598 baseEnd_1985598 := by
    simpa [prefixWord, tailWord_1985598, baseEnd_1985598] using wordTrace_append hprefix tailTrace_1985598
  have hstable : (prefixWord ++ tailWord_1985598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985598).length < 2 ^ (prefixWord ++ tailWord_1985598).sum := by decide
  have hdescent : baseEnd_1985598 < baseStart_1985598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985608 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 2, 4, 2]
def baseStart_1985608 : Nat := 118140960795 + 1985608 * 2 ^ 59
def prefixEnd_1985608 : Nat := 4983230072969 + 3 ^ 40 * 1985608 * 2
def baseEnd_1985608 : Nat := 1019571295412772533268361

theorem tailTrace_1985608 : CollatzResearch.WordTrace tailWord_1985608 prefixEnd_1985608 1019571295412772533268361 := by
  unfold tailWord_1985608
  simp only [CollatzResearch.WordTrace]
  refine ⟨36210536695244402846598739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48280715593659203795464985 36210536695244402846598739)
  ·
    refine ⟨54315805042866604269898109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36210536695244402846598739 54315805042866604269898109)
    ·
      refine ⟨20368426891074976601211791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54315805042866604269898109 20368426891074976601211791)
      ·
        refine ⟨30552640336612464901817687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20368426891074976601211791 30552640336612464901817687)
        ·
          refine ⟨45828960504918697352726531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30552640336612464901817687 45828960504918697352726531)
          ·
            refine ⟨68743440757378046029089797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45828960504918697352726531 68743440757378046029089797)
            ·
              refine ⟨12889395142008383630454337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68743440757378046029089797 12889395142008383630454337)
              ·
                refine ⟨9667046356506287722840753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12889395142008383630454337 9667046356506287722840753)
                ·
                  refine ⟨7250284767379715792130565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9667046356506287722840753 7250284767379715792130565)
                  ·
                    refine ⟨1359428393883696711024481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7250284767379715792130565 1359428393883696711024481)
                    ·
                      refine ⟨1019571295412772533268361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1359428393883696711024481 1019571295412772533268361)
                      ·
                        rfl

theorem cell23_1985608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_1985608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985608 prefixEnd_1985608 := by exact prefixLift 1985608
  have htrace : WordTrace (prefixWord ++ tailWord_1985608) baseStart_1985608 baseEnd_1985608 := by
    simpa [prefixWord, tailWord_1985608, baseEnd_1985608] using wordTrace_append hprefix tailTrace_1985608
  have hstable : (prefixWord ++ tailWord_1985608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985608).length < 2 ^ (prefixWord ++ tailWord_1985608).sum := by decide
  have hdescent : baseEnd_1985608 < baseStart_1985608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985628 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1985628 : Nat := 118140960795 + 1985628 * 2 ^ 59
def prefixEnd_1985628 : Nat := 4983230072969 + 3 ^ 40 * 1985628 * 2
def baseEnd_1985628 : Nat := 1019581565025862455018269

theorem tailTrace_1985628 : CollatzResearch.WordTrace tailWord_1985628 prefixEnd_1985628 1019581565025862455018269 := by
  unfold tailWord_1985628
  simp only [CollatzResearch.WordTrace]
  refine ⟨36210901425208174554462769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48281201900277566072617025 36210901425208174554462769)
  ·
    refine ⟨27158176068906130915847077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36210901425208174554462769 27158176068906130915847077)
    ·
      refine ⟨5092158012919899546721327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27158176068906130915847077 5092158012919899546721327)
      ·
        refine ⟨7638237019379849320081991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092158012919899546721327 7638237019379849320081991)
        ·
          refine ⟨11457355529069773980122987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7638237019379849320081991 11457355529069773980122987)
          ·
            refine ⟨17186033293604660970184481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11457355529069773980122987 17186033293604660970184481)
            ·
              refine ⟨12889524970203495727638361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17186033293604660970184481 12889524970203495727638361)
              ·
                refine ⟨9667143727652621795728771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12889524970203495727638361 9667143727652621795728771)
                ·
                  refine ⟨14500715591478932693593157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9667143727652621795728771 14500715591478932693593157)
                  ·
                    refine ⟨2718884173402299880048717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14500715591478932693593157 2718884173402299880048717)
                    ·
                      refine ⟨1019581565025862455018269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2718884173402299880048717 1019581565025862455018269)
                      ·
                        rfl

theorem cell23_1985628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1985628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985628 prefixEnd_1985628 := by exact prefixLift 1985628
  have htrace : WordTrace (prefixWord ++ tailWord_1985628) baseStart_1985628 baseEnd_1985628 := by
    simpa [prefixWord, tailWord_1985628, baseEnd_1985628] using wordTrace_append hprefix tailTrace_1985628
  have hstable : (prefixWord ++ tailWord_1985628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985628).length < 2 ^ (prefixWord ++ tailWord_1985628).sum := by decide
  have hdescent : baseEnd_1985628 < baseStart_1985628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985631 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 6]
def baseStart_1985631 : Nat := 118140960795 + 1985631 * 2 ^ 59
def prefixEnd_1985631 : Nat := 4983230072969 + 3 ^ 40 * 1985631 * 2
def baseEnd_1985631 : Nat := 113287011718647327031195

theorem tailTrace_1985631 : CollatzResearch.WordTrace tailWord_1985631 prefixEnd_1985631 113287011718647327031195 := by
  unfold tailWord_1985631
  simp only [CollatzResearch.WordTrace]
  refine ⟨72421912269405480621284747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48281274846270320414189831 72421912269405480621284747)
  ·
    refine ⟨108632868404108220931927121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72421912269405480621284747 108632868404108220931927121)
    ·
      refine ⟨81474651303081165698945341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108632868404108220931927121 81474651303081165698945341)
      ·
        refine ⟨30552994238655437137104503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81474651303081165698945341 30552994238655437137104503)
        ·
          refine ⟨45829491357983155705656755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30552994238655437137104503 45829491357983155705656755)
          ·
            refine ⟨68744237036974733558485133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45829491357983155705656755 68744237036974733558485133)
            ·
              refine ⟨25779088888865525084431925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68744237036974733558485133 25779088888865525084431925)
              ·
                refine ⟨2416789583331142976665493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25779088888865525084431925 2416789583331142976665493)
                ·
                  refine ⟨113287011718647327031195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2416789583331142976665493 113287011718647327031195)
                  ·
                    rfl

theorem cell23_1985631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 6].length) (baseStart_1985631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985631 prefixEnd_1985631 := by exact prefixLift 1985631
  have htrace : WordTrace (prefixWord ++ tailWord_1985631) baseStart_1985631 baseEnd_1985631 := by
    simpa [prefixWord, tailWord_1985631, baseEnd_1985631] using wordTrace_append hprefix tailTrace_1985631
  have hstable : (prefixWord ++ tailWord_1985631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985631).length < 2 ^ (prefixWord ++ tailWord_1985631).sum := by decide
  have hdescent : baseEnd_1985631 < baseStart_1985631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985645 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_1985645 : Nat := 118140960795 + 1985645 * 2 ^ 59
def prefixEnd_1985645 : Nat := 4983230072969 + 3 ^ 40 * 1985645 * 2
def baseEnd_1985645 : Nat := 1019590294196988888505691

theorem tailTrace_1985645 : CollatzResearch.WordTrace tailWord_1985645 prefixEnd_1985645 1019590294196988888505691 := by
  unfold tailWord_1985645
  simp only [CollatzResearch.WordTrace]
  refine ⟨72422422891354761012294389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48281615260903174008196259 72422422891354761012294389)
  ·
    refine ⟨6789602146064508844902599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72422422891354761012294389 6789602146064508844902599)
    ·
      refine ⟨10184403219096763267353899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6789602146064508844902599 10184403219096763267353899)
      ·
        refine ⟨15276604828645144901030849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10184403219096763267353899 15276604828645144901030849)
        ·
          refine ⟨11457453621483858675773137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15276604828645144901030849 11457453621483858675773137)
          ·
            refine ⟨8593090216112894006829853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11457453621483858675773137 8593090216112894006829853)
            ·
              refine ⟨3222408831042335252561195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8593090216112894006829853 3222408831042335252561195)
              ·
                refine ⟨4833613246563502878841793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222408831042335252561195 4833613246563502878841793)
                ·
                  refine ⟨3625209934922627159131345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4833613246563502878841793 3625209934922627159131345)
                  ·
                    refine ⟨2718907451191970369348509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3625209934922627159131345 2718907451191970369348509)
                    ·
                      refine ⟨1019590294196988888505691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2718907451191970369348509 1019590294196988888505691)
                      ·
                        rfl

theorem cell23_1985645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_1985645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985645 prefixEnd_1985645 := by exact prefixLift 1985645
  have htrace : WordTrace (prefixWord ++ tailWord_1985645) baseStart_1985645 baseEnd_1985645 := by
    simpa [prefixWord, tailWord_1985645, baseEnd_1985645] using wordTrace_append hprefix tailTrace_1985645
  have hstable : (prefixWord ++ tailWord_1985645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985645).length < 2 ^ (prefixWord ++ tailWord_1985645).sum := by decide
  have hdescent : baseEnd_1985645 < baseStart_1985645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985665 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 6]
def baseStart_1985665 : Nat := 118140960795 + 1985665 * 2 ^ 59
def prefixEnd_1985665 : Nat := 4983230072969 + 3 ^ 40 * 1985665 * 2
def baseEnd_1985665 : Nat := 113288951534453201139511

theorem tailTrace_1985665 : CollatzResearch.WordTrace tailWord_1985665 prefixEnd_1985665 113288951534453201139511 := by
  unfold tailWord_1985665
  simp only [CollatzResearch.WordTrace]
  refine ⟨72423152351282304428022449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48282101567521536285348299 72423152351282304428022449)
  ·
    refine ⟨54317364263461728321016837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72423152351282304428022449 54317364263461728321016837)
    ·
      refine ⟨10184505799399074060190657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54317364263461728321016837 10184505799399074060190657)
      ·
        refine ⟨7638379349549305545142993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10184505799399074060190657 7638379349549305545142993)
        ·
          refine ⟨5728784512161979158857245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7638379349549305545142993 5728784512161979158857245)
          ·
            refine ⟨2148294192060742184571467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5728784512161979158857245 2148294192060742184571467)
            ·
              refine ⟨3222441288091113276857201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148294192060742184571467 3222441288091113276857201)
              ·
                refine ⟨2416830966068334957642901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3222441288091113276857201 2416830966068334957642901)
                ·
                  refine ⟨113288951534453201139511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2416830966068334957642901 113288951534453201139511)
                  ·
                    rfl

theorem cell23_1985665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 6].length) (baseStart_1985665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985665 prefixEnd_1985665 := by exact prefixLift 1985665
  have htrace : WordTrace (prefixWord ++ tailWord_1985665) baseStart_1985665 baseEnd_1985665 := by
    simpa [prefixWord, tailWord_1985665, baseEnd_1985665] using wordTrace_append hprefix tailTrace_1985665
  have hstable : (prefixWord ++ tailWord_1985665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985665).length < 2 ^ (prefixWord ++ tailWord_1985665).sum := by decide
  have hdescent : baseEnd_1985665 < baseStart_1985665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985715 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 5, 2, 2]
def baseStart_1985715 : Nat := 118140960795 + 1985715 * 2 ^ 59
def prefixEnd_1985715 : Nat := 4983230072969 + 3 ^ 40 * 1985715 * 2
def baseEnd_1985715 : Nat := 1019626237842803614630369

theorem tailTrace_1985715 : CollatzResearch.WordTrace tailWord_1985715 prefixEnd_1985715 1019626237842803614630369 := by
  unfold tailWord_1985715
  simp only [CollatzResearch.WordTrace]
  refine ⟨72424976001101162967342599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48283317334067441978228399 72424976001101162967342599)
  ·
    refine ⟨108637464001651744451013899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72424976001101162967342599 108637464001651744451013899)
    ·
      refine ⟨162956196002477616676520849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108637464001651744451013899 162956196002477616676520849)
      ·
        refine ⟨122217147001858212507390637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162956196002477616676520849 122217147001858212507390637)
        ·
          refine ⟨45831430125696829690271489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122217147001858212507390637 45831430125696829690271489)
          ·
            refine ⟨34373572594272622267703617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45831430125696829690271489 34373572594272622267703617)
            ·
              refine ⟨25780179445704466700777713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34373572594272622267703617 25780179445704466700777713)
              ·
                refine ⟨19335134584278350025583285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25780179445704466700777713 19335134584278350025583285)
                ·
                  refine ⟨1812668867276095314898433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19335134584278350025583285 1812668867276095314898433)
                  ·
                    refine ⟨1359501650457071486173825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1812668867276095314898433 1359501650457071486173825)
                    ·
                      refine ⟨1019626237842803614630369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1359501650457071486173825 1019626237842803614630369)
                      ·
                        rfl

theorem cell23_1985715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 2, 2].length) (baseStart_1985715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985715 prefixEnd_1985715 := by exact prefixLift 1985715
  have htrace : WordTrace (prefixWord ++ tailWord_1985715) baseStart_1985715 baseEnd_1985715 := by
    simpa [prefixWord, tailWord_1985715, baseEnd_1985715] using wordTrace_append hprefix tailTrace_1985715
  have hstable : (prefixWord ++ tailWord_1985715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985715).length < 2 ^ (prefixWord ++ tailWord_1985715).sum := by decide
  have hdescent : baseEnd_1985715 < baseStart_1985715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985721 : List Nat := [1, 2, 1, 4, 1, 3, 11]
def baseStart_1985721 : Nat := 118140960795 + 1985721 * 2 ^ 59
def prefixEnd_1985721 : Nat := 4983230072969 + 3 ^ 40 * 1985721 * 2
def baseEnd_1985721 : Nat := 12588016280576920878461

theorem tailTrace_1985721 : CollatzResearch.WordTrace tailWord_1985721 prefixEnd_1985721 12588016280576920878461 := by
  unfold tailWord_1985721
  simp only [CollatzResearch.WordTrace]
  refine ⟨72425194839079425992061017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48283463226052950661374011 72425194839079425992061017)
  ·
    refine ⟨54318896129309569494045763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72425194839079425992061017 54318896129309569494045763)
    ·
      refine ⟨81478344193964354241068645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54318896129309569494045763 81478344193964354241068645)
      ·
        refine ⟨15277189536368316420200371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81478344193964354241068645 15277189536368316420200371)
        ·
          refine ⟨22915784304552474630300557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15277189536368316420200371 22915784304552474630300557)
          ·
            refine ⟨8593419114207177986362709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22915784304552474630300557 8593419114207177986362709)
            ·
              refine ⟨12588016280576920878461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8593419114207177986362709 12588016280576920878461)
              ·
                rfl

theorem cell23_1985721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 11].length) (baseStart_1985721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985721 prefixEnd_1985721 := by exact prefixLift 1985721
  have htrace : WordTrace (prefixWord ++ tailWord_1985721) baseStart_1985721 baseEnd_1985721 := by
    simpa [prefixWord, tailWord_1985721, baseEnd_1985721] using wordTrace_append hprefix tailTrace_1985721
  have hstable : (prefixWord ++ tailWord_1985721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985721).length < 2 ^ (prefixWord ++ tailWord_1985721).sum := by decide
  have hdescent : baseEnd_1985721 < baseStart_1985721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985726 : List Nat := [4, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_1985726 : Nat := 118140960795 + 1985726 * 2 ^ 59
def prefixEnd_1985726 : Nat := 4983230072969 + 3 ^ 40 * 1985726 * 2
def baseEnd_1985726 : Nat := 1019631886130003071592819

theorem tailTrace_1985726 : CollatzResearch.WordTrace tailWord_1985726 prefixEnd_1985726 1019631886130003071592819 := by
  unfold tailWord_1985726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053172150507663980749129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48283584802707541230662021 9053172150507663980749129)
  ·
    refine ⟨6789879112880747985561847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9053172150507663980749129 6789879112880747985561847)
    ·
      refine ⟨10184818669321121978342771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6789879112880747985561847 10184818669321121978342771)
      ·
        refine ⟨15277228003981682967514157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10184818669321121978342771 15277228003981682967514157)
        ·
          refine ⟨5728960501493131112817809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15277228003981682967514157 5728960501493131112817809)
          ·
            refine ⟨4296720376119848334613357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5728960501493131112817809 4296720376119848334613357)
            ·
              refine ⟨1611270141044943125480009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4296720376119848334613357 1611270141044943125480009)
              ·
                refine ⟨1208452605783707344110007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611270141044943125480009 1208452605783707344110007)
                ·
                  refine ⟨1812678908675561016165011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208452605783707344110007 1812678908675561016165011)
                  ·
                    refine ⟨2719018363013341524247517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1812678908675561016165011 2719018363013341524247517)
                    ·
                      refine ⟨1019631886130003071592819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2719018363013341524247517 1019631886130003071592819)
                      ·
                        rfl

theorem cell23_1985726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_1985726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985726 prefixEnd_1985726 := by exact prefixLift 1985726
  have htrace : WordTrace (prefixWord ++ tailWord_1985726) baseStart_1985726 baseEnd_1985726 := by
    simpa [prefixWord, tailWord_1985726, baseEnd_1985726] using wordTrace_append hprefix tailTrace_1985726
  have hstable : (prefixWord ++ tailWord_1985726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985726).length < 2 ^ (prefixWord ++ tailWord_1985726).sum := by decide
  have hdescent : baseEnd_1985726 < baseStart_1985726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985738 : List Nat := [3, 1, 2, 1, 3, 3, 2, 8]
def baseStart_1985738 : Nat := 118140960795 + 1985738 * 2 ^ 59
def prefixEnd_1985738 : Nat := 4983230072969 + 3 ^ 40 * 1985738 * 2
def baseEnd_1985738 : Nat := 37764372144365074986769

theorem tailTrace_1985738 : CollatzResearch.WordTrace tailWord_1985738 prefixEnd_1985738 37764372144365074986769 := by
  unfold tailWord_1985738
  simp only [CollatzResearch.WordTrace]
  refine ⟨18106453720004459473857467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48283876586678558596953245 18106453720004459473857467)
  ·
    refine ⟨27159680580006689210786201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18106453720004459473857467 27159680580006689210786201)
    ·
      refine ⟨20369760435005016908089651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27159680580006689210786201 20369760435005016908089651)
      ·
        refine ⟨30554640652507525362134477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20369760435005016908089651 30554640652507525362134477)
        ·
          refine ⟨11457990244690322010800429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30554640652507525362134477 11457990244690322010800429)
          ·
            refine ⟨4296746341758870754050161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11457990244690322010800429 4296746341758870754050161)
            ·
              refine ⟨3222559756319153065537621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4296746341758870754050161 3222559756319153065537621)
              ·
                refine ⟨37764372144365074986769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3222559756319153065537621 37764372144365074986769)
                ·
                  rfl

theorem cell23_1985738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 8].length) (baseStart_1985738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985738 prefixEnd_1985738 := by exact prefixLift 1985738
  have htrace : WordTrace (prefixWord ++ tailWord_1985738) baseStart_1985738 baseEnd_1985738 := by
    simpa [prefixWord, tailWord_1985738, baseEnd_1985738] using wordTrace_append hprefix tailTrace_1985738
  have hstable : (prefixWord ++ tailWord_1985738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985738).length < 2 ^ (prefixWord ++ tailWord_1985738).sum := by decide
  have hdescent : baseEnd_1985738 < baseStart_1985738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985742 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_1985742 : Nat := 118140960795 + 1985742 * 2 ^ 59
def prefixEnd_1985742 : Nat := 4983230072969 + 3 ^ 40 * 1985742 * 2
def baseEnd_1985742 : Nat := 339880033940158336330915

theorem tailTrace_1985742 : CollatzResearch.WordTrace tailWord_1985742 prefixEnd_1985742 339880033940158336330915 := by
  unfold tailWord_1985742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053245096500418322321935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48283973848002231052383653 9053245096500418322321935)
  ·
    refine ⟨13579867644750627483482903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9053245096500418322321935 13579867644750627483482903)
    ·
      refine ⟨20369801467125941225224355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13579867644750627483482903 20369801467125941225224355)
      ·
        refine ⟨30554702200688911837836533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20369801467125941225224355 30554702200688911837836533)
        ·
          refine ⟨2864503331314585484797175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30554702200688911837836533 2864503331314585484797175)
          ·
            refine ⟨4296754996971878227195763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864503331314585484797175 4296754996971878227195763)
            ·
              refine ⟨6445132495457817340793645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296754996971878227195763 6445132495457817340793645)
              ·
                refine ⟨2416924685796681502797617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6445132495457817340793645 2416924685796681502797617)
                ·
                  refine ⟨1812693514347511127098213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2416924685796681502797617 1812693514347511127098213)
                  ·
                    refine ⟨339880033940158336330915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1812693514347511127098213 339880033940158336330915)
                    ·
                      rfl

theorem cell23_1985742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_1985742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985742 prefixEnd_1985742 := by exact prefixLift 1985742
  have htrace : WordTrace (prefixWord ++ tailWord_1985742) baseStart_1985742 baseEnd_1985742 := by
    simpa [prefixWord, tailWord_1985742, baseEnd_1985742] using wordTrace_append hprefix tailTrace_1985742
  have hstable : (prefixWord ++ tailWord_1985742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985742).length < 2 ^ (prefixWord ++ tailWord_1985742).sum := by decide
  have hdescent : baseEnd_1985742 < baseStart_1985742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985828 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 9]
def baseStart_1985828 : Nat := 118140960795 + 1985828 * 2 ^ 59
def prefixEnd_1985828 : Nat := 4983230072969 + 3 ^ 40 * 1985828 * 2
def baseEnd_1985828 : Nat := 113298251239640185835261

theorem tailTrace_1985828 : CollatzResearch.WordTrace tailWord_1985828 prefixEnd_1985828 113298251239640185835261 := by
  unfold tailWord_1985828
  simp only [CollatzResearch.WordTrace]
  refine ⟨36214548724845891633103069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48286064966461188844137425 36214548724845891633103069)
  ·
    refine ⟨13580455771817209362413651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36214548724845891633103069 13580455771817209362413651)
    ·
      refine ⟨20370683657725814043620477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13580455771817209362413651 20370683657725814043620477)
      ·
        refine ⟨7639006371647180266357679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20370683657725814043620477 7639006371647180266357679)
        ·
          refine ⟨11458509557470770399536519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7639006371647180266357679 11458509557470770399536519)
          ·
            refine ⟨17187764336206155599304779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11458509557470770399536519 17187764336206155599304779)
            ·
              refine ⟨25781646504309233398957169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17187764336206155599304779 25781646504309233398957169)
              ·
                refine ⟨19336234878231925049217877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25781646504309233398957169 19336234878231925049217877)
                ·
                  refine ⟨113298251239640185835261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19336234878231925049217877 113298251239640185835261)
                  ·
                    rfl

theorem cell23_1985828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_1985828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985828 prefixEnd_1985828 := by exact prefixLift 1985828
  have htrace : WordTrace (prefixWord ++ tailWord_1985828) baseStart_1985828 baseEnd_1985828 := by
    simpa [prefixWord, tailWord_1985828, baseEnd_1985828] using wordTrace_append hprefix tailTrace_1985828
  have hstable : (prefixWord ++ tailWord_1985828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985828).length < 2 ^ (prefixWord ++ tailWord_1985828).sum := by decide
  have hdescent : baseEnd_1985828 < baseStart_1985828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985845 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 7]
def baseStart_1985845 : Nat := 118140960795 + 1985845 * 2 ^ 59
def prefixEnd_1985845 : Nat := 4983230072969 + 3 ^ 40 * 1985845 * 2
def baseEnd_1985845 : Nat := 113299221147543122889419

theorem tailTrace_1985845 : CollatzResearch.WordTrace tailWord_1985845 prefixEnd_1985845 113299221147543122889419 := by
  unfold tailWord_1985845
  simp only [CollatzResearch.WordTrace]
  refine ⟨72429717490630195169574989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48286478327086796779716659 72429717490630195169574989)
  ·
    refine ⟨27161144058986323188590621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72429717490630195169574989 27161144058986323188590621)
    ·
      refine ⟨10185429022119871195721483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27161144058986323188590621 10185429022119871195721483)
      ·
        refine ⟨15278143533179806793582225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10185429022119871195721483 15278143533179806793582225)
        ·
          refine ⟨11458607649884855095186669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15278143533179806793582225 11458607649884855095186669)
          ·
            refine ⟨4296977868706820660695001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11458607649884855095186669 4296977868706820660695001)
            ·
              refine ⟨3222733401530115495521251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4296977868706820660695001 3222733401530115495521251)
              ·
                refine ⟨4834100102295173243281877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222733401530115495521251 4834100102295173243281877)
                ·
                  refine ⟨113299221147543122889419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4834100102295173243281877 113299221147543122889419)
                  ·
                    rfl

theorem cell23_1985845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_1985845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985845 prefixEnd_1985845 := by exact prefixLift 1985845
  have htrace : WordTrace (prefixWord ++ tailWord_1985845) baseStart_1985845 baseEnd_1985845 := by
    simpa [prefixWord, tailWord_1985845, baseEnd_1985845] using wordTrace_append hprefix tailTrace_1985845
  have hstable : (prefixWord ++ tailWord_1985845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985845).length < 2 ^ (prefixWord ++ tailWord_1985845).sum := by decide
  have hdescent : baseEnd_1985845 < baseStart_1985845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985855 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 3]
def baseStart_1985855 : Nat := 118140960795 + 1985855 * 2 ^ 59
def prefixEnd_1985855 : Nat := 4983230072969 + 3 ^ 40 * 1985855 * 2
def baseEnd_1985855 : Nat := 1019698125134433066879725

theorem tailTrace_1985855 : CollatzResearch.WordTrace tailWord_1985855 prefixEnd_1985855 1019698125134433066879725 := by
  unfold tailWord_1985855
  simp only [CollatzResearch.WordTrace]
  refine ⟨72430082220593966877439019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48286721480395977918292679 72430082220593966877439019)
  ·
    refine ⟨108645123330890950316158529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72430082220593966877439019 108645123330890950316158529)
    ·
      refine ⟨81483842498168212737118897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108645123330890950316158529 81483842498168212737118897)
      ·
        refine ⟨61112881873626159552839173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81483842498168212737118897 61112881873626159552839173)
        ·
          refine ⟨11458665351304904916157345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61112881873626159552839173 11458665351304904916157345)
          ·
            refine ⟨8593999013478678687118009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11458665351304904916157345 8593999013478678687118009)
            ·
              refine ⟨6445499260109009015338507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8593999013478678687118009 6445499260109009015338507)
              ·
                refine ⟨9668248890163513523007761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445499260109009015338507 9668248890163513523007761)
                ·
                  refine ⟨7251186667622635142255821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9668248890163513523007761 7251186667622635142255821)
                  ·
                    refine ⟨2719195000358488178345933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7251186667622635142255821 2719195000358488178345933)
                    ·
                      refine ⟨1019698125134433066879725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2719195000358488178345933 1019698125134433066879725)
                      ·
                        rfl

theorem cell23_1985855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_1985855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985855 prefixEnd_1985855 := by exact prefixLift 1985855
  have htrace : WordTrace (prefixWord ++ tailWord_1985855) baseStart_1985855 baseEnd_1985855 := by
    simpa [prefixWord, tailWord_1985855, baseEnd_1985855] using wordTrace_append hprefix tailTrace_1985855
  have hstable : (prefixWord ++ tailWord_1985855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985855).length < 2 ^ (prefixWord ++ tailWord_1985855).sum := by decide
  have hdescent : baseEnd_1985855 < baseStart_1985855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985865 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 2, 5, 2]
def baseStart_1985865 : Nat := 118140960795 + 1985865 * 2 ^ 59
def prefixEnd_1985865 : Nat := 4983230072969 + 3 ^ 40 * 1985865 * 2
def baseEnd_1985865 : Nat := 1019703259940978027754679

theorem tailTrace_1985865 : CollatzResearch.WordTrace tailWord_1985865 prefixEnd_1985865 1019703259940978027754679 := by
  unfold tailWord_1985865
  simp only [CollatzResearch.WordTrace]
  refine ⟨72430446950557738585303049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48286964633705159056868699 72430446950557738585303049)
  ·
    refine ⟨54322835212918303938977287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72430446950557738585303049 54322835212918303938977287)
    ·
      refine ⟨81484252819377455908465931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54322835212918303938977287 81484252819377455908465931)
      ·
        refine ⟨122226379229066183862698897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81484252819377455908465931 122226379229066183862698897)
        ·
          refine ⟨91669784421799637897024173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122226379229066183862698897 91669784421799637897024173)
          ·
            refine ⟨34376169158174864211384065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91669784421799637897024173 34376169158174864211384065)
            ·
              refine ⟨25782126868631148158538049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34376169158174864211384065 25782126868631148158538049)
              ·
                refine ⟨19336595151473361118903537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25782126868631148158538049 19336595151473361118903537)
                ·
                  refine ⟨14502446363605020839177653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19336595151473361118903537 14502446363605020839177653)
                  ·
                    refine ⟨1359604346587970703672905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14502446363605020839177653 1359604346587970703672905)
                    ·
                      refine ⟨1019703259940978027754679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1359604346587970703672905 1019703259940978027754679)
                      ·
                        rfl

theorem cell23_1985865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 5, 2].length) (baseStart_1985865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985865 prefixEnd_1985865 := by exact prefixLift 1985865
  have htrace : WordTrace (prefixWord ++ tailWord_1985865) baseStart_1985865 baseEnd_1985865 := by
    simpa [prefixWord, tailWord_1985865, baseEnd_1985865] using wordTrace_append hprefix tailTrace_1985865
  have hstable : (prefixWord ++ tailWord_1985865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985865).length < 2 ^ (prefixWord ++ tailWord_1985865).sum := by decide
  have hdescent : baseEnd_1985865 < baseStart_1985865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985915 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 3]
def baseStart_1985915 : Nat := 118140960795 + 1985915 * 2 ^ 59
def prefixEnd_1985915 : Nat := 4983230072969 + 3 ^ 40 * 1985915 * 2
def baseEnd_1985915 : Nat := 1019728933973702832129449

theorem tailTrace_1985915 : CollatzResearch.WordTrace tailWord_1985915 prefixEnd_1985915 1019728933973702832129449 := by
  unfold tailWord_1985915
  simp only [CollatzResearch.WordTrace]
  refine ⟨72432270600376597124623199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48288180400251064749748799 72432270600376597124623199)
  ·
    refine ⟨108648405900564895686934799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72432270600376597124623199 108648405900564895686934799)
    ·
      refine ⟨162972608850847343530402199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108648405900564895686934799 162972608850847343530402199)
      ·
        refine ⟨244458913276271015295603299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162972608850847343530402199 244458913276271015295603299)
        ·
          refine ⟨366688369914406522943404949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244458913276271015295603299 366688369914406522943404949)
          ·
            refine ⟨17188517339737805762972107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 366688369914406522943404949 17188517339737805762972107)
            ·
              refine ⟨25782776009606708644458161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17188517339737805762972107 25782776009606708644458161)
              ·
                refine ⟨19337082007205031483343621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25782776009606708644458161 19337082007205031483343621)
                ·
                  refine ⟨3625702876350943403126929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19337082007205031483343621 3625702876350943403126929)
                  ·
                    refine ⟨2719277157263207552345197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3625702876350943403126929 2719277157263207552345197)
                    ·
                      refine ⟨1019728933973702832129449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2719277157263207552345197 1019728933973702832129449)
                      ·
                        rfl

theorem cell23_1985915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 3].length) (baseStart_1985915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985915 prefixEnd_1985915 := by exact prefixLift 1985915
  have htrace : WordTrace (prefixWord ++ tailWord_1985915) baseStart_1985915 baseEnd_1985915 := by
    simpa [prefixWord, tailWord_1985915, baseEnd_1985915] using wordTrace_append hprefix tailTrace_1985915
  have hstable : (prefixWord ++ tailWord_1985915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985915).length < 2 ^ (prefixWord ++ tailWord_1985915).sum := by decide
  have hdescent : baseEnd_1985915 < baseStart_1985915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985932 : List Nat := [2, 2, 1, 2, 1, 3, 4, 1, 2, 2, 3]
def baseStart_1985932 : Nat := 118140960795 + 1985932 * 2 ^ 59
def prefixEnd_1985932 : Nat := 4983230072969 + 3 ^ 40 * 1985932 * 2
def baseEnd_1985932 : Nat := 1019737663144829265616871

theorem tailTrace_1985932 : CollatzResearch.WordTrace tailWord_1985932 prefixEnd_1985932 1019737663144829265616871 := by
  unfold tailWord_1985932
  simp only [CollatzResearch.WordTrace]
  refine ⟨36216445320657504513996025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48288593760876672685328033 36216445320657504513996025)
  ·
    refine ⟨27162333990493128385497019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36216445320657504513996025 27162333990493128385497019)
    ·
      refine ⟨40743500985739692578245529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27162333990493128385497019 40743500985739692578245529)
      ·
        refine ⟨30557625739304769433684147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40743500985739692578245529 30557625739304769433684147)
        ·
          refine ⟨45836438608957154150526221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30557625739304769433684147 45836438608957154150526221)
          ·
            refine ⟨17188664478358932806447333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45836438608957154150526221 17188664478358932806447333)
            ·
              refine ⟨3222874589692299901208875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17188664478358932806447333 3222874589692299901208875)
              ·
                refine ⟨4834311884538449851813313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222874589692299901208875 4834311884538449851813313)
                ·
                  refine ⟨3625733913403837388859985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4834311884538449851813313 3625733913403837388859985)
                  ·
                    refine ⟨2719300435052878041644989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3625733913403837388859985 2719300435052878041644989)
                    ·
                      refine ⟨1019737663144829265616871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2719300435052878041644989 1019737663144829265616871)
                      ·
                        rfl

theorem cell23_1985932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_1985932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985932 prefixEnd_1985932 := by exact prefixLift 1985932
  have htrace : WordTrace (prefixWord ++ tailWord_1985932) baseStart_1985932 baseEnd_1985932 := by
    simpa [prefixWord, tailWord_1985932, baseEnd_1985932] using wordTrace_append hprefix tailTrace_1985932
  have hstable : (prefixWord ++ tailWord_1985932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985932).length < 2 ^ (prefixWord ++ tailWord_1985932).sum := by decide
  have hdescent : baseEnd_1985932 < baseStart_1985932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985982 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_1985982 : Nat := 118140960795 + 1985982 * 2 ^ 59
def prefixEnd_1985982 : Nat := 4983230072969 + 3 ^ 40 * 1985982 * 2
def baseEnd_1985982 : Nat := 339921112392518023330547

theorem tailTrace_1985982 : CollatzResearch.WordTrace tailWord_1985982 prefixEnd_1985982 339921112392518023330547 := by
  unfold tailWord_1985982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9054339286391733445914025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48289809527422578378208133 9054339286391733445914025)
  ·
    refine ⟨6790754464793800084435519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9054339286391733445914025 6790754464793800084435519)
    ·
      refine ⟨10186131697190700126653279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6790754464793800084435519 10186131697190700126653279)
      ·
        refine ⟨15279197545786050189979919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10186131697190700126653279 15279197545786050189979919)
        ·
          refine ⟨22918796318679075284969879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15279197545786050189979919 22918796318679075284969879)
          ·
            refine ⟨34378194478018612927454819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22918796318679075284969879 34378194478018612927454819)
            ·
              refine ⟨51567291717027919391182229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34378194478018612927454819 51567291717027919391182229)
              ·
                refine ⟨2417216799235683721461667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51567291717027919391182229 2417216799235683721461667)
                ·
                  refine ⟨3625825198853525582192501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417216799235683721461667 3625825198853525582192501)
                  ·
                    refine ⟨339921112392518023330547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3625825198853525582192501 339921112392518023330547)
                    ·
                      rfl

theorem cell23_1985982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_1985982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985982 prefixEnd_1985982 := by exact prefixLift 1985982
  have htrace : WordTrace (prefixWord ++ tailWord_1985982) baseStart_1985982 baseEnd_1985982 := by
    simpa [prefixWord, tailWord_1985982, baseEnd_1985982] using wordTrace_append hprefix tailTrace_1985982
  have hstable : (prefixWord ++ tailWord_1985982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985982).length < 2 ^ (prefixWord ++ tailWord_1985982).sum := by decide
  have hdescent : baseEnd_1985982 < baseStart_1985982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985995 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 1, 6]
def baseStart_1985995 : Nat := 118140960795 + 1985995 * 2 ^ 59
def prefixEnd_1985995 : Nat := 4983230072969 + 3 ^ 40 * 1985995 * 2
def baseEnd_1985995 : Nat := 339923337475354173043027

theorem tailTrace_1985995 : CollatzResearch.WordTrace tailWord_1985995 prefixEnd_1985995 339923337475354173043027 := by
  unfold tailWord_1985995
  simp only [CollatzResearch.WordTrace]
  refine ⟨72435188440086770787535439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48290125626724513858356959 72435188440086770787535439)
  ·
    refine ⟨108652782660130156181303159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72435188440086770787535439 108652782660130156181303159)
    ·
      refine ⟨162979173990195234271954739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108652782660130156181303159 162979173990195234271954739)
      ·
        refine ⟨244468760985292851407932109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162979173990195234271954739 244468760985292851407932109)
        ·
          refine ⟨91675785369484819277974541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244468760985292851407932109 91675785369484819277974541)
          ·
            refine ⟨34378419513556807229240453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91675785369484819277974541 34378419513556807229240453)
            ·
              refine ⟨6445953658791901355482585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34378419513556807229240453 6445953658791901355482585)
              ·
                refine ⟨4834465244093926016611939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6445953658791901355482585 4834465244093926016611939)
                ·
                  refine ⟨7251697866140889024917909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834465244093926016611939 7251697866140889024917909)
                  ·
                    refine ⟨339923337475354173043027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7251697866140889024917909 339923337475354173043027)
                    ·
                      rfl

theorem cell23_1985995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 6].length) (baseStart_1985995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985995 prefixEnd_1985995 := by exact prefixLift 1985995
  have htrace : WordTrace (prefixWord ++ tailWord_1985995) baseStart_1985995 baseEnd_1985995 := by
    simpa [prefixWord, tailWord_1985995, baseEnd_1985995] using wordTrace_append hprefix tailTrace_1985995
  have hstable : (prefixWord ++ tailWord_1985995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985995).length < 2 ^ (prefixWord ++ tailWord_1985995).sum := by decide
  have hdescent : baseEnd_1985995 < baseStart_1985995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985996 : List Nat := [2, 2, 1, 4, 2, 1, 1, 5, 1, 1, 3]
def baseStart_1985996 : Nat := 118140960795 + 1985996 * 2 ^ 59
def prefixEnd_1985996 : Nat := 4983230072969 + 3 ^ 40 * 1985996 * 2
def baseEnd_1985996 : Nat := 1019770525906717015216577

theorem tailTrace_1985996 : CollatzResearch.WordTrace tailWord_1985996 prefixEnd_1985996 1019770525906717015216577 := by
  unfold tailWord_1985996
  simp only [CollatzResearch.WordTrace]
  refine ⟨36217612456541573979160921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48290149942055431972214561 36217612456541573979160921)
  ·
    refine ⟨27163209342406180484370691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36217612456541573979160921 27163209342406180484370691)
    ·
      refine ⟨40744814013609270726556037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27163209342406180484370691 40744814013609270726556037)
      ·
        refine ⟨7639652627551738261229257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40744814013609270726556037 7639652627551738261229257)
        ·
          refine ⟨5729739470663803695921943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7639652627551738261229257 5729739470663803695921943)
          ·
            refine ⟨8594609205995705543882915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5729739470663803695921943 8594609205995705543882915)
            ·
              refine ⟨12891913808993558315824373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8594609205995705543882915 12891913808993558315824373)
              ·
                refine ⟨1208616919593146092108535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12891913808993558315824373 1208616919593146092108535)
                ·
                  refine ⟨1812925379389719138162803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208616919593146092108535 1812925379389719138162803)
                  ·
                    refine ⟨2719388069084578707244205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1812925379389719138162803 2719388069084578707244205)
                    ·
                      refine ⟨1019770525906717015216577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2719388069084578707244205 1019770525906717015216577)
                      ·
                        rfl

theorem cell23_1985996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_1985996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1985996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1985996 prefixEnd_1985996 := by exact prefixLift 1985996
  have htrace : WordTrace (prefixWord ++ tailWord_1985996) baseStart_1985996 baseEnd_1985996 := by
    simpa [prefixWord, tailWord_1985996, baseEnd_1985996] using wordTrace_append hprefix tailTrace_1985996
  have hstable : (prefixWord ++ tailWord_1985996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985996).length < 2 ^ (prefixWord ++ tailWord_1985996).sum := by decide
  have hdescent : baseEnd_1985996 < baseStart_1985996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986015 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 6]
def baseStart_1986015 : Nat := 118140960795 + 1986015 * 2 ^ 59
def prefixEnd_1986015 : Nat := 4983230072969 + 3 ^ 40 * 1986015 * 2
def baseEnd_1986015 : Nat := 1019780282039152440878989

theorem tailTrace_1986015 : CollatzResearch.WordTrace tailWord_1986015 prefixEnd_1986015 1019780282039152440878989 := by
  unfold tailWord_1986015
  simp only [CollatzResearch.WordTrace]
  refine ⟨72435917900014314203263499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48290611933342876135508999 72435917900014314203263499)
  ·
    refine ⟨108653876850021471304895249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72435917900014314203263499 108653876850021471304895249)
    ·
      refine ⟨81490407637516103478671437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108653876850021471304895249 81490407637516103478671437)
      ·
        refine ⟨30558902864068538804501789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81490407637516103478671437 30558902864068538804501789)
        ·
          refine ⟨11459588574025702051688171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30558902864068538804501789 11459588574025702051688171)
          ·
            refine ⟨17189382861038553077532257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11459588574025702051688171 17189382861038553077532257)
            ·
              refine ⟨12892037145778914808149193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17189382861038553077532257 12892037145778914808149193)
              ·
                refine ⟨9669027859334186106111895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12892037145778914808149193 9669027859334186106111895)
                ·
                  refine ⟨14503541789001279159167843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9669027859334186106111895 14503541789001279159167843)
                  ·
                    refine ⟨21755312683501918738751765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14503541789001279159167843 21755312683501918738751765)
                    ·
                      refine ⟨1019780282039152440878989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21755312683501918738751765 1019780282039152440878989)
                      ·
                        rfl

theorem cell23_1986015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_1986015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986015 prefixEnd_1986015 := by exact prefixLift 1986015
  have htrace : WordTrace (prefixWord ++ tailWord_1986015) baseStart_1986015 baseEnd_1986015 := by
    simpa [prefixWord, tailWord_1986015, baseEnd_1986015] using wordTrace_append hprefix tailTrace_1986015
  have hstable : (prefixWord ++ tailWord_1986015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986015).length < 2 ^ (prefixWord ++ tailWord_1986015).sum := by decide
  have hdescent : baseEnd_1986015 < baseStart_1986015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986032 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 4]
def baseStart_1986032 : Nat := 118140960795 + 1986032 * 2 ^ 59
def prefixEnd_1986032 : Nat := 4983230072969 + 3 ^ 40 * 1986032 * 2
def baseEnd_1986032 : Nat := 1019789011210278874366411

theorem tailTrace_1986032 : CollatzResearch.WordTrace tailWord_1986032 prefixEnd_1986032 1019789011210278874366411 := by
  unfold tailWord_1986032
  simp only [CollatzResearch.WordTrace]
  refine ⟨36218268970476363053316175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48291025293968484071088233 36218268970476363053316175)
  ·
    refine ⟨54327403455714544579974263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36218268970476363053316175 54327403455714544579974263)
    ·
      refine ⟨81491105183571816869961395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54327403455714544579974263 81491105183571816869961395)
      ·
        refine ⟨122236657775357725304942093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81491105183571816869961395 122236657775357725304942093)
        ·
          refine ⟨45838746665759146989353285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122236657775357725304942093 45838746665759146989353285)
          ·
            refine ⟨8594764999829840060503741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45838746665759146989353285 8594764999829840060503741)
            ·
              refine ⟨3223036874936190022688903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8594764999829840060503741 3223036874936190022688903)
              ·
                refine ⟨4834555312404285034033355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223036874936190022688903 4834555312404285034033355)
                ·
                  refine ⟨7251832968606427551050033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4834555312404285034033355 7251832968606427551050033)
                  ·
                    refine ⟨5438874726454820663287525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7251832968606427551050033 5438874726454820663287525)
                    ·
                      refine ⟨1019789011210278874366411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5438874726454820663287525 1019789011210278874366411)
                      ·
                        rfl

theorem cell23_1986032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 4].length) (baseStart_1986032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986032 prefixEnd_1986032 := by exact prefixLift 1986032
  have htrace : WordTrace (prefixWord ++ tailWord_1986032) baseStart_1986032 baseEnd_1986032 := by
    simpa [prefixWord, tailWord_1986032, baseEnd_1986032] using wordTrace_append hprefix tailTrace_1986032
  have hstable : (prefixWord ++ tailWord_1986032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986032).length < 2 ^ (prefixWord ++ tailWord_1986032).sum := by decide
  have hdescent : baseEnd_1986032 < baseStart_1986032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986065 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_1986065 : Nat := 118140960795 + 1986065 * 2 ^ 59
def prefixEnd_1986065 : Nat := 4983230072969 + 3 ^ 40 * 1986065 * 2
def baseEnd_1986065 : Nat := 1019805956071877245253759

theorem tailTrace_1986065 : CollatzResearch.WordTrace tailWord_1986065 prefixEnd_1986065 1019805956071877245253759 := by
  unfold tailWord_1986065
  simp only [CollatzResearch.WordTrace]
  refine ⟨72437741549833172742583649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48291827699888781828389099 72437741549833172742583649)
  ·
    refine ⟨54328306162374879556937737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72437741549833172742583649 54328306162374879556937737)
    ·
      refine ⟨40746229621781159667703303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54328306162374879556937737 40746229621781159667703303)
      ·
        refine ⟨61119344432671739501554955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40746229621781159667703303 61119344432671739501554955)
        ·
          refine ⟨91679016649007609252332433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61119344432671739501554955 91679016649007609252332433)
          ·
            refine ⟨68759262486755706939249325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91679016649007609252332433 68759262486755706939249325)
            ·
              refine ⟨25784723432533390102218497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68759262486755706939249325 25784723432533390102218497)
              ·
                refine ⟨19338542574400042576663873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25784723432533390102218497 19338542574400042576663873)
                ·
                  refine ⟨14503906930800031932497905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19338542574400042576663873 14503906930800031932497905)
                  ·
                    refine ⟨10877930198100023949373429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14503906930800031932497905 10877930198100023949373429)
                    ·
                      refine ⟨1019805956071877245253759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10877930198100023949373429 1019805956071877245253759)
                      ·
                        rfl

theorem cell23_1986065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_1986065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986065 prefixEnd_1986065 := by exact prefixLift 1986065
  have htrace : WordTrace (prefixWord ++ tailWord_1986065) baseStart_1986065 baseEnd_1986065 := by
    simpa [prefixWord, tailWord_1986065, baseEnd_1986065] using wordTrace_append hprefix tailTrace_1986065
  have hstable : (prefixWord ++ tailWord_1986065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986065).length < 2 ^ (prefixWord ++ tailWord_1986065).sum := by decide
  have hdescent : baseEnd_1986065 < baseStart_1986065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986069 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_1986069 : Nat := 118140960795 + 1986069 * 2 ^ 59
def prefixEnd_1986069 : Nat := 4983230072969 + 3 ^ 40 * 1986069 * 2
def baseEnd_1986069 : Nat := 1019808009994495229603741

theorem tailTrace_1986069 : CollatzResearch.WordTrace tailWord_1986069 prefixEnd_1986069 1019808009994495229603741 := by
  unfold tailWord_1986069
  simp only [CollatzResearch.WordTrace]
  refine ⟨72437887441818681425729261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48291924961212454283819507 72437887441818681425729261)
  ·
    refine ⟨27164207790682005534648473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72437887441818681425729261 27164207790682005534648473)
    ·
      refine ⟨20373155843011504150986355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27164207790682005534648473 20373155843011504150986355)
      ·
        refine ⟨30559733764517256226479533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20373155843011504150986355 30559733764517256226479533)
        ·
          refine ⟨11459900161693971084929825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30559733764517256226479533 11459900161693971084929825)
          ·
            refine ⟨8594925121270478313697369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11459900161693971084929825 8594925121270478313697369)
            ·
              refine ⟨6446193840952858735273027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8594925121270478313697369 6446193840952858735273027)
              ·
                refine ⟨9669290761429288102909541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6446193840952858735273027 9669290761429288102909541)
                ·
                  refine ⟨1812992017767991519295539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9669290761429288102909541 1812992017767991519295539)
                  ·
                    refine ⟨2719488026651987278943309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1812992017767991519295539 2719488026651987278943309)
                    ·
                      refine ⟨1019808009994495229603741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2719488026651987278943309 1019808009994495229603741)
                      ·
                        rfl

theorem cell23_1986069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_1986069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986069 prefixEnd_1986069 := by exact prefixLift 1986069
  have htrace : WordTrace (prefixWord ++ tailWord_1986069) baseStart_1986069 baseEnd_1986069 := by
    simpa [prefixWord, tailWord_1986069, baseEnd_1986069] using wordTrace_append hprefix tailTrace_1986069
  have hstable : (prefixWord ++ tailWord_1986069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986069).length < 2 ^ (prefixWord ++ tailWord_1986069).sum := by decide
  have hdescent : baseEnd_1986069 < baseStart_1986069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986085 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_1986085 : Nat := 118140960795 + 1986085 * 2 ^ 59
def prefixEnd_1986085 : Nat := 4983230072969 + 3 ^ 40 * 1986085 * 2
def baseEnd_1986085 : Nat := 339938741894989055667889

theorem tailTrace_1986085 : CollatzResearch.WordTrace tailWord_1986085 prefixEnd_1986085 339938741894989055667889 := by
  unfold tailWord_1986085
  simp only [CollatzResearch.WordTrace]
  refine ⟨72438471009760716158311709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48292314006507144105541139 72438471009760716158311709)
  ·
    refine ⟨27164426628660268559366891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72438471009760716158311709 27164426628660268559366891)
    ·
      refine ⟨40746639942990402839050337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27164426628660268559366891 40746639942990402839050337)
      ·
        refine ⟨30559979957242802129287753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40746639942990402839050337 30559979957242802129287753)
        ·
          refine ⟨22919984967932101596965815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30559979957242802129287753 22919984967932101596965815)
          ·
            refine ⟨34379977451898152395448723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22919984967932101596965815 34379977451898152395448723)
            ·
              refine ⟨51569966177847228593173085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34379977451898152395448723 51569966177847228593173085)
              ·
                refine ⟨19338737316692710722439907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51569966177847228593173085 19338737316692710722439907)
                ·
                  refine ⟨29008105975039066083659861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19338737316692710722439907 29008105975039066083659861)
                  ·
                    refine ⟨339938741894989055667889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29008105975039066083659861 339938741894989055667889)
                    ·
                      rfl

theorem cell23_1986085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_1986085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986085 prefixEnd_1986085 := by exact prefixLift 1986085
  have htrace : WordTrace (prefixWord ++ tailWord_1986085) baseStart_1986085 baseEnd_1986085 := by
    simpa [prefixWord, tailWord_1986085, baseEnd_1986085] using wordTrace_append hprefix tailTrace_1986085
  have hstable : (prefixWord ++ tailWord_1986085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986085).length < 2 ^ (prefixWord ++ tailWord_1986085).sum := by decide
  have hdescent : baseEnd_1986085 < baseStart_1986085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986113 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 1, 3, 2]
def baseStart_1986113 : Nat := 118140960795 + 1986113 * 2 ^ 59
def prefixEnd_1986113 : Nat := 4983230072969 + 3 ^ 40 * 1986113 * 2
def baseEnd_1986113 : Nat := 1019830603143293057453539

theorem tailTrace_1986113 : CollatzResearch.WordTrace tailWord_1986113 prefixEnd_1986113 1019830603143293057453539 := by
  unfold tailWord_1986113
  simp only [CollatzResearch.WordTrace]
  refine ⟨72439492253659276940330993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48292994835772851293553995 72439492253659276940330993)
  ·
    refine ⟨54329619190244457705248245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72439492253659276940330993 54329619190244457705248245)
    ·
      refine ⟨5093401799085417909867023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54329619190244457705248245 5093401799085417909867023)
      ·
        refine ⟨7640102698628126864800535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093401799085417909867023 7640102698628126864800535)
        ·
          refine ⟨11460154047942190297200803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7640102698628126864800535 11460154047942190297200803)
          ·
            refine ⟨17190231071913285445801205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11460154047942190297200803 17190231071913285445801205)
            ·
              refine ⟨1611584162991870510543863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17190231071913285445801205 1611584162991870510543863)
              ·
                refine ⟨2417376244487805765815795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611584162991870510543863 2417376244487805765815795)
                ·
                  refine ⟨3626064366731708648723693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417376244487805765815795 3626064366731708648723693)
                  ·
                    refine ⟨1359774137524390743271385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3626064366731708648723693 1359774137524390743271385)
                    ·
                      refine ⟨1019830603143293057453539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1359774137524390743271385 1019830603143293057453539)
                      ·
                        rfl

theorem cell23_1986113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_1986113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986113 prefixEnd_1986113 := by exact prefixLift 1986113
  have htrace : WordTrace (prefixWord ++ tailWord_1986113) baseStart_1986113 baseEnd_1986113 := by
    simpa [prefixWord, tailWord_1986113, baseEnd_1986113] using wordTrace_append hprefix tailTrace_1986113
  have hstable : (prefixWord ++ tailWord_1986113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986113).length < 2 ^ (prefixWord ++ tailWord_1986113).sum := by decide
  have hdescent : baseEnd_1986113 < baseStart_1986113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986122 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_1986122 : Nat := 118140960795 + 1986122 * 2 ^ 59
def prefixEnd_1986122 : Nat := 4983230072969 + 3 ^ 40 * 1986122 * 2
def baseEnd_1986122 : Nat := 1019835224469183522240997

theorem tailTrace_1986122 : CollatzResearch.WordTrace tailWord_1986122 prefixEnd_1986122 1019835224469183522240997 := by
  unfold tailWord_1986122
  simp only [CollatzResearch.WordTrace]
  refine ⟨18109955127656667869352155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48293213673751114318272413 18109955127656667869352155)
  ·
    refine ⟨27164932691485001804028233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18109955127656667869352155 27164932691485001804028233)
    ·
      refine ⟨20373699518613751353021175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27164932691485001804028233 20373699518613751353021175)
      ·
        refine ⟨30560549277920627029531763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20373699518613751353021175 30560549277920627029531763)
        ·
          refine ⟨45840823916880940544297645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30560549277920627029531763 45840823916880940544297645)
          ·
            refine ⟨17190308968830352704111617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45840823916880940544297645 17190308968830352704111617)
            ·
              refine ⟨12892731726622764528083713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17190308968830352704111617 12892731726622764528083713)
              ·
                refine ⟨9669548794967073396062785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12892731726622764528083713 9669548794967073396062785)
                ·
                  refine ⟨7252161596225305047047089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9669548794967073396062785 7252161596225305047047089)
                  ·
                    refine ⟨5439121197168978785285317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7252161596225305047047089 5439121197168978785285317)
                    ·
                      refine ⟨1019835224469183522240997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5439121197168978785285317 1019835224469183522240997)
                      ·
                        rfl

theorem cell23_1986122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_1986122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986122 prefixEnd_1986122 := by exact prefixLift 1986122
  have htrace : WordTrace (prefixWord ++ tailWord_1986122) baseStart_1986122 baseEnd_1986122 := by
    simpa [prefixWord, tailWord_1986122, baseEnd_1986122] using wordTrace_append hprefix tailTrace_1986122
  have hstable : (prefixWord ++ tailWord_1986122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986122).length < 2 ^ (prefixWord ++ tailWord_1986122).sum := by decide
  have hdescent : baseEnd_1986122 < baseStart_1986122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986132 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 7]
def baseStart_1986132 : Nat := 118140960795 + 1986132 * 2 ^ 59
def prefixEnd_1986132 : Nat := 4983230072969 + 3 ^ 40 * 1986132 * 2
def baseEnd_1986132 : Nat := 113315595475080942568439

theorem tailTrace_1986132 : CollatzResearch.WordTrace tailWord_1986132 prefixEnd_1986132 113315595475080942568439 := by
  unfold tailWord_1986132
  simp only [CollatzResearch.WordTrace]
  refine ⟨36220092620295221592636325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48293456827060295456848433 36220092620295221592636325)
  ·
    refine ⟨6791267366305354048619311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36220092620295221592636325 6791267366305354048619311)
    ·
      refine ⟨10186901049458031072928967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6791267366305354048619311 10186901049458031072928967)
      ·
        refine ⟨15280351574187046609393451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10186901049458031072928967 15280351574187046609393451)
        ·
          refine ⟨22920527361280569914090177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15280351574187046609393451 22920527361280569914090177)
          ·
            refine ⟨17190395520960427435567633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22920527361280569914090177 17190395520960427435567633)
            ·
              refine ⟨12892796640720320576675725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17190395520960427435567633 12892796640720320576675725)
              ·
                refine ⟨4834798740270120216253397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12892796640720320576675725 4834798740270120216253397)
                ·
                  refine ⟨113315595475080942568439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4834798740270120216253397 113315595475080942568439)
                  ·
                    rfl

theorem cell23_1986132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_1986132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986132 prefixEnd_1986132 := by exact prefixLift 1986132
  have htrace : WordTrace (prefixWord ++ tailWord_1986132) baseStart_1986132 baseEnd_1986132 := by
    simpa [prefixWord, tailWord_1986132, baseEnd_1986132] using wordTrace_append hprefix tailTrace_1986132
  have hstable : (prefixWord ++ tailWord_1986132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986132).length < 2 ^ (prefixWord ++ tailWord_1986132).sum := by decide
  have hdescent : baseEnd_1986132 < baseStart_1986132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986166 : List Nat := [5, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_1986166 : Nat := 118140960795 + 1986166 * 2 ^ 59
def prefixEnd_1986166 : Nat := 4983230072969 + 3 ^ 40 * 1986166 * 2
def baseEnd_1986166 : Nat := 113317535290886816676755

theorem tailTrace_1986166 : CollatzResearch.WordTrace tailWord_1986166 prefixEnd_1986166 113317535290886816676755 := by
  unfold tailWord_1986166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4527589082654204187000647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48294283548311511328006901 4527589082654204187000647)
  ·
    refine ⟨6791383623981306280500971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4527589082654204187000647 6791383623981306280500971)
    ·
      refine ⟨10187075435971959420751457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6791383623981306280500971 10187075435971959420751457)
      ·
        refine ⟨7640306576978969565563593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10187075435971959420751457 7640306576978969565563593)
        ·
          refine ⟨5730229932734227174172695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7640306576978969565563593 5730229932734227174172695)
          ·
            refine ⟨8595344899101340761259043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5730229932734227174172695 8595344899101340761259043)
            ·
              refine ⟨12893017348652011141888565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8595344899101340761259043 12893017348652011141888565)
              ·
                refine ⟨1208720376436126044552053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12893017348652011141888565 1208720376436126044552053)
                ·
                  refine ⟨113317535290886816676755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1208720376436126044552053 113317535290886816676755)
                  ·
                    rfl

theorem cell23_1986166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_1986166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986166 prefixEnd_1986166 := by exact prefixLift 1986166
  have htrace : WordTrace (prefixWord ++ tailWord_1986166) baseStart_1986166 baseEnd_1986166 := by
    simpa [prefixWord, tailWord_1986166, baseEnd_1986166] using wordTrace_append hprefix tailTrace_1986166
  have hstable : (prefixWord ++ tailWord_1986166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986166).length < 2 ^ (prefixWord ++ tailWord_1986166).sum := by decide
  have hdescent : baseEnd_1986166 < baseStart_1986166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986236 : List Nat := [2, 2, 2, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1986236 : Nat := 118140960795 + 1986236 * 2 ^ 59
def prefixEnd_1986236 : Nat := 4983230072969 + 3 ^ 40 * 1986236 * 2
def baseEnd_1986236 : Nat := 1019893761263796076215473

theorem tailTrace_1986236 : CollatzResearch.WordTrace tailWord_1986236 prefixEnd_1986236 1019893761263796076215473 := by
  unfold tailWord_1986236
  simp only [CollatzResearch.WordTrace]
  refine ⟨36221989216106834473529281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48295985621475779298039041 36221989216106834473529281)
  ·
    refine ⟨27166491912080125855146961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36221989216106834473529281 27166491912080125855146961)
    ·
      refine ⟨20374868934060094391360221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27166491912080125855146961 20374868934060094391360221)
      ·
        refine ⟨7640575850272535396760083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20374868934060094391360221 7640575850272535396760083)
        ·
          refine ⟨11460863775408803095140125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7640575850272535396760083 11460863775408803095140125)
          ·
            refine ⟨4297823915778301160677547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11460863775408803095140125 4297823915778301160677547)
            ·
              refine ⟨6446735873667451741016321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4297823915778301160677547 6446735873667451741016321)
              ·
                refine ⟨4835051905250588805762241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6446735873667451741016321 4835051905250588805762241)
                ·
                  refine ⟨3626288928937941604321681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4835051905250588805762241 3626288928937941604321681)
                  ·
                    refine ⟨2719716696703456203241261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3626288928937941604321681 2719716696703456203241261)
                    ·
                      refine ⟨1019893761263796076215473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2719716696703456203241261 1019893761263796076215473)
                      ·
                        rfl

theorem cell23_1986236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1986236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986236 prefixEnd_1986236 := by exact prefixLift 1986236
  have htrace : WordTrace (prefixWord ++ tailWord_1986236) baseStart_1986236 baseEnd_1986236 := by
    simpa [prefixWord, tailWord_1986236, baseEnd_1986236] using wordTrace_append hprefix tailTrace_1986236
  have hstable : (prefixWord ++ tailWord_1986236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986236).length < 2 ^ (prefixWord ++ tailWord_1986236).sum := by decide
  have hdescent : baseEnd_1986236 < baseStart_1986236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986306 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_1986306 : Nat := 118140960795 + 1986306 * 2 ^ 59
def prefixEnd_1986306 : Nat := 4983230072969 + 3 ^ 40 * 1986306 * 2
def baseEnd_1986306 : Nat := 1019929704909610802340151

theorem tailTrace_1986306 : CollatzResearch.WordTrace tailWord_1986306 prefixEnd_1986306 1019929704909610802340151 := by
  unfold tailWord_1986306
  simp only [CollatzResearch.WordTrace]
  refine ⟨18111632885490017725526693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48297687694640047268071181 18111632885490017725526693)
  ·
    refine ⟨3395931166029378323536255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18111632885490017725526693 3395931166029378323536255)
    ·
      refine ⟨5093896749044067485304383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3395931166029378323536255 5093896749044067485304383)
      ·
        refine ⟨7640845123566101227956575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093896749044067485304383 7640845123566101227956575)
        ·
          refine ⟨11461267685349151841934863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7640845123566101227956575 11461267685349151841934863)
          ·
            refine ⟨17191901528023727762902295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11461267685349151841934863 17191901528023727762902295)
            ·
              refine ⟨25787852292035591644353443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17191901528023727762902295 25787852292035591644353443)
              ·
                refine ⟨38681778438053387466530165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25787852292035591644353443 38681778438053387466530165)
                ·
                  refine ⟨3626416728567505074987203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38681778438053387466530165 3626416728567505074987203)
                  ·
                    refine ⟨5439625092851257612480805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3626416728567505074987203 5439625092851257612480805)
                    ·
                      refine ⟨1019929704909610802340151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5439625092851257612480805 1019929704909610802340151)
                      ·
                        rfl

theorem cell23_1986306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_1986306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986306 prefixEnd_1986306 := by exact prefixLift 1986306
  have htrace : WordTrace (prefixWord ++ tailWord_1986306) baseStart_1986306 baseEnd_1986306 := by
    simpa [prefixWord, tailWord_1986306, baseEnd_1986306] using wordTrace_append hprefix tailTrace_1986306
  have hstable : (prefixWord ++ tailWord_1986306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986306).length < 2 ^ (prefixWord ++ tailWord_1986306).sum := by decide
  have hdescent : baseEnd_1986306 < baseStart_1986306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986316 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 2, 4]
def baseStart_1986316 : Nat := 118140960795 + 1986316 * 2 ^ 59
def prefixEnd_1986316 : Nat := 4983230072969 + 3 ^ 40 * 1986316 * 2
def baseEnd_1986316 : Nat := 339978279905385254405035

theorem tailTrace_1986316 : CollatzResearch.WordTrace tailWord_1986316 prefixEnd_1986316 339978279905385254405035 := by
  unfold tailWord_1986316
  simp only [CollatzResearch.WordTrace]
  refine ⟨36223448135961921304985401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48297930847949228406647201 36223448135961921304985401)
  ·
    refine ⟨27167586101971440978739051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36223448135961921304985401 27167586101971440978739051)
    ·
      refine ⟨40751379152957161468108577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27167586101971440978739051 40751379152957161468108577)
      ·
        refine ⟨30563534364717871101081433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40751379152957161468108577 30563534364717871101081433)
        ·
          refine ⟨22922650773538403325811075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30563534364717871101081433 22922650773538403325811075)
          ·
            refine ⟨34383976160307604988716613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22922650773538403325811075 34383976160307604988716613)
            ·
              refine ⟨6446995530057675935384365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34383976160307604988716613 6446995530057675935384365)
              ·
                refine ⟨2417623323771628475769137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6446995530057675935384365 2417623323771628475769137)
                ·
                  refine ⟨1813217492828721356826853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2417623323771628475769137 1813217492828721356826853)
                  ·
                    refine ⟨339978279905385254405035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1813217492828721356826853 339978279905385254405035)
                    ·
                      rfl

theorem cell23_1986316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_1986316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986316 prefixEnd_1986316 := by exact prefixLift 1986316
  have htrace : WordTrace (prefixWord ++ tailWord_1986316) baseStart_1986316 baseEnd_1986316 := by
    simpa [prefixWord, tailWord_1986316, baseEnd_1986316] using wordTrace_append hprefix tailTrace_1986316
  have hstable : (prefixWord ++ tailWord_1986316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986316).length < 2 ^ (prefixWord ++ tailWord_1986316).sum := by decide
  have hdescent : baseEnd_1986316 < baseStart_1986316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986340 : List Nat := [2, 3, 1, 3, 2, 3, 2, 1, 1, 1, 4]
def baseStart_1986340 : Nat := 118140960795 + 1986340 * 2 ^ 59
def prefixEnd_1986340 : Nat := 4983230072969 + 3 ^ 40 * 1986340 * 2
def baseEnd_1986340 : Nat := 1019947163251863669314995

theorem tailTrace_1986340 : CollatzResearch.WordTrace tailWord_1986340 prefixEnd_1986340 1019947163251863669314995 := by
  unfold tailWord_1986340
  simp only [CollatzResearch.WordTrace]
  refine ⟨36223885811918447354422237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48298514415891263139229649 36223885811918447354422237)
  ·
    refine ⟨13583957179469417757908339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36223885811918447354422237 13583957179469417757908339)
    ·
      refine ⟨20375935769204126636862509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13583957179469417757908339 20375935769204126636862509)
      ·
        refine ⟨7640975913451547488823441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20375935769204126636862509 7640975913451547488823441)
        ·
          refine ⟨5730731935088660616617581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7640975913451547488823441 5730731935088660616617581)
          ·
            refine ⟨2149024475658247731231593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5730731935088660616617581 2149024475658247731231593)
            ·
              refine ⟨1611768356743685798423695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2149024475658247731231593 1611768356743685798423695)
              ·
                refine ⟨2417652535115528697635543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611768356743685798423695 2417652535115528697635543)
                ·
                  refine ⟨3626478802673293046453315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417652535115528697635543 3626478802673293046453315)
                  ·
                    refine ⟨5439718204009939569679973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3626478802673293046453315 5439718204009939569679973)
                    ·
                      refine ⟨1019947163251863669314995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5439718204009939569679973 1019947163251863669314995)
                      ·
                        rfl

theorem cell23_1986340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_1986340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986340 prefixEnd_1986340 := by exact prefixLift 1986340
  have htrace : WordTrace (prefixWord ++ tailWord_1986340) baseStart_1986340 baseEnd_1986340 := by
    simpa [prefixWord, tailWord_1986340, baseEnd_1986340] using wordTrace_append hprefix tailTrace_1986340
  have hstable : (prefixWord ++ tailWord_1986340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986340).length < 2 ^ (prefixWord ++ tailWord_1986340).sum := by decide
  have hdescent : baseEnd_1986340 < baseStart_1986340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986399 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 5]
def baseStart_1986399 : Nat := 118140960795 + 1986399 * 2 ^ 59
def prefixEnd_1986399 : Nat := 4983230072969 + 3 ^ 40 * 1986399 * 2
def baseEnd_1986399 : Nat := 1019977458610478938477223

theorem tailTrace_1986399 : CollatzResearch.WordTrace tailWord_1986399 prefixEnd_1986399 1019977458610478938477223 := by
  unfold tailWord_1986399
  simp only [CollatzResearch.WordTrace]
  refine ⟨72449923530623147785242251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48299949020415431856828167 72449923530623147785242251)
  ·
    refine ⟨108674885295934721677863377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72449923530623147785242251 108674885295934721677863377)
    ·
      refine ⟨81506163971951041258397533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108674885295934721677863377 81506163971951041258397533)
      ·
        refine ⟨30564811489481640471899075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81506163971951041258397533 30564811489481640471899075)
        ·
          refine ⟨45847217234222460707848613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30564811489481640471899075 45847217234222460707848613)
          ·
            refine ⟨8596353231416711382721615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45847217234222460707848613 8596353231416711382721615)
            ·
              refine ⟨12894529847125067074082423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8596353231416711382721615 12894529847125067074082423)
              ·
                refine ⟨19341794770687600611123635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12894529847125067074082423 19341794770687600611123635)
                ·
                  refine ⟨29012692156031400916685453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19341794770687600611123635 29012692156031400916685453)
                  ·
                    refine ⟨10879759558511775343757045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29012692156031400916685453 10879759558511775343757045)
                    ·
                      refine ⟨1019977458610478938477223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10879759558511775343757045 1019977458610478938477223)
                      ·
                        rfl

theorem cell23_1986399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_1986399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986399 prefixEnd_1986399 := by exact prefixLift 1986399
  have htrace : WordTrace (prefixWord ++ tailWord_1986399) baseStart_1986399 baseEnd_1986399 := by
    simpa [prefixWord, tailWord_1986399, baseEnd_1986399] using wordTrace_append hprefix tailTrace_1986399
  have hstable : (prefixWord ++ tailWord_1986399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986399).length < 2 ^ (prefixWord ++ tailWord_1986399).sum := by decide
  have hdescent : baseEnd_1986399 < baseStart_1986399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986409 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 4]
def baseStart_1986409 : Nat := 118140960795 + 1986409 * 2 ^ 59
def prefixEnd_1986409 : Nat := 4983230072969 + 3 ^ 40 * 1986409 * 2
def baseEnd_1986409 : Nat := 1019982593417023899352177

theorem tailTrace_1986409 : CollatzResearch.WordTrace tailWord_1986409 prefixEnd_1986409 1019982593417023899352177 := by
  unfold tailWord_1986409
  simp only [CollatzResearch.WordTrace]
  refine ⟨72450288260586919493106281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48300192173724612995404187 72450288260586919493106281)
  ·
    refine ⟨54337716195440189619829711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72450288260586919493106281 54337716195440189619829711)
    ·
      refine ⟨81506574293160284429744567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54337716195440189619829711 81506574293160284429744567)
      ·
        refine ⟨122259861439740426644616851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81506574293160284429744567 122259861439740426644616851)
        ·
          refine ⟨183389792159610639966925277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122259861439740426644616851 183389792159610639966925277)
          ·
            refine ⟨68771172059853989987596979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183389792159610639966925277 68771172059853989987596979)
            ·
              refine ⟨103156758089780984981395469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68771172059853989987596979 103156758089780984981395469)
              ·
                refine ⟨38683784283667869368023301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103156758089780984981395469 38683784283667869368023301)
                ·
                  refine ⟨7253209553187725506504369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38683784283667869368023301 7253209553187725506504369)
                  ·
                    refine ⟨5439907164890794129878277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7253209553187725506504369 5439907164890794129878277)
                    ·
                      refine ⟨1019982593417023899352177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5439907164890794129878277 1019982593417023899352177)
                      ·
                        rfl

theorem cell23_1986409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_1986409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986409 prefixEnd_1986409 := by exact prefixLift 1986409
  have htrace : WordTrace (prefixWord ++ tailWord_1986409) baseStart_1986409 baseEnd_1986409 := by
    simpa [prefixWord, tailWord_1986409, baseEnd_1986409] using wordTrace_append hprefix tailTrace_1986409
  have hstable : (prefixWord ++ tailWord_1986409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986409).length < 2 ^ (prefixWord ++ tailWord_1986409).sum := by decide
  have hdescent : baseEnd_1986409 < baseStart_1986409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986449 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 1, 7]
def baseStart_1986449 : Nat := 118140960795 + 1986449 * 2 ^ 59
def prefixEnd_1986449 : Nat := 4983230072969 + 3 ^ 40 * 1986449 * 2
def baseEnd_1986449 : Nat := 340001044214401247617331

theorem tailTrace_1986449 : CollatzResearch.WordTrace tailWord_1986449 prefixEnd_1986449 340001044214401247617331 := by
  unfold tailWord_1986449
  simp only [CollatzResearch.WordTrace]
  refine ⟨72451747180442006324562401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48301164786961337549708267 72451747180442006324562401)
  ·
    refine ⟨54338810385331504743421801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72451747180442006324562401 54338810385331504743421801)
    ·
      refine ⟨40754107788998628557566351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54338810385331504743421801 40754107788998628557566351)
      ·
        refine ⟨61131161683497942836349527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40754107788998628557566351 61131161683497942836349527)
        ·
          refine ⟨91696742525246914254524291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61131161683497942836349527 91696742525246914254524291)
          ·
            refine ⟨137545113787870371381786437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91696742525246914254524291 137545113787870371381786437)
            ·
              refine ⟨25789708835225694634084957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137545113787870371381786437 25789708835225694634084957)
              ·
                refine ⟨9671140813209635487781859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25789708835225694634084957 9671140813209635487781859)
                ·
                  refine ⟨14506711219814453231672789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9671140813209635487781859 14506711219814453231672789)
                  ·
                    refine ⟨340001044214401247617331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14506711219814453231672789 340001044214401247617331)
                    ·
                      rfl

theorem cell23_1986449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_1986449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986449 prefixEnd_1986449 := by exact prefixLift 1986449
  have htrace : WordTrace (prefixWord ++ tailWord_1986449) baseStart_1986449 baseEnd_1986449 := by
    simpa [prefixWord, tailWord_1986449, baseEnd_1986449] using wordTrace_append hprefix tailTrace_1986449
  have hstable : (prefixWord ++ tailWord_1986449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986449).length < 2 ^ (prefixWord ++ tailWord_1986449).sum := by decide
  have hdescent : baseEnd_1986449 < baseStart_1986449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986499 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 6]
def baseStart_1986499 : Nat := 118140960795 + 1986499 * 2 ^ 59
def prefixEnd_1986499 : Nat := 4983230072969 + 3 ^ 40 * 1986499 * 2
def baseEnd_1986499 : Nat := 1020028806675928547226763

theorem tailTrace_1986499 : CollatzResearch.WordTrace tailWord_1986499 prefixEnd_1986499 1020028806675928547226763 := by
  unfold tailWord_1986499
  simp only [CollatzResearch.WordTrace]
  refine ⟨72453570830260864863882551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48302380553507243242588367 72453570830260864863882551)
  ·
    refine ⟨108680356245391297295823827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72453570830260864863882551 108680356245391297295823827)
    ·
      refine ⟨163020534368086945943735741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108680356245391297295823827 163020534368086945943735741)
      ·
        refine ⟨61132700388032604728900903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163020534368086945943735741 61132700388032604728900903)
        ·
          refine ⟨91699050582048907093351355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61132700388032604728900903 91699050582048907093351355)
          ·
            refine ⟨137548575873073360640027033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91699050582048907093351355 137548575873073360640027033)
            ·
              refine ⟨103161431904805020480020275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137548575873073360640027033 103161431904805020480020275)
              ·
                refine ⟨154742147857207530720030413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103161431904805020480020275 154742147857207530720030413)
                ·
                  refine ⟨58028305446452824020011405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154742147857207530720030413 58028305446452824020011405)
                  ·
                    refine ⟨21760614542419809007504277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58028305446452824020011405 21760614542419809007504277)
                    ·
                      refine ⟨1020028806675928547226763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21760614542419809007504277 1020028806675928547226763)
                      ·
                        rfl

theorem cell23_1986499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_1986499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1986499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1986499 prefixEnd_1986499 := by exact prefixLift 1986499
  have htrace : WordTrace (prefixWord ++ tailWord_1986499) baseStart_1986499 baseEnd_1986499 := by
    simpa [prefixWord, tailWord_1986499, baseEnd_1986499] using wordTrace_append hprefix tailTrace_1986499
  have hstable : (prefixWord ++ tailWord_1986499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986499).length < 2 ^ (prefixWord ++ tailWord_1986499).sum := by decide
  have hdescent : baseEnd_1986499 < baseStart_1986499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
