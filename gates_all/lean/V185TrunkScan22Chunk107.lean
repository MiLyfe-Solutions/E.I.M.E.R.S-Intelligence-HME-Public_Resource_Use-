import V185TrunkScan22Chunk106

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_960012 : List Nat := [2, 2, 1, 2, 5, 1, 1, 4, 1, 3]
def baseStart_960012 : Nat := 118140960795 + 960012 * 2 ^ 59
def prefixEnd_960012 : Nat := 4983230072969 + 3 ^ 40 * 960012 * 2
def baseEnd_960012 : Nat := 328631726722802121556661

theorem tailTrace_960012 : CollatzResearch.WordTrace tailWord_960012 prefixEnd_960012 328631726722802121556661 := by
  unfold tailWord_960012
  simp only [CollatzResearch.WordTrace]
  refine ⟨17507257099023977920713145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23343009465365303894284193 17507257099023977920713145)
  ·
    refine ⟨13130442824267983440534859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17507257099023977920713145 13130442824267983440534859)
    ·
      refine ⟨19695664236401975160802289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13130442824267983440534859 19695664236401975160802289)
      ·
        refine ⟨14771748177301481370601717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19695664236401975160802289 14771748177301481370601717)
        ·
          refine ⟨1384851391622013878493911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14771748177301481370601717 1384851391622013878493911)
          ·
            refine ⟨2077277087433020817740867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384851391622013878493911 2077277087433020817740867)
            ·
              refine ⟨3115915631149531226611301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077277087433020817740867 3115915631149531226611301)
              ·
                refine ⟨584234180840537104989619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3115915631149531226611301 584234180840537104989619)
                ·
                  refine ⟨876351271260805657484429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584234180840537104989619 876351271260805657484429)
                  ·
                    refine ⟨328631726722802121556661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 876351271260805657484429 328631726722802121556661)
                    ·
                      rfl

theorem cell22_960012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_960012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960012 prefixEnd_960012 := by exact prefixLift 960012
  have htrace : WordTrace (prefixWord ++ tailWord_960012) baseStart_960012 baseEnd_960012 := by
    simpa [prefixWord, tailWord_960012, baseEnd_960012] using wordTrace_append hprefix tailTrace_960012
  have hstable : (prefixWord ++ tailWord_960012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960012).length < 2 ^ (prefixWord ++ tailWord_960012).sum := by decide
  have hdescent : baseEnd_960012 < baseStart_960012 := by decide
  rcases family_descends (prefixWord ++ tailWord_960012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960055 : List Nat := [1, 1, 3, 1, 2, 4, 4, 1, 1, 4]
def baseStart_960055 : Nat := 118140960795 + 960055 * 2 ^ 59
def prefixEnd_960055 : Nat := 4983230072969 + 3 ^ 40 * 960055 * 2
def baseEnd_960055 : Nat := 328646446501564342731529

theorem tailTrace_960055 : CollatzResearch.WordTrace tailWord_960055 prefixEnd_960055 328646446501564342731529 := by
  unfold tailWord_960055
  simp only [CollatzResearch.WordTrace]
  refine ⟨35016082536892174185241619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23344055024594782790161079 35016082536892174185241619)
  ·
    refine ⟨52524123805338261277862429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35016082536892174185241619 52524123805338261277862429)
    ·
      refine ⟨19696546427001847979198411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52524123805338261277862429 19696546427001847979198411)
      ·
        refine ⟨29544819640502771968797617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19696546427001847979198411 29544819640502771968797617)
        ·
          refine ⟨22158614730377078976598213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29544819640502771968797617 22158614730377078976598213)
          ·
            refine ⟨4154740261945702308112165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22158614730377078976598213 4154740261945702308112165)
            ·
              refine ⟨779013799114819182771031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4154740261945702308112165 779013799114819182771031)
              ·
                refine ⟨1168520698672228774156547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779013799114819182771031 1168520698672228774156547)
                ·
                  refine ⟨1752781048008343161234821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168520698672228774156547 1752781048008343161234821)
                  ·
                    refine ⟨328646446501564342731529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1752781048008343161234821 328646446501564342731529)
                    ·
                      rfl

theorem cell22_960055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_960055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960055 prefixEnd_960055 := by exact prefixLift 960055
  have htrace : WordTrace (prefixWord ++ tailWord_960055) baseStart_960055 baseEnd_960055 := by
    simpa [prefixWord, tailWord_960055, baseEnd_960055] using wordTrace_append hprefix tailTrace_960055
  have hstable : (prefixWord ++ tailWord_960055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960055).length < 2 ^ (prefixWord ++ tailWord_960055).sum := by decide
  have hdescent : baseEnd_960055 < baseStart_960055 := by decide
  rcases family_descends (prefixWord ++ tailWord_960055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960081 : List Nat := [1, 2, 2, 1, 3, 2, 2, 9]
def baseStart_960081 : Nat := 118140960795 + 960081 * 2 ^ 59
def prefixEnd_960081 : Nat := 4983230072969 + 3 ^ 40 * 960081 * 2
def baseEnd_960081 : Nat := 36517260759212104620161

theorem tailTrace_960081 : CollatzResearch.WordTrace tailWord_960081 prefixEnd_960081 36517260759212104620161 := by
  unfold tailWord_960081
  simp only [CollatzResearch.WordTrace]
  refine ⟨35017030834797980625688097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23344687223198653750458731 35017030834797980625688097)
  ·
    refine ⟨26262773126098485469266073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35017030834797980625688097 26262773126098485469266073)
    ·
      refine ⟨19697079844573864101949555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26262773126098485469266073 19697079844573864101949555)
      ·
        refine ⟨29545619766860796152924333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19697079844573864101949555 29545619766860796152924333)
        ·
          refine ⟨11079607412572798557346625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29545619766860796152924333 11079607412572798557346625)
          ·
            refine ⟨8309705559429598918009969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11079607412572798557346625 8309705559429598918009969)
            ·
              refine ⟨6232279169572199188507477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8309705559429598918009969 6232279169572199188507477)
              ·
                refine ⟨36517260759212104620161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6232279169572199188507477 36517260759212104620161)
                ·
                  rfl

theorem cell22_960081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 9].length) (baseStart_960081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960081 prefixEnd_960081 := by exact prefixLift 960081
  have htrace : WordTrace (prefixWord ++ tailWord_960081) baseStart_960081 baseEnd_960081 := by
    simpa [prefixWord, tailWord_960081, baseEnd_960081] using wordTrace_append hprefix tailTrace_960081
  have hstable : (prefixWord ++ tailWord_960081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960081).length < 2 ^ (prefixWord ++ tailWord_960081).sum := by decide
  have hdescent : baseEnd_960081 < baseStart_960081 := by decide
  rcases family_descends (prefixWord ++ tailWord_960081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960096 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_960096 : Nat := 118140960795 + 960096 * 2 ^ 59
def prefixEnd_960096 : Nat := 4983230072969 + 3 ^ 40 * 960096 * 2
def baseEnd_960096 : Nat := 328660481639453902456403

theorem tailTrace_960096 : CollatzResearch.WordTrace tailWord_960096 prefixEnd_960096 328660481639453902456403 := by
  unfold tailWord_960096
  simp only [CollatzResearch.WordTrace]
  refine ⟨17508788964871819093742071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23345051953162425458322761 17508788964871819093742071)
  ·
    refine ⟨26263183447307728640613107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17508788964871819093742071 26263183447307728640613107)
    ·
      refine ⟨39394775170961592960919661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26263183447307728640613107 39394775170961592960919661)
      ·
        refine ⟨14773040689110597360344873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39394775170961592960919661 14773040689110597360344873)
        ·
          refine ⟨11079780516832948020258655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14773040689110597360344873 11079780516832948020258655)
          ·
            refine ⟨16619670775249422030387983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11079780516832948020258655 16619670775249422030387983)
            ·
              refine ⟨24929506162874133045581975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16619670775249422030387983 24929506162874133045581975)
              ·
                refine ⟨37394259244311199568372963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24929506162874133045581975 37394259244311199568372963)
                ·
                  refine ⟨56091388866466799352559445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37394259244311199568372963 56091388866466799352559445)
                  ·
                    refine ⟨328660481639453902456403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 56091388866466799352559445 328660481639453902456403)
                    ·
                      rfl

theorem cell22_960096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_960096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960096 prefixEnd_960096 := by exact prefixLift 960096
  have htrace : WordTrace (prefixWord ++ tailWord_960096) baseStart_960096 baseEnd_960096 := by
    simpa [prefixWord, tailWord_960096, baseEnd_960096] using wordTrace_append hprefix tailTrace_960096
  have hstable : (prefixWord ++ tailWord_960096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960096).length < 2 ^ (prefixWord ++ tailWord_960096).sum := by decide
  have hdescent : baseEnd_960096 < baseStart_960096 := by decide
  rcases family_descends (prefixWord ++ tailWord_960096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960111 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 1, 8]
def baseStart_960111 : Nat := 118140960795 + 960111 * 2 ^ 59
def prefixEnd_960111 : Nat := 4983230072969 + 3 ^ 40 * 960111 * 2
def baseEnd_960111 : Nat := 328665616445998863331357

theorem tailTrace_960111 : CollatzResearch.WordTrace tailWord_960111 prefixEnd_960111 328665616445998863331357 := by
  unfold tailWord_960111
  simp only [CollatzResearch.WordTrace]
  refine ⟨35018125024689295749280187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23345416683126197166186791 35018125024689295749280187)
  ·
    refine ⟨52527187537033943623920281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35018125024689295749280187 52527187537033943623920281)
    ·
      refine ⟨39395390652775457717940211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52527187537033943623920281 39395390652775457717940211)
      ·
        refine ⟨59093085979163186576910317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39395390652775457717940211 59093085979163186576910317)
        ·
          refine ⟨22159907242186194966341369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59093085979163186576910317 22159907242186194966341369)
          ·
            refine ⟨16619930431639646224756027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22159907242186194966341369 16619930431639646224756027)
            ·
              refine ⟨24929895647459469337134041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16619930431639646224756027 24929895647459469337134041)
              ·
                refine ⟨18697421735594602002850531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24929895647459469337134041 18697421735594602002850531)
                ·
                  refine ⟨28046132603391903004275797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18697421735594602002850531 28046132603391903004275797)
                  ·
                    refine ⟨328665616445998863331357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28046132603391903004275797 328665616445998863331357)
                    ·
                      rfl

theorem cell22_960111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_960111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960111 prefixEnd_960111 := by exact prefixLift 960111
  have htrace : WordTrace (prefixWord ++ tailWord_960111) baseStart_960111 baseEnd_960111 := by
    simpa [prefixWord, tailWord_960111, baseEnd_960111] using wordTrace_append hprefix tailTrace_960111
  have hstable : (prefixWord ++ tailWord_960111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960111).length < 2 ^ (prefixWord ++ tailWord_960111).sum := by decide
  have hdescent : baseEnd_960111 < baseStart_960111 := by decide
  rcases family_descends (prefixWord ++ tailWord_960111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960113 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 5, 3]
def baseStart_960113 : Nat := 118140960795 + 960113 * 2 ^ 59
def prefixEnd_960113 : Nat := 4983230072969 + 3 ^ 40 * 960113 * 2
def baseEnd_960113 : Nat := 328666301086871524781351

theorem tailTrace_960113 : CollatzResearch.WordTrace tailWord_960113 prefixEnd_960113 328666301086871524781351 := by
  unfold tailWord_960113
  simp only [CollatzResearch.WordTrace]
  refine ⟨35018197970682050090852993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23345465313788033393901995 35018197970682050090852993)
  ·
    refine ⟨26263648478011537568139745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35018197970682050090852993 26263648478011537568139745)
    ·
      refine ⟨19697736358508653176104809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26263648478011537568139745 19697736358508653176104809)
      ·
        refine ⟨14773302268881489882078607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19697736358508653176104809 14773302268881489882078607)
        ·
          refine ⟨22159953403322234823117911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14773302268881489882078607 22159953403322234823117911)
          ·
            refine ⟨33239930104983352234676867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22159953403322234823117911 33239930104983352234676867)
            ·
              refine ⟨49859895157475028352015301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33239930104983352234676867 49859895157475028352015301)
              ·
                refine ⟨9348730342026567816002869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49859895157475028352015301 9348730342026567816002869)
                ·
                  refine ⟨876443469564990732750269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9348730342026567816002869 876443469564990732750269)
                  ·
                    refine ⟨328666301086871524781351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 876443469564990732750269 328666301086871524781351)
                    ·
                      rfl

theorem cell22_960113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_960113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960113 prefixEnd_960113 := by exact prefixLift 960113
  have htrace : WordTrace (prefixWord ++ tailWord_960113) baseStart_960113 baseEnd_960113 := by
    simpa [prefixWord, tailWord_960113, baseEnd_960113] using wordTrace_append hprefix tailTrace_960113
  have hstable : (prefixWord ++ tailWord_960113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960113).length < 2 ^ (prefixWord ++ tailWord_960113).sum := by decide
  have hdescent : baseEnd_960113 < baseStart_960113 := by decide
  rcases family_descends (prefixWord ++ tailWord_960113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960136 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 2, 3]
def baseStart_960136 : Nat := 118140960795 + 960136 * 2 ^ 59
def prefixEnd_960136 : Nat := 4983230072969 + 3 ^ 40 * 960136 * 2
def baseEnd_960136 : Nat := 328674174456907131456281

theorem tailTrace_960136 : CollatzResearch.WordTrace tailWord_960136 prefixEnd_960136 328674174456907131456281 := by
  unfold tailWord_960136
  simp only [CollatzResearch.WordTrace]
  refine ⟨17509518424799362509470131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23346024566399150012626841 17509518424799362509470131)
  ·
    refine ⟨26264277637199043764205197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17509518424799362509470131 26264277637199043764205197)
    ·
      refine ⟨9849104113949641411576949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26264277637199043764205197 9849104113949641411576949)
      ·
        refine ⟨923353510682778882335339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9849104113949641411576949 923353510682778882335339)
        ·
          refine ⟨1385030266024168323503009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923353510682778882335339 1385030266024168323503009)
          ·
            refine ⟨1038772699518126242627257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1385030266024168323503009 1038772699518126242627257)
            ·
              refine ⟨779079524638594681970443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1038772699518126242627257 779079524638594681970443)
              ·
                refine ⟨1168619286957892022955665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779079524638594681970443 1168619286957892022955665)
                ·
                  refine ⟨876464465218419017216749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1168619286957892022955665 876464465218419017216749)
                  ·
                    refine ⟨328674174456907131456281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 876464465218419017216749 328674174456907131456281)
                    ·
                      rfl

theorem cell22_960136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_960136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960136 prefixEnd_960136 := by exact prefixLift 960136
  have htrace : WordTrace (prefixWord ++ tailWord_960136) baseStart_960136 baseEnd_960136 := by
    simpa [prefixWord, tailWord_960136, baseEnd_960136] using wordTrace_append hprefix tailTrace_960136
  have hstable : (prefixWord ++ tailWord_960136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960136).length < 2 ^ (prefixWord ++ tailWord_960136).sum := by decide
  have hdescent : baseEnd_960136 < baseStart_960136 := by decide
  rcases family_descends (prefixWord ++ tailWord_960136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960190 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_960190 : Nat := 118140960795 + 960190 * 2 ^ 59
def prefixEnd_960190 : Nat := 4983230072969 + 3 ^ 40 * 960190 * 2
def baseEnd_960190 : Nat := 328692659760468990606115

theorem tailTrace_960190 : CollatzResearch.WordTrace tailWord_960190 prefixEnd_960190 328692659760468990606115 := by
  unfold tailWord_960190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377625798925386530175753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23347337594268728160937349 4377625798925386530175753)
  ·
    refine ⟨3283219349194039897631815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4377625798925386530175753 3283219349194039897631815)
    ·
      refine ⟨4924829023791059846447723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3283219349194039897631815 4924829023791059846447723)
      ·
        refine ⟨7387243535686589769671585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4924829023791059846447723 7387243535686589769671585)
        ·
          refine ⟨5540432651764942327253689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7387243535686589769671585 5540432651764942327253689)
          ·
            refine ⟨4155324488823706745440267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5540432651764942327253689 4155324488823706745440267)
            ·
              refine ⟨6232986733235560118160401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155324488823706745440267 6232986733235560118160401)
              ·
                refine ⟨4674740049926670088620301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6232986733235560118160401 4674740049926670088620301)
                ·
                  refine ⟨1753027518722501283232613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4674740049926670088620301 1753027518722501283232613)
                  ·
                    refine ⟨328692659760468990606115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1753027518722501283232613 328692659760468990606115)
                    ·
                      rfl

theorem cell22_960190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_960190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960190 prefixEnd_960190 := by exact prefixLift 960190
  have htrace : WordTrace (prefixWord ++ tailWord_960190) baseStart_960190 baseEnd_960190 := by
    simpa [prefixWord, tailWord_960190, baseEnd_960190] using wordTrace_append hprefix tailTrace_960190
  have hstable : (prefixWord ++ tailWord_960190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960190).length < 2 ^ (prefixWord ++ tailWord_960190).sum := by decide
  have hdescent : baseEnd_960190 < baseStart_960190 := by decide
  rcases family_descends (prefixWord ++ tailWord_960190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960237 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_960237 : Nat := 118140960795 + 960237 * 2 ^ 59
def prefixEnd_960237 : Nat := 4983230072969 + 3 ^ 40 * 960237 * 2
def baseEnd_960237 : Nat := 328708748820976534680971

theorem tailTrace_960237 : CollatzResearch.WordTrace tailWord_960237 prefixEnd_960237 328708748820976534680971 := by
  unfold tailWord_960237
  simp only [CollatzResearch.WordTrace]
  refine ⟨35022720622232819268366965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23348480414821879512244643 35022720622232819268366965)
  ·
    refine ⟨3283380058334326806409403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35022720622232819268366965 3283380058334326806409403)
    ·
      refine ⟨4925070087501490209614105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3283380058334326806409403 4925070087501490209614105)
      ·
        refine ⟨3693802565626117657210579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4925070087501490209614105 3693802565626117657210579)
        ·
          refine ⟨5540703848439176485815869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3693802565626117657210579 5540703848439176485815869)
          ·
            refine ⟨2077763943164691182180951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5540703848439176485815869 2077763943164691182180951)
            ·
              refine ⟨3116645914747036773271427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077763943164691182180951 3116645914747036773271427)
              ·
                refine ⟨4674968872120555159907141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116645914747036773271427 4674968872120555159907141)
                ·
                  refine ⟨876556663522604092482589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4674968872120555159907141 876556663522604092482589)
                  ·
                    refine ⟨328708748820976534680971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 876556663522604092482589 328708748820976534680971)
                    ·
                      rfl

theorem cell22_960237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_960237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960237 prefixEnd_960237 := by exact prefixLift 960237
  have htrace : WordTrace (prefixWord ++ tailWord_960237) baseStart_960237 baseEnd_960237 := by
    simpa [prefixWord, tailWord_960237, baseEnd_960237] using wordTrace_append hprefix tailTrace_960237
  have hstable : (prefixWord ++ tailWord_960237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960237).length < 2 ^ (prefixWord ++ tailWord_960237).sum := by decide
  have hdescent : baseEnd_960237 < baseStart_960237 := by decide
  rcases family_descends (prefixWord ++ tailWord_960237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960254 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_960254 : Nat := 118140960795 + 960254 * 2 ^ 59
def prefixEnd_960254 : Nat := 4983230072969 + 3 ^ 40 * 960254 * 2
def baseEnd_960254 : Nat := 328714568268394157005919

theorem tailTrace_960254 : CollatzResearch.WordTrace tailWord_960254 prefixEnd_960254 328714568268394157005919 := by
  unfold tailWord_960254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377917582896403896466977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23348893775447487447823877 4377917582896403896466977)
  ·
    refine ⟨3283438187172302922350233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4377917582896403896466977 3283438187172302922350233)
    ·
      refine ⟨2462578640379227191762675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3283438187172302922350233 2462578640379227191762675)
      ·
        refine ⟨3693867960568840787644013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2462578640379227191762675 3693867960568840787644013)
        ·
          refine ⟨1385200485213315295366505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3693867960568840787644013 1385200485213315295366505)
          ·
            refine ⟨1038900363909986471524879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1385200485213315295366505 1038900363909986471524879)
            ·
              refine ⟨1558350545864979707287319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1038900363909986471524879 1558350545864979707287319)
              ·
                refine ⟨2337525818797469560930979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1558350545864979707287319 2337525818797469560930979)
                ·
                  refine ⟨3506288728196204341396469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2337525818797469560930979 3506288728196204341396469)
                  ·
                    refine ⟨328714568268394157005919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3506288728196204341396469 328714568268394157005919)
                    ·
                      rfl

theorem cell22_960254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_960254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960254 prefixEnd_960254 := by exact prefixLift 960254
  have htrace : WordTrace (prefixWord ++ tailWord_960254) baseStart_960254 baseEnd_960254 := by
    simpa [prefixWord, tailWord_960254, baseEnd_960254] using wordTrace_append hprefix tailTrace_960254
  have hstable : (prefixWord ++ tailWord_960254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960254).length < 2 ^ (prefixWord ++ tailWord_960254).sum := by decide
  have hdescent : baseEnd_960254 < baseStart_960254 := by decide
  rcases family_descends (prefixWord ++ tailWord_960254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960286 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_960286 : Nat := 118140960795 + 960286 * 2 ^ 59
def prefixEnd_960286 : Nat := 4983230072969 + 3 ^ 40 * 960286 * 2
def baseEnd_960286 : Nat := 328725522522356740205821

theorem tailTrace_960286 : CollatzResearch.WordTrace tailWord_960286 prefixEnd_960286 328725522522356740205821 := by
  unfold tailWord_960286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4378063474881912579612589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23349671866036867091267141 4378063474881912579612589)
  ·
    refine ⟨1641773803080717217354721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4378063474881912579612589 1641773803080717217354721)
    ·
      refine ⟨1231330352310537913016041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1641773803080717217354721 1231330352310537913016041)
      ·
        refine ⟨923497764232903434762031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1231330352310537913016041 923497764232903434762031)
        ·
          refine ⟨1385246646349355152143047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 923497764232903434762031 1385246646349355152143047)
          ·
            refine ⟨2077869969524032728214571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385246646349355152143047 2077869969524032728214571)
            ·
              refine ⟨3116804954286049092321857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077869969524032728214571 3116804954286049092321857)
              ·
                refine ⟨2337603715714536819241393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3116804954286049092321857 2337603715714536819241393)
                ·
                  refine ⟨1753202786785902614431045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2337603715714536819241393 1753202786785902614431045)
                  ·
                    refine ⟨328725522522356740205821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1753202786785902614431045 328725522522356740205821)
                    ·
                      rfl

theorem cell22_960286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_960286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960286 prefixEnd_960286 := by exact prefixLift 960286
  have htrace : WordTrace (prefixWord ++ tailWord_960286) baseStart_960286 baseEnd_960286 := by
    simpa [prefixWord, tailWord_960286, baseEnd_960286] using wordTrace_append hprefix tailTrace_960286
  have hstable : (prefixWord ++ tailWord_960286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960286).length < 2 ^ (prefixWord ++ tailWord_960286).sum := by decide
  have hdescent : baseEnd_960286 < baseStart_960286 := by decide
  rcases family_descends (prefixWord ++ tailWord_960286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960312 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 5]
def baseStart_960312 : Nat := 118140960795 + 960312 * 2 ^ 59
def prefixEnd_960312 : Nat := 4983230072969 + 3 ^ 40 * 960312 * 2
def baseEnd_960312 : Nat := 109578140951233779685247

theorem tailTrace_960312 : CollatzResearch.WordTrace tailWord_960312 prefixEnd_960312 109578140951233779685247 := by
  unfold tailWord_960312
  simp only [CollatzResearch.WordTrace]
  refine ⟨17512728048480553538673595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23350304064640738051564793 17512728048480553538673595)
  ·
    refine ⟨26269092072720830308010393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17512728048480553538673595 26269092072720830308010393)
    ·
      refine ⟨19701819054540622731007795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26269092072720830308010393 19701819054540622731007795)
      ·
        refine ⟨29552728581810934096511693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19701819054540622731007795 29552728581810934096511693)
        ·
          refine ⟨11082273218179100286191885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29552728581810934096511693 11082273218179100286191885)
          ·
            refine ⟨4155852456817162607321957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11082273218179100286191885 4155852456817162607321957)
            ·
              refine ⟨779222335653217988872867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4155852456817162607321957 779222335653217988872867)
              ·
                refine ⟨1168833503479826983309301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779222335653217988872867 1168833503479826983309301)
                ·
                  refine ⟨109578140951233779685247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1168833503479826983309301 109578140951233779685247)
                  ·
                    rfl

theorem cell22_960312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 5].length) (baseStart_960312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960312 prefixEnd_960312 := by exact prefixLift 960312
  have htrace : WordTrace (prefixWord ++ tailWord_960312) baseStart_960312 baseEnd_960312 := by
    simpa [prefixWord, tailWord_960312, baseEnd_960312] using wordTrace_append hprefix tailTrace_960312
  have hstable : (prefixWord ++ tailWord_960312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960312).length < 2 ^ (prefixWord ++ tailWord_960312).sum := by decide
  have hdescent : baseEnd_960312 < baseStart_960312 := by decide
  rcases family_descends (prefixWord ++ tailWord_960312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960325 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_960325 : Nat := 118140960795 + 960325 * 2 ^ 59
def prefixEnd_960325 : Nat := 4983230072969 + 3 ^ 40 * 960325 * 2
def baseEnd_960325 : Nat := 328738873019373638480701

theorem tailTrace_960325 : CollatzResearch.WordTrace tailWord_960325 prefixEnd_960325 328738873019373638480701 := by
  unfold tailWord_960325
  simp only [CollatzResearch.WordTrace]
  refine ⟨35025930245914010297570429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23350620163942673531713619 35025930245914010297570429)
  ·
    refine ⟨13134723842217753861588911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35025930245914010297570429 13134723842217753861588911)
    ·
      refine ⟨19702085763326630792383367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13134723842217753861588911 19702085763326630792383367)
      ·
        refine ⟨29553128644989946188575051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19702085763326630792383367 29553128644989946188575051)
        ·
          refine ⟨44329692967484919282862577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29553128644989946188575051 44329692967484919282862577)
          ·
            refine ⟨33247269725613689462146933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44329692967484919282862577 33247269725613689462146933)
            ·
              refine ⟨3116931536776283387076275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33247269725613689462146933 3116931536776283387076275)
              ·
                refine ⟨4675397305164425080614413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116931536776283387076275 4675397305164425080614413)
                ·
                  refine ⟨1753273989436659405230405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4675397305164425080614413 1753273989436659405230405)
                  ·
                    refine ⟨328738873019373638480701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1753273989436659405230405 328738873019373638480701)
                    ·
                      rfl

theorem cell22_960325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_960325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960325 prefixEnd_960325 := by exact prefixLift 960325
  have htrace : WordTrace (prefixWord ++ tailWord_960325) baseStart_960325 baseEnd_960325 := by
    simpa [prefixWord, tailWord_960325, baseEnd_960325] using wordTrace_append hprefix tailTrace_960325
  have hstable : (prefixWord ++ tailWord_960325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960325).length < 2 ^ (prefixWord ++ tailWord_960325).sum := by decide
  have hdescent : baseEnd_960325 < baseStart_960325 := by decide
  rcases family_descends (prefixWord ++ tailWord_960325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960370 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_960370 : Nat := 118140960795 + 960370 * 2 ^ 59
def prefixEnd_960370 : Nat := 4983230072969 + 3 ^ 40 * 960370 * 2
def baseEnd_960370 : Nat := 328754277439008521105563

theorem tailTrace_960370 : CollatzResearch.WordTrace tailWord_960370 prefixEnd_960370 328754277439008521105563 := by
  unfold tailWord_960370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8756892882687745745739641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23351714353833988655305709 8756892882687745745739641)
  ·
    refine ⟨6567669662015809309304731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8756892882687745745739641 6567669662015809309304731)
    ·
      refine ⟨9851504493023713963957097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6567669662015809309304731 9851504493023713963957097)
      ·
        refine ⟨7388628369767785472967823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9851504493023713963957097 7388628369767785472967823)
        ·
          refine ⟨11082942554651678209451735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7388628369767785472967823 11082942554651678209451735)
          ·
            refine ⟨16624413831977517314177603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11082942554651678209451735 16624413831977517314177603)
            ·
              refine ⟨24936620747966275971266405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16624413831977517314177603 24936620747966275971266405)
              ·
                refine ⟨4675616390243676744612451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24936620747966275971266405 4675616390243676744612451)
                ·
                  refine ⟨7013424585365515116918677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675616390243676744612451 7013424585365515116918677)
                  ·
                    refine ⟨328754277439008521105563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7013424585365515116918677 328754277439008521105563)
                    ·
                      rfl

theorem cell22_960370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_960370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960370 prefixEnd_960370 := by exact prefixLift 960370
  have htrace : WordTrace (prefixWord ++ tailWord_960370) baseStart_960370 baseEnd_960370 := by
    simpa [prefixWord, tailWord_960370, baseEnd_960370] using wordTrace_append hprefix tailTrace_960370
  have hstable : (prefixWord ++ tailWord_960370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960370).length < 2 ^ (prefixWord ++ tailWord_960370).sum := by decide
  have hdescent : baseEnd_960370 < baseStart_960370 := by decide
  rcases family_descends (prefixWord ++ tailWord_960370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960374 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_960374 : Nat := 118140960795 + 960374 * 2 ^ 59
def prefixEnd_960374 : Nat := 4983230072969 + 3 ^ 40 * 960374 * 2
def baseEnd_960374 : Nat := 109585215573584614668517

theorem tailTrace_960374 : CollatzResearch.WordTrace tailWord_960374 prefixEnd_960374 109585215573584614668517 := by
  unfold tailWord_960374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2189232338921030729131511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23351811615157661110736117 2189232338921030729131511)
  ·
    refine ⟨3283848508381546093697267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2189232338921030729131511 3283848508381546093697267)
    ·
      refine ⟨4925772762572319140545901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3283848508381546093697267 4925772762572319140545901)
      ·
        refine ⟨1847164785964619677704713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4925772762572319140545901 1847164785964619677704713)
        ·
          refine ⟨1385373589473464758278535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1847164785964619677704713 1385373589473464758278535)
          ·
            refine ⟨2078060384210197137417803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385373589473464758278535 2078060384210197137417803)
            ·
              refine ⟨3117090576315295706126705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078060384210197137417803 3117090576315295706126705)
              ·
                refine ⟨2337817932236471779595029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3117090576315295706126705 2337817932236471779595029)
                ·
                  refine ⟨109585215573584614668517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2337817932236471779595029 109585215573584614668517)
                  ·
                    rfl

theorem cell22_960374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_960374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960374 prefixEnd_960374 := by exact prefixLift 960374
  have htrace : WordTrace (prefixWord ++ tailWord_960374) baseStart_960374 baseEnd_960374 := by
    simpa [prefixWord, tailWord_960374, baseEnd_960374] using wordTrace_append hprefix tailTrace_960374
  have hstable : (prefixWord ++ tailWord_960374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960374).length < 2 ^ (prefixWord ++ tailWord_960374).sum := by decide
  have hdescent : baseEnd_960374 < baseStart_960374 := by decide
  rcases family_descends (prefixWord ++ tailWord_960374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960387 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 2, 4]
def baseStart_960387 : Nat := 118140960795 + 960387 * 2 ^ 59
def prefixEnd_960387 : Nat := 4983230072969 + 3 ^ 40 * 960387 * 2
def baseEnd_960387 : Nat := 328760096886426143430511

theorem tailTrace_960387 : CollatzResearch.WordTrace tailWord_960387 prefixEnd_960387 328760096886426143430511 := by
  unfold tailWord_960387
  simp only [CollatzResearch.WordTrace]
  refine ⟨35028191571689394886327415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23352127714459596590884943 35028191571689394886327415)
  ·
    refine ⟨52542287357534092329491123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35028191571689394886327415 52542287357534092329491123)
    ·
      refine ⟨78813431036301138494236685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52542287357534092329491123 78813431036301138494236685)
      ·
        refine ⟨29555036638612926935338757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78813431036301138494236685 29555036638612926935338757)
        ·
          refine ⟨5541569369739923800376017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29555036638612926935338757 5541569369739923800376017)
          ·
            refine ⟨4156177027304942850282013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5541569369739923800376017 4156177027304942850282013)
            ·
              refine ⟨1558566385239353568855755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4156177027304942850282013 1558566385239353568855755)
              ·
                refine ⟨2337849577859030353283633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1558566385239353568855755 2337849577859030353283633)
                ·
                  refine ⟨1753387183394272764962725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2337849577859030353283633 1753387183394272764962725)
                  ·
                    refine ⟨328760096886426143430511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1753387183394272764962725 328760096886426143430511)
                    ·
                      rfl

theorem cell22_960387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 4].length) (baseStart_960387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960387 prefixEnd_960387 := by exact prefixLift 960387
  have htrace : WordTrace (prefixWord ++ tailWord_960387) baseStart_960387 baseEnd_960387 := by
    simpa [prefixWord, tailWord_960387, baseEnd_960387] using wordTrace_append hprefix tailTrace_960387
  have hstable : (prefixWord ++ tailWord_960387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960387).length < 2 ^ (prefixWord ++ tailWord_960387).sum := by decide
  have hdescent : baseEnd_960387 < baseStart_960387 := by decide
  rcases family_descends (prefixWord ++ tailWord_960387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960402 : List Nat := [3, 2, 3, 2, 1, 2, 9]
def baseStart_960402 : Nat := 118140960795 + 960402 * 2 ^ 59
def prefixEnd_960402 : Nat := 4983230072969 + 3 ^ 40 * 960402 * 2
def baseEnd_960402 : Nat := 12176490062702633492795

theorem tailTrace_960402 : CollatzResearch.WordTrace tailWord_960402 prefixEnd_960402 12176490062702633492795 := by
  unfold tailWord_960402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8757184666658763112030865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23352492444423368298748973 8757184666658763112030865)
  ·
    refine ⟨6567888499994072334023149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8757184666658763112030865 6567888499994072334023149)
    ·
      refine ⟨2462958187497777125258681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6567888499994072334023149 2462958187497777125258681)
      ·
        refine ⟨1847218640623332843944011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2462958187497777125258681 1847218640623332843944011)
        ·
          refine ⟨2770827960934999265916017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1847218640623332843944011 2770827960934999265916017)
          ·
            refine ⟨2078120970701249449437013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2770827960934999265916017 2078120970701249449437013)
            ·
              refine ⟨12176490062702633492795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2078120970701249449437013 12176490062702633492795)
              ·
                rfl

theorem cell22_960402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 9].length) (baseStart_960402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960402 prefixEnd_960402 := by exact prefixLift 960402
  have htrace : WordTrace (prefixWord ++ tailWord_960402) baseStart_960402 baseEnd_960402 := by
    simpa [prefixWord, tailWord_960402, baseEnd_960402] using wordTrace_append hprefix tailTrace_960402
  have hstable : (prefixWord ++ tailWord_960402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960402).length < 2 ^ (prefixWord ++ tailWord_960402).sum := by decide
  have hdescent : baseEnd_960402 < baseStart_960402 := by decide
  rcases family_descends (prefixWord ++ tailWord_960402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960468 : List Nat := [2, 4, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_960468 : Nat := 118140960795 + 960468 * 2 ^ 59
def prefixEnd_960468 : Nat := 4983230072969 + 3 ^ 40 * 960468 * 2
def baseEnd_960468 : Nat := 328787824841768932155263

theorem tailTrace_960468 : CollatzResearch.WordTrace tailWord_960468 prefixEnd_960468 328787824841768932155263 := by
  unfold tailWord_960468
  simp only [CollatzResearch.WordTrace]
  refine ⟨17515572942197972860013029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23354097256263963813350705 17515572942197972860013029)
  ·
    refine ⟨3284169926662119911252443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17515572942197972860013029 3284169926662119911252443)
    ·
      refine ⟨4926254889993179866878665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284169926662119911252443 4926254889993179866878665)
      ·
        refine ⟨3694691167494884900158999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4926254889993179866878665 3694691167494884900158999)
        ·
          refine ⟨5542036751242327350238499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3694691167494884900158999 5542036751242327350238499)
          ·
            refine ⟨8313055126863491025357749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5542036751242327350238499 8313055126863491025357749)
            ·
              refine ⟨779348918143452283627289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8313055126863491025357749 779348918143452283627289)
              ·
                refine ⟨584511688607589212720467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 779348918143452283627289 584511688607589212720467)
                ·
                  refine ⟨876767532911383819080701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584511688607589212720467 876767532911383819080701)
                  ·
                    refine ⟨328787824841768932155263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 876767532911383819080701 328787824841768932155263)
                    ·
                      rfl

theorem cell22_960468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_960468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960468 prefixEnd_960468 := by exact prefixLift 960468
  have htrace : WordTrace (prefixWord ++ tailWord_960468) baseStart_960468 baseEnd_960468 := by
    simpa [prefixWord, tailWord_960468, baseEnd_960468] using wordTrace_append hprefix tailTrace_960468
  have hstable : (prefixWord ++ tailWord_960468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960468).length < 2 ^ (prefixWord ++ tailWord_960468).sum := by decide
  have hdescent : baseEnd_960468 < baseStart_960468 := by decide
  rcases family_descends (prefixWord ++ tailWord_960468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960494 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_960494 : Nat := 118140960795 + 960494 * 2 ^ 59
def prefixEnd_960494 : Nat := 4983230072969 + 3 ^ 40 * 960494 * 2
def baseEnd_960494 : Nat := 328796725173113531005183

theorem tailTrace_960494 : CollatzResearch.WordTrace tailWord_960494 prefixEnd_960494 328796725173113531005183 := by
  unfold tailWord_960494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379011772787719020059067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23354729454867834773648357 4379011772787719020059067)
  ·
    refine ⟨6568517659181578530088601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4379011772787719020059067 6568517659181578530088601)
    ·
      refine ⟨4926388244386183897566451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6568517659181578530088601 4926388244386183897566451)
      ·
        refine ⟨7389582366579275846349677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4926388244386183897566451 7389582366579275846349677)
        ·
          refine ⟨2771093387467228442381129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7389582366579275846349677 2771093387467228442381129)
          ·
            refine ⟨2078320040600421331785847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2771093387467228442381129 2078320040600421331785847)
            ·
              refine ⟨3117480060900631997678771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078320040600421331785847 3117480060900631997678771)
              ·
                refine ⟨4676220091350947996518157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3117480060900631997678771 4676220091350947996518157)
                ·
                  refine ⟨1753582534256605498694309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4676220091350947996518157 1753582534256605498694309)
                  ·
                    refine ⟨328796725173113531005183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1753582534256605498694309 328796725173113531005183)
                    ·
                      rfl

theorem cell22_960494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_960494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960494 prefixEnd_960494 := by exact prefixLift 960494
  have htrace : WordTrace (prefixWord ++ tailWord_960494) baseStart_960494 baseEnd_960494 := by
    simpa [prefixWord, tailWord_960494, baseEnd_960494] using wordTrace_append hprefix tailTrace_960494
  have hstable : (prefixWord ++ tailWord_960494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960494).length < 2 ^ (prefixWord ++ tailWord_960494).sum := by decide
  have hdescent : baseEnd_960494 < baseStart_960494 := by decide
  rcases family_descends (prefixWord ++ tailWord_960494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960507 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 6, 3]
def baseStart_960507 : Nat := 118140960795 + 960507 * 2 ^ 59
def prefixEnd_960507 : Nat := 4983230072969 + 3 ^ 40 * 960507 * 2
def baseEnd_960507 : Nat := 328801175338785830430143

theorem tailTrace_960507 : CollatzResearch.WordTrace tailWord_960507 prefixEnd_960507 328801175338785830430143 := by
  unfold tailWord_960507
  simp only [CollatzResearch.WordTrace]
  refine ⟨35032568331254655380695775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23355045554169770253797183 35032568331254655380695775)
  ·
    refine ⟨52548852496881983071043663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35032568331254655380695775 52548852496881983071043663)
    ·
      refine ⟨78823278745322974606565495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52548852496881983071043663 78823278745322974606565495)
      ·
        refine ⟨118234918117984461909848243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78823278745322974606565495 118234918117984461909848243)
        ·
          refine ⟨177352377176976692864772365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118234918117984461909848243 177352377176976692864772365)
          ·
            refine ⟨66507141441366259824289637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177352377176976692864772365 66507141441366259824289637)
            ·
              refine ⟨12470089020256173717054307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66507141441366259824289637 12470089020256173717054307)
              ·
                refine ⟨18705133530384260575581461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12470089020256173717054307 18705133530384260575581461)
                ·
                  refine ⟨876803134236762214480381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18705133530384260575581461 876803134236762214480381)
                  ·
                    refine ⟨328801175338785830430143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 876803134236762214480381 328801175338785830430143)
                    ·
                      rfl

theorem cell22_960507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 3].length) (baseStart_960507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960507 prefixEnd_960507 := by exact prefixLift 960507
  have htrace : WordTrace (prefixWord ++ tailWord_960507) baseStart_960507 baseEnd_960507 := by
    simpa [prefixWord, tailWord_960507, baseEnd_960507] using wordTrace_append hprefix tailTrace_960507
  have hstable : (prefixWord ++ tailWord_960507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960507).length < 2 ^ (prefixWord ++ tailWord_960507).sum := by decide
  have hdescent : baseEnd_960507 < baseStart_960507 := by decide
  rcases family_descends (prefixWord ++ tailWord_960507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960541 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_960541 : Nat := 118140960795 + 960541 * 2 ^ 59
def prefixEnd_960541 : Nat := 4983230072969 + 3 ^ 40 * 960541 * 2
def baseEnd_960541 : Nat := 328812814233621075080039

theorem tailTrace_960541 : CollatzResearch.WordTrace tailWord_960541 prefixEnd_960541 328812814233621075080039 := by
  unfold tailWord_960541
  simp only [CollatzResearch.WordTrace]
  refine ⟨35033808413131479187433477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23355872275420986124955651 35033808413131479187433477)
  ·
    refine ⟨6568839077462152347643777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35033808413131479187433477 6568839077462152347643777)
    ·
      refine ⟨4926629308096614260732833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6568839077462152347643777 4926629308096614260732833)
      ·
        refine ⟨3694971981072460695549625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4926629308096614260732833 3694971981072460695549625)
        ·
          refine ⟨2771228985804345521662219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3694971981072460695549625 2771228985804345521662219)
          ·
            refine ⟨4156843478706518282493329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771228985804345521662219 4156843478706518282493329)
            ·
              refine ⟨3117632609029888711869997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4156843478706518282493329 3117632609029888711869997)
              ·
                refine ⟨1169112228386208266951249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3117632609029888711869997 1169112228386208266951249)
                ·
                  refine ⟨876834171289656200213437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1169112228386208266951249 876834171289656200213437)
                  ·
                    refine ⟨328812814233621075080039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 876834171289656200213437 328812814233621075080039)
                    ·
                      rfl

theorem cell22_960541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_960541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960541 prefixEnd_960541 := by exact prefixLift 960541
  have htrace : WordTrace (prefixWord ++ tailWord_960541) baseStart_960541 baseEnd_960541 := by
    simpa [prefixWord, tailWord_960541, baseEnd_960541] using wordTrace_append hprefix tailTrace_960541
  have hstable : (prefixWord ++ tailWord_960541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960541).length < 2 ^ (prefixWord ++ tailWord_960541).sum := by decide
  have hdescent : baseEnd_960541 < baseStart_960541 := by decide
  rcases family_descends (prefixWord ++ tailWord_960541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960663 : List Nat := [1, 1, 3, 3, 4, 2, 1, 2, 1, 4]
def baseStart_960663 : Nat := 118140960795 + 960663 * 2 ^ 59
def prefixEnd_960663 : Nat := 4983230072969 + 3 ^ 40 * 960663 * 2
def baseEnd_960663 : Nat := 328854577326853423529665

theorem tailTrace_960663 : CollatzResearch.WordTrace tailWord_960663 prefixEnd_960663 328854577326853423529665 := by
  unfold tailWord_960663
  simp only [CollatzResearch.WordTrace]
  refine ⟨35038258118689494023374643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23358838745792996015583095 35038258118689494023374643)
  ·
    refine ⟨52557387178034241035061965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35038258118689494023374643 52557387178034241035061965)
    ·
      refine ⟨19709020191762840388148237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52557387178034241035061965 19709020191762840388148237)
      ·
        refine ⟨7390882571911065145555589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19709020191762840388148237 7390882571911065145555589)
        ·
          refine ⟨1385790482233324714791673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7390882571911065145555589 1385790482233324714791673)
          ·
            refine ⟨1039342861674993536093755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1385790482233324714791673 1039342861674993536093755)
            ·
              refine ⟨1559014292512490304140633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039342861674993536093755 1559014292512490304140633)
              ·
                refine ⟨1169260719384367728105475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559014292512490304140633 1169260719384367728105475)
                ·
                  refine ⟨1753891079076551592158213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169260719384367728105475 1753891079076551592158213)
                  ·
                    refine ⟨328854577326853423529665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1753891079076551592158213 328854577326853423529665)
                    ·
                      rfl

theorem cell22_960663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_960663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960663 prefixEnd_960663 := by exact prefixLift 960663
  have htrace : WordTrace (prefixWord ++ tailWord_960663) baseStart_960663 baseEnd_960663 := by
    simpa [prefixWord, tailWord_960663, baseEnd_960663] using wordTrace_append hprefix tailTrace_960663
  have hstable : (prefixWord ++ tailWord_960663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960663).length < 2 ^ (prefixWord ++ tailWord_960663).sum := by decide
  have hdescent : baseEnd_960663 < baseStart_960663 := by decide
  rcases family_descends (prefixWord ++ tailWord_960663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960676 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_960676 : Nat := 118140960795 + 960676 * 2 ^ 59
def prefixEnd_960676 : Nat := 4983230072969 + 3 ^ 40 * 960676 * 2
def baseEnd_960676 : Nat := 328859027492525722954625

theorem tailTrace_960676 : CollatzResearch.WordTrace tailWord_960676 prefixEnd_960676 328859027492525722954625 := by
  unfold tailWord_960676
  simp only [CollatzResearch.WordTrace]
  refine ⟨17519366133821198621798941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23359154845094931495731921 17519366133821198621798941)
  ·
    refine ⟨6569762300182949483174603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17519366133821198621798941 6569762300182949483174603)
    ·
      refine ⟨9854643450274424224761905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6569762300182949483174603 9854643450274424224761905)
      ·
        refine ⟨7390982587705818168571429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9854643450274424224761905 7390982587705818168571429)
        ·
          refine ⟨1385809235194840906607143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7390982587705818168571429 1385809235194840906607143)
          ·
            refine ⟨2078713852792261359910715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385809235194840906607143 2078713852792261359910715)
            ·
              refine ⟨3118070779188392039866073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078713852792261359910715 3118070779188392039866073)
              ·
                refine ⟨2338553084391294029899555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3118070779188392039866073 2338553084391294029899555)
                ·
                  refine ⟨3507829626586941044849333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2338553084391294029899555 3507829626586941044849333)
                  ·
                    refine ⟨328859027492525722954625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3507829626586941044849333 328859027492525722954625)
                    ·
                      rfl

theorem cell22_960676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_960676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960676 prefixEnd_960676 := by exact prefixLift 960676
  have htrace : WordTrace (prefixWord ++ tailWord_960676) baseStart_960676 baseEnd_960676 := by
    simpa [prefixWord, tailWord_960676, baseEnd_960676] using wordTrace_append hprefix tailTrace_960676
  have hstable : (prefixWord ++ tailWord_960676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960676).length < 2 ^ (prefixWord ++ tailWord_960676).sum := by decide
  have hdescent : baseEnd_960676 < baseStart_960676 := by decide
  rcases family_descends (prefixWord ++ tailWord_960676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960689 : List Nat := [1, 2, 2, 5, 2, 10]
def baseStart_960689 : Nat := 118140960795 + 960689 * 2 ^ 59
def prefixEnd_960689 : Nat := 4983230072969 + 3 ^ 40 * 960689 * 2
def baseEnd_960689 : Nat := 4060042934051827436785

theorem tailTrace_960689 : CollatzResearch.WordTrace tailWord_960689 prefixEnd_960689 4060042934051827436785 := by
  unfold tailWord_960689
  simp only [CollatzResearch.WordTrace]
  refine ⟨35039206416595300463821121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23359470944396866975880747 35039206416595300463821121)
  ·
    refine ⟨26279404812446475347865841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35039206416595300463821121 26279404812446475347865841)
    ·
      refine ⟨19709553609334856510899381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26279404812446475347865841 19709553609334856510899381)
      ·
        refine ⟨1847770650875142797896817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19709553609334856510899381 1847770650875142797896817)
        ·
          refine ⟨1385827988156357098422613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1847770650875142797896817 1385827988156357098422613)
          ·
            refine ⟨4060042934051827436785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1385827988156357098422613 4060042934051827436785)
            ·
              rfl

theorem cell22_960689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 10].length) (baseStart_960689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960689 prefixEnd_960689 := by exact prefixLift 960689
  have htrace : WordTrace (prefixWord ++ tailWord_960689) baseStart_960689 baseEnd_960689 := by
    simpa [prefixWord, tailWord_960689, baseEnd_960689] using wordTrace_append hprefix tailTrace_960689
  have hstable : (prefixWord ++ tailWord_960689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960689).length < 2 ^ (prefixWord ++ tailWord_960689).sum := by decide
  have hdescent : baseEnd_960689 < baseStart_960689 := by decide
  rcases family_descends (prefixWord ++ tailWord_960689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960725 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 2, 4]
def baseStart_960725 : Nat := 118140960795 + 960725 * 2 ^ 59
def prefixEnd_960725 : Nat := 4983230072969 + 3 ^ 40 * 960725 * 2
def baseEnd_960725 : Nat := 328875801193905928479475

theorem tailTrace_960725 : CollatzResearch.WordTrace tailWord_960725 prefixEnd_960725 328875801193905928479475 := by
  unfold tailWord_960725
  simp only [CollatzResearch.WordTrace]
  refine ⟨35040519444464878612131629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23360346296309919074754419 35040519444464878612131629)
  ·
    refine ⟨13140194791674329479549361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35040519444464878612131629 13140194791674329479549361)
    ·
      refine ⟨9855146093755747109662021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13140194791674329479549361 9855146093755747109662021)
      ·
        refine ⟨1847839892579202583061629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9855146093755747109662021 1847839892579202583061629)
        ·
          refine ⟨692939959717200968648111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1847839892579202583061629 692939959717200968648111)
          ·
            refine ⟨1039409939575801452972167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692939959717200968648111 1039409939575801452972167)
            ·
              refine ⟨1559114909363702179458251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039409939575801452972167 1559114909363702179458251)
              ·
                refine ⟨2338672364045553269187377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559114909363702179458251 2338672364045553269187377)
                ·
                  refine ⟨1754004273034164951890533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2338672364045553269187377 1754004273034164951890533)
                  ·
                    refine ⟨328875801193905928479475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1754004273034164951890533 328875801193905928479475)
                    ·
                      rfl

theorem cell22_960725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_960725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960725 prefixEnd_960725 := by exact prefixLift 960725
  have htrace : WordTrace (prefixWord ++ tailWord_960725) baseStart_960725 baseEnd_960725 := by
    simpa [prefixWord, tailWord_960725, baseEnd_960725] using wordTrace_append hprefix tailTrace_960725
  have hstable : (prefixWord ++ tailWord_960725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960725).length < 2 ^ (prefixWord ++ tailWord_960725).sum := by decide
  have hdescent : baseEnd_960725 < baseStart_960725 := by decide
  rcases family_descends (prefixWord ++ tailWord_960725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960751 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 5]
def baseStart_960751 : Nat := 118140960795 + 960751 * 2 ^ 59
def prefixEnd_960751 : Nat := 4983230072969 + 3 ^ 40 * 960751 * 2
def baseEnd_960751 : Nat := 109628233841750175776465

theorem tailTrace_960751 : CollatzResearch.WordTrace tailWord_960751 prefixEnd_960751 109628233841750175776465 := by
  unfold tailWord_960751
  simp only [CollatzResearch.WordTrace]
  refine ⟨35041467742370685052578107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23360978494913790035052071 35041467742370685052578107)
  ·
    refine ⟨52562201613556027578867161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35041467742370685052578107 52562201613556027578867161)
    ·
      refine ⟨39421651210167020684150371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52562201613556027578867161 39421651210167020684150371)
      ·
        refine ⟨59132476815250531026225557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39421651210167020684150371 59132476815250531026225557)
        ·
          refine ⟨2771834850714868641854323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59132476815250531026225557 2771834850714868641854323)
          ·
            refine ⟨4157752276072302962781485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771834850714868641854323 4157752276072302962781485)
            ·
              refine ⟨1559157103527113611043057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4157752276072302962781485 1559157103527113611043057)
              ·
                refine ⟨1169367827645335208282293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559157103527113611043057 1169367827645335208282293)
                ·
                  refine ⟨109628233841750175776465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1169367827645335208282293 109628233841750175776465)
                  ·
                    rfl

theorem cell22_960751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 5].length) (baseStart_960751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960751 prefixEnd_960751 := by exact prefixLift 960751
  have htrace : WordTrace (prefixWord ++ tailWord_960751) baseStart_960751 baseEnd_960751 := by
    simpa [prefixWord, tailWord_960751, baseEnd_960751] using wordTrace_append hprefix tailTrace_960751
  have hstable : (prefixWord ++ tailWord_960751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960751).length < 2 ^ (prefixWord ++ tailWord_960751).sum := by decide
  have hdescent : baseEnd_960751 < baseStart_960751 := by decide
  rcases family_descends (prefixWord ++ tailWord_960751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960766 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_960766 : Nat := 118140960795 + 960766 * 2 ^ 59
def prefixEnd_960766 : Nat := 4983230072969 + 3 ^ 40 * 960766 * 2
def baseEnd_960766 : Nat := 328889836331795488204349

theorem tailTrace_960766 : CollatzResearch.WordTrace tailWord_960766 prefixEnd_960766 328889836331795488204349 := by
  unfold tailWord_960766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4380251854664542826796769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23361343224877561742916101 4380251854664542826796769)
  ·
    refine ⟨3285188890998407120097577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4380251854664542826796769 3285188890998407120097577)
    ·
      refine ⟨2463891668248805340073183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3285188890998407120097577 2463891668248805340073183)
      ·
        refine ⟨3695837502373208010109775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2463891668248805340073183 3695837502373208010109775)
        ·
          refine ⟨5543756253559812015164663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695837502373208010109775 5543756253559812015164663)
          ·
            refine ⟨8315634380339718022746995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5543756253559812015164663 8315634380339718022746995)
            ·
              refine ⟨12473451570509577034120493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8315634380339718022746995 12473451570509577034120493)
              ·
                refine ⟨4677544338941091387795185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12473451570509577034120493 4677544338941091387795185)
                ·
                  refine ⟨3508158254205818540846389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4677544338941091387795185 3508158254205818540846389)
                  ·
                    refine ⟨328889836331795488204349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3508158254205818540846389 328889836331795488204349)
                    ·
                      rfl

theorem cell22_960766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_960766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960766 prefixEnd_960766 := by exact prefixLift 960766
  have htrace : WordTrace (prefixWord ++ tailWord_960766) baseStart_960766 baseEnd_960766 := by
    simpa [prefixWord, tailWord_960766, baseEnd_960766] using wordTrace_append hprefix tailTrace_960766
  have hstable : (prefixWord ++ tailWord_960766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960766).length < 2 ^ (prefixWord ++ tailWord_960766).sum := by decide
  have hdescent : baseEnd_960766 < baseStart_960766 := by decide
  rcases family_descends (prefixWord ++ tailWord_960766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960779 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 6]
def baseStart_960779 : Nat := 118140960795 + 960779 * 2 ^ 59
def prefixEnd_960779 : Nat := 4983230072969 + 3 ^ 40 * 960779 * 2
def baseEnd_960779 : Nat := 109631428832489262543103

theorem tailTrace_960779 : CollatzResearch.WordTrace tailWord_960779 prefixEnd_960779 109631428832489262543103 := by
  unfold tailWord_960779
  simp only [CollatzResearch.WordTrace]
  refine ⟨35042488986269245834597391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23361659324179497223064927 35042488986269245834597391)
  ·
    refine ⟨52563733479403868751896087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35042488986269245834597391 52563733479403868751896087)
    ·
      refine ⟨78845600219105803127844131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52563733479403868751896087 78845600219105803127844131)
      ·
        refine ⟨118268400328658704691766197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78845600219105803127844131 118268400328658704691766197)
        ·
          refine ⟨11087662530811753564853081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118268400328658704691766197 11087662530811753564853081)
          ·
            refine ⟨8315746898108815173639811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11087662530811753564853081 8315746898108815173639811)
            ·
              refine ⟨12473620347163222760459717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8315746898108815173639811 12473620347163222760459717)
              ·
                refine ⟨2338803815093104267586197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12473620347163222760459717 2338803815093104267586197)
                ·
                  refine ⟨109631428832489262543103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2338803815093104267586197 109631428832489262543103)
                  ·
                    rfl

theorem cell22_960779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 6].length) (baseStart_960779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960779 prefixEnd_960779 := by exact prefixLift 960779
  have htrace : WordTrace (prefixWord ++ tailWord_960779) baseStart_960779 baseEnd_960779 := by
    simpa [prefixWord, tailWord_960779, baseEnd_960779] using wordTrace_append hprefix tailTrace_960779
  have hstable : (prefixWord ++ tailWord_960779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960779).length < 2 ^ (prefixWord ++ tailWord_960779).sum := by decide
  have hdescent : baseEnd_960779 < baseStart_960779 := by decide
  rcases family_descends (prefixWord ++ tailWord_960779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960824 : List Nat := [2, 1, 2, 1, 3, 1, 3, 9]
def baseStart_960824 : Nat := 118140960795 + 960824 * 2 ^ 59
def prefixEnd_960824 : Nat := 4983230072969 + 3 ^ 40 * 960824 * 2
def baseEnd_960824 : Nat := 36545521213011407806019

theorem tailTrace_960824 : CollatzResearch.WordTrace tailWord_960824 prefixEnd_960824 36545521213011407806019 := by
  unfold tailWord_960824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17522065135553109259992763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23362753514070812346657017 17522065135553109259992763)
  ·
    refine ⟨26283097703329663889989145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17522065135553109259992763 26283097703329663889989145)
    ·
      refine ⟨19712323277497247917491859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26283097703329663889989145 19712323277497247917491859)
      ·
        refine ⟨29568484916245871876237789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19712323277497247917491859 29568484916245871876237789)
        ·
          refine ⟨11088181843592201953589171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29568484916245871876237789 11088181843592201953589171)
          ·
            refine ⟨16632272765388302930383757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11088181843592201953589171 16632272765388302930383757)
            ·
              refine ⟨6237102287020613598893909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16632272765388302930383757 6237102287020613598893909)
              ·
                refine ⟨36545521213011407806019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6237102287020613598893909 36545521213011407806019)
                ·
                  rfl

theorem cell22_960824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 9].length) (baseStart_960824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960824 prefixEnd_960824 := by exact prefixLift 960824
  have htrace : WordTrace (prefixWord ++ tailWord_960824) baseStart_960824 baseEnd_960824 := by
    simpa [prefixWord, tailWord_960824, baseEnd_960824] using wordTrace_append hprefix tailTrace_960824
  have hstable : (prefixWord ++ tailWord_960824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960824).length < 2 ^ (prefixWord ++ tailWord_960824).sum := by decide
  have hdescent : baseEnd_960824 < baseStart_960824 := by decide
  rcases family_descends (prefixWord ++ tailWord_960824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960828 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 2, 3]
def baseStart_960828 : Nat := 118140960795 + 960828 * 2 ^ 59
def prefixEnd_960828 : Nat := 4983230072969 + 3 ^ 40 * 960828 * 2
def baseEnd_960828 : Nat := 328911060198847993154159

theorem tailTrace_960828 : CollatzResearch.WordTrace tailWord_960828 prefixEnd_960828 328911060198847993154159 := by
  unfold tailWord_960828
  simp only [CollatzResearch.WordTrace]
  refine ⟨17522138081545863601565569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23362850775394484802087425 17522138081545863601565569)
  ·
    refine ⟨13141603561159397701174177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17522138081545863601565569 13141603561159397701174177)
    ·
      refine ⟨9856202670869548275880633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13141603561159397701174177 9856202670869548275880633)
      ·
        refine ⟨7392152003152161206910475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9856202670869548275880633 7392152003152161206910475)
        ·
          refine ⟨11088228004728241810365713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7392152003152161206910475 11088228004728241810365713)
          ·
            refine ⟨8316171003546181357774285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11088228004728241810365713 8316171003546181357774285)
            ·
              refine ⟨3118564126329818009165357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8316171003546181357774285 3118564126329818009165357)
              ·
                refine ⟨1169461547373681753437009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3118564126329818009165357 1169461547373681753437009)
                ·
                  refine ⟨877096160530261315077757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1169461547373681753437009 877096160530261315077757)
                  ·
                    refine ⟨328911060198847993154159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877096160530261315077757 328911060198847993154159)
                    ·
                      rfl

theorem cell22_960828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_960828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960828 prefixEnd_960828 := by exact prefixLift 960828
  have htrace : WordTrace (prefixWord ++ tailWord_960828) baseStart_960828 baseEnd_960828 := by
    simpa [prefixWord, tailWord_960828, baseEnd_960828] using wordTrace_append hprefix tailTrace_960828
  have hstable : (prefixWord ++ tailWord_960828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960828).length < 2 ^ (prefixWord ++ tailWord_960828).sum := by decide
  have hdescent : baseEnd_960828 < baseStart_960828 := by decide
  rcases family_descends (prefixWord ++ tailWord_960828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960856 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 7, 3]
def baseStart_960856 : Nat := 118140960795 + 960856 * 2 ^ 59
def prefixEnd_960856 : Nat := 4983230072969 + 3 ^ 40 * 960856 * 2
def baseEnd_960856 : Nat := 328920645171065253454073

theorem tailTrace_960856 : CollatzResearch.WordTrace tailWord_960856 prefixEnd_960856 328920645171065253454073 := by
  unfold tailWord_960856
  simp only [CollatzResearch.WordTrace]
  refine ⟨17522648703495143992575211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23363531604660191990100281 17522648703495143992575211)
  ·
    refine ⟨26283973055242715988862817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17522648703495143992575211 26283973055242715988862817)
    ·
      refine ⟨19712979791432036991647113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26283973055242715988862817 19712979791432036991647113)
      ·
        refine ⟨14784734843574027743735335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19712979791432036991647113 14784734843574027743735335)
        ·
          refine ⟨22177102265361041615603003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14784734843574027743735335 22177102265361041615603003)
          ·
            refine ⟨33265653398041562423404505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22177102265361041615603003 33265653398041562423404505)
            ·
              refine ⟨24949240048531171817553379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33265653398041562423404505 24949240048531171817553379)
              ·
                refine ⟨37423860072796757726330069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24949240048531171817553379 37423860072796757726330069)
                ·
                  refine ⟨877121720456174009210861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37423860072796757726330069 877121720456174009210861)
                  ·
                    refine ⟨328920645171065253454073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877121720456174009210861 328920645171065253454073)
                    ·
                      rfl

theorem cell22_960856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_960856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960856 prefixEnd_960856 := by exact prefixLift 960856
  have htrace : WordTrace (prefixWord ++ tailWord_960856) baseStart_960856 baseEnd_960856 := by
    simpa [prefixWord, tailWord_960856, baseEnd_960856] using wordTrace_append hprefix tailTrace_960856
  have hstable : (prefixWord ++ tailWord_960856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960856).length < 2 ^ (prefixWord ++ tailWord_960856).sum := by decide
  have hdescent : baseEnd_960856 < baseStart_960856 := by decide
  rcases family_descends (prefixWord ++ tailWord_960856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960871 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 2, 6]
def baseStart_960871 : Nat := 118140960795 + 960871 * 2 ^ 59
def prefixEnd_960871 : Nat := 4983230072969 + 3 ^ 40 * 960871 * 2
def baseEnd_960871 : Nat := 328925779977610214329027

theorem tailTrace_960871 : CollatzResearch.WordTrace tailWord_960871 prefixEnd_960871 328925779977610214329027 := by
  unfold tailWord_960871
  simp only [CollatzResearch.WordTrace]
  refine ⟨35045844501935945546946467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23363896334623963697964311 35045844501935945546946467)
  ·
    refine ⟨52568766752903918320419701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35045844501935945546946467 52568766752903918320419701)
    ·
      refine ⟨4928321883084742342539347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52568766752903918320419701 4928321883084742342539347)
      ·
        refine ⟨7392482824627113513809021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4928321883084742342539347 7392482824627113513809021)
        ·
          refine ⟨2772181059235167567678383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7392482824627113513809021 2772181059235167567678383)
          ·
            refine ⟨4158271588852751351517575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772181059235167567678383 4158271588852751351517575)
            ·
              refine ⟨6237407383279127027276363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158271588852751351517575 6237407383279127027276363)
              ·
                refine ⟨9356111074918690540914545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6237407383279127027276363 9356111074918690540914545)
                ·
                  refine ⟨7017083306189017905685909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9356111074918690540914545 7017083306189017905685909)
                  ·
                    refine ⟨328925779977610214329027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7017083306189017905685909 328925779977610214329027)
                    ·
                      rfl

theorem cell22_960871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_960871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960871 prefixEnd_960871 := by exact prefixLift 960871
  have htrace : WordTrace (prefixWord ++ tailWord_960871) baseStart_960871 baseEnd_960871 := by
    simpa [prefixWord, tailWord_960871, baseEnd_960871] using wordTrace_append hprefix tailTrace_960871
  have hstable : (prefixWord ++ tailWord_960871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960871).length < 2 ^ (prefixWord ++ tailWord_960871).sum := by decide
  have hdescent : baseEnd_960871 < baseStart_960871 := by decide
  rcases family_descends (prefixWord ++ tailWord_960871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960920 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 5]
def baseStart_960920 : Nat := 118140960795 + 960920 * 2 ^ 59
def prefixEnd_960920 : Nat := 4983230072969 + 3 ^ 40 * 960920 * 2
def baseEnd_960920 : Nat := 109647517892996806617959

theorem tailTrace_960920 : CollatzResearch.WordTrace tailWord_960920 prefixEnd_960920 109647517892996806617959 := by
  unfold tailWord_960920
  simp only [CollatzResearch.WordTrace]
  refine ⟨17523815839379213457740107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23365087785838951276986809 17523815839379213457740107)
  ·
    refine ⟨26285723759068820186610161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17523815839379213457740107 26285723759068820186610161)
    ·
      refine ⟨19714292819301615139957621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26285723759068820186610161 19714292819301615139957621)
      ·
        refine ⟨1848214951809526419371027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19714292819301615139957621 1848214951809526419371027)
        ·
          refine ⟨2772322427714289629056541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848214951809526419371027 2772322427714289629056541)
          ·
            refine ⟨1039620910392858610896203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2772322427714289629056541 1039620910392858610896203)
            ·
              refine ⟨1559431365589287916344305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039620910392858610896203 1559431365589287916344305)
              ·
                refine ⟨1169573524191965937258229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559431365589287916344305 1169573524191965937258229)
                ·
                  refine ⟨109647517892996806617959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1169573524191965937258229 109647517892996806617959)
                  ·
                    rfl

theorem cell22_960920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 5].length) (baseStart_960920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960920 prefixEnd_960920 := by exact prefixLift 960920
  have htrace : WordTrace (prefixWord ++ tailWord_960920) baseStart_960920 baseEnd_960920 := by
    simpa [prefixWord, tailWord_960920, baseEnd_960920] using wordTrace_append hprefix tailTrace_960920
  have hstable : (prefixWord ++ tailWord_960920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960920).length < 2 ^ (prefixWord ++ tailWord_960920).sum := by decide
  have hdescent : baseEnd_960920 < baseStart_960920 := by decide
  rcases family_descends (prefixWord ++ tailWord_960920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960931 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 6]
def baseStart_960931 : Nat := 118140960795 + 960931 * 2 ^ 59
def prefixEnd_960931 : Nat := 4983230072969 + 3 ^ 40 * 960931 * 2
def baseEnd_960931 : Nat := 109648773067930019276281

theorem tailTrace_960931 : CollatzResearch.WordTrace tailWord_960931 prefixEnd_960931 109648773067930019276281 := by
  unfold tailWord_960931
  simp only [CollatzResearch.WordTrace]
  refine ⟨35048032881718575794130647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23365355254479050529420431 35048032881718575794130647)
  ·
    refine ⟨52572049322577863691195971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35048032881718575794130647 52572049322577863691195971)
    ·
      refine ⟨78858073983866795536793957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52572049322577863691195971 78858073983866795536793957)
      ·
        refine ⟨14785888871975024163148867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78858073983866795536793957 14785888871975024163148867)
        ·
          refine ⟨22178833307962536244723301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14785888871975024163148867 22178833307962536244723301)
          ·
            refine ⟨4158531245242975545885619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22178833307962536244723301 4158531245242975545885619)
            ·
              refine ⟨6237796867864463318828429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158531245242975545885619 6237796867864463318828429)
              ·
                refine ⟨2339173825449173744560661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6237796867864463318828429 2339173825449173744560661)
                ·
                  refine ⟨109648773067930019276281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2339173825449173744560661 109648773067930019276281)
                  ·
                    rfl

theorem cell22_960931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 6].length) (baseStart_960931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960931 prefixEnd_960931 := by exact prefixLift 960931
  have htrace : WordTrace (prefixWord ++ tailWord_960931) baseStart_960931 baseEnd_960931 := by
    simpa [prefixWord, tailWord_960931, baseEnd_960931] using wordTrace_append hprefix tailTrace_960931
  have hstable : (prefixWord ++ tailWord_960931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960931).length < 2 ^ (prefixWord ++ tailWord_960931).sum := by decide
  have hdescent : baseEnd_960931 < baseStart_960931 := by decide
  rcases family_descends (prefixWord ++ tailWord_960931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960980 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_960980 : Nat := 118140960795 + 960980 * 2 ^ 59
def prefixEnd_960980 : Nat := 4983230072969 + 3 ^ 40 * 960980 * 2
def baseEnd_960980 : Nat := 328963092905170263353693

theorem tailTrace_960980 : CollatzResearch.WordTrace tailWord_960980 prefixEnd_960980 328963092905170263353693 := by
  unfold tailWord_960980
  simp only [CollatzResearch.WordTrace]
  refine ⟨17524910029270528581332197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23366546705694038108442929 17524910029270528581332197)
  ·
    refine ⟨3285920630488224108999787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17524910029270528581332197 3285920630488224108999787)
    ·
      refine ⟨4928880945732336163499681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3285920630488224108999787 4928880945732336163499681)
      ·
        refine ⟨3696660709299252122624761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4928880945732336163499681 3696660709299252122624761)
        ·
          refine ⟨2772495531974439091968571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3696660709299252122624761 2772495531974439091968571)
          ·
            refine ⟨4158743297961658637952857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772495531974439091968571 4158743297961658637952857)
            ·
              refine ⟨3119057473471243978464643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4158743297961658637952857 3119057473471243978464643)
              ·
                refine ⟨4678586210206865967696965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3119057473471243978464643 4678586210206865967696965)
                ·
                  refine ⟨877234914413787368943181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4678586210206865967696965 877234914413787368943181)
                  ·
                    refine ⟨328963092905170263353693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877234914413787368943181 328963092905170263353693)
                    ·
                      rfl

theorem cell22_960980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_960980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960980 prefixEnd_960980 := by exact prefixLift 960980
  have htrace : WordTrace (prefixWord ++ tailWord_960980) baseStart_960980 baseEnd_960980 := by
    simpa [prefixWord, tailWord_960980, baseEnd_960980] using wordTrace_append hprefix tailTrace_960980
  have hstable : (prefixWord ++ tailWord_960980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960980).length < 2 ^ (prefixWord ++ tailWord_960980).sum := by decide
  have hdescent : baseEnd_960980 < baseStart_960980 := by decide
  rcases family_descends (prefixWord ++ tailWord_960980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_960997 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 2, 3]
def baseStart_960997 : Nat := 118140960795 + 960997 * 2 ^ 59
def prefixEnd_960997 : Nat := 4983230072969 + 3 ^ 40 * 960997 * 2
def baseEnd_960997 : Nat := 328968912352587885678641

theorem tailTrace_960997 : CollatzResearch.WordTrace tailWord_960997 prefixEnd_960997 328968912352587885678641 := by
  unfold tailWord_960997
  simp only [CollatzResearch.WordTrace]
  refine ⟨35050440099479469066033245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23366960066319646044022163 35050440099479469066033245)
  ·
    refine ⟨13143915037304800899762467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35050440099479469066033245 13143915037304800899762467)
    ·
      refine ⟨19715872555957201349643701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13143915037304800899762467 19715872555957201349643701)
      ·
        refine ⟨1848363052120987626529097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19715872555957201349643701 1848363052120987626529097)
        ·
          refine ⟨1386272289090740719896823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1848363052120987626529097 1386272289090740719896823)
          ·
            refine ⟨2079408433636111079845235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386272289090740719896823 2079408433636111079845235)
            ·
              refine ⟨3119112650454166619767853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079408433636111079845235 3119112650454166619767853)
              ·
                refine ⟨1169667243920312482412945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3119112650454166619767853 1169667243920312482412945)
                ·
                  refine ⟨877250432940234361809709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1169667243920312482412945 877250432940234361809709)
                  ·
                    refine ⟨328968912352587885678641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877250432940234361809709 328968912352587885678641)
                    ·
                      rfl

theorem cell22_960997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_960997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_960997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_960997 prefixEnd_960997 := by exact prefixLift 960997
  have htrace : WordTrace (prefixWord ++ tailWord_960997) baseStart_960997 baseEnd_960997 := by
    simpa [prefixWord, tailWord_960997, baseEnd_960997] using wordTrace_append hprefix tailTrace_960997
  have hstable : (prefixWord ++ tailWord_960997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_960997).length < 2 ^ (prefixWord ++ tailWord_960997).sum := by decide
  have hdescent : baseEnd_960997 < baseStart_960997 := by decide
  rcases family_descends (prefixWord ++ tailWord_960997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961008 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 5, 3]
def baseStart_961008 : Nat := 118140960795 + 961008 * 2 ^ 59
def prefixEnd_961008 : Nat := 4983230072969 + 3 ^ 40 * 961008 * 2
def baseEnd_961008 : Nat := 328972677877387523653607

theorem tailTrace_961008 : CollatzResearch.WordTrace tailWord_961008 prefixEnd_961008 328972677877387523653607 := by
  unfold tailWord_961008
  simp only [CollatzResearch.WordTrace]
  refine ⟨17525420651219808972341839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23367227534959745296455785 17525420651219808972341839)
  ·
    refine ⟨26288130976829713458512759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17525420651219808972341839 26288130976829713458512759)
    ·
      refine ⟨39432196465244570187769139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26288130976829713458512759 39432196465244570187769139)
      ·
        refine ⟨59148294697866855281653709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39432196465244570187769139 59148294697866855281653709)
        ·
          refine ⟨22180610511700070730620141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59148294697866855281653709 22180610511700070730620141)
          ·
            refine ⟨8317728941887526523982553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22180610511700070730620141 8317728941887526523982553)
            ·
              refine ⟨6238296706415644892986915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8317728941887526523982553 6238296706415644892986915)
              ·
                refine ⟨9357445059623467339480373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6238296706415644892986915 9357445059623467339480373)
                ·
                  refine ⟨877260474339700063076285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9357445059623467339480373 877260474339700063076285)
                  ·
                    refine ⟨328972677877387523653607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877260474339700063076285 328972677877387523653607)
                    ·
                      rfl

theorem cell22_961008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5, 3].length) (baseStart_961008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961008 prefixEnd_961008 := by exact prefixLift 961008
  have htrace : WordTrace (prefixWord ++ tailWord_961008) baseStart_961008 baseEnd_961008 := by
    simpa [prefixWord, tailWord_961008, baseEnd_961008] using wordTrace_append hprefix tailTrace_961008
  have hstable : (prefixWord ++ tailWord_961008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961008).length < 2 ^ (prefixWord ++ tailWord_961008).sum := by decide
  have hdescent : baseEnd_961008 < baseStart_961008 := by decide
  rcases family_descends (prefixWord ++ tailWord_961008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961053 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_961053 : Nat := 118140960795 + 961053 * 2 ^ 59
def prefixEnd_961053 : Nat := 4983230072969 + 3 ^ 40 * 961053 * 2
def baseEnd_961053 : Nat := 328988082297022406278469

theorem tailTrace_961053 : CollatzResearch.WordTrace tailWord_961053 prefixEnd_961053 328988082297022406278469 := by
  unfold tailWord_961053
  simp only [CollatzResearch.WordTrace]
  refine ⟨35052482587276590630071813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23368321724851060420047875 35052482587276590630071813)
  ·
    refine ⟨6572340485114360743138465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35052482587276590630071813 6572340485114360743138465)
    ·
      refine ⟨4929255363835770557353849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6572340485114360743138465 4929255363835770557353849)
      ·
        refine ⟨3696941522876827918015387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4929255363835770557353849 3696941522876827918015387)
        ·
          refine ⟨5545412284315241877023081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696941522876827918015387 5545412284315241877023081)
          ·
            refine ⟨4159059213236431407767311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5545412284315241877023081 4159059213236431407767311)
            ·
              refine ⟨6238588819854647111650967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159059213236431407767311 6238588819854647111650967)
              ·
                refine ⟨9357883229781970667476451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6238588819854647111650967 9357883229781970667476451)
                ·
                  refine ⟨14036824844672956001214677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9357883229781970667476451 14036824844672956001214677)
                  ·
                    refine ⟨328988082297022406278469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14036824844672956001214677 328988082297022406278469)
                    ·
                      rfl

theorem cell22_961053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_961053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961053 prefixEnd_961053 := by exact prefixLift 961053
  have htrace : WordTrace (prefixWord ++ tailWord_961053) baseStart_961053 baseEnd_961053 := by
    simpa [prefixWord, tailWord_961053, baseEnd_961053] using wordTrace_append hprefix tailTrace_961053
  have hstable : (prefixWord ++ tailWord_961053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961053).length < 2 ^ (prefixWord ++ tailWord_961053).sum := by decide
  have hdescent : baseEnd_961053 < baseStart_961053 := by decide
  rcases family_descends (prefixWord ++ tailWord_961053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961100 : List Nat := [2, 2, 1, 3, 1, 2, 1, 6, 4]
def baseStart_961100 : Nat := 118140960795 + 961100 * 2 ^ 59
def prefixEnd_961100 : Nat := 4983230072969 + 3 ^ 40 * 961100 * 2
def baseEnd_961100 : Nat := 109668057119176650117775

theorem tailTrace_961100 : CollatzResearch.WordTrace tailWord_961100 prefixEnd_961100 109668057119176650117775 := by
  unfold tailWord_961100
  simp only [CollatzResearch.WordTrace]
  refine ⟨17527098409053158828516377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23369464545404211771355169 17527098409053158828516377)
  ·
    refine ⟨13145323806789869121387283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17527098409053158828516377 13145323806789869121387283)
    ·
      refine ⟨19717985710184803682080925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13145323806789869121387283 19717985710184803682080925)
      ·
        refine ⟨7394244641319301380780347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19717985710184803682080925 7394244641319301380780347)
        ·
          refine ⟨11091366961978952071170521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7394244641319301380780347 11091366961978952071170521)
          ·
            refine ⟨8318525221484214053377891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11091366961978952071170521 8318525221484214053377891)
            ·
              refine ⟨12477787832226321080066837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318525221484214053377891 12477787832226321080066837)
              ·
                refine ⟨584896304635608800628133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12477787832226321080066837 584896304635608800628133)
                ·
                  refine ⟨109668057119176650117775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 584896304635608800628133 109668057119176650117775)
                  ·
                    rfl

theorem cell22_961100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_961100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961100 prefixEnd_961100 := by exact prefixLift 961100
  have htrace : WordTrace (prefixWord ++ tailWord_961100) baseStart_961100 baseEnd_961100 := by
    simpa [prefixWord, tailWord_961100, baseEnd_961100] using wordTrace_append hprefix tailTrace_961100
  have hstable : (prefixWord ++ tailWord_961100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961100).length < 2 ^ (prefixWord ++ tailWord_961100).sum := by decide
  have hdescent : baseEnd_961100 < baseStart_961100 := by decide
  rcases family_descends (prefixWord ++ tailWord_961100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961130 : List Nat := [3, 1, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_961130 : Nat := 118140960795 + 961130 * 2 ^ 59
def prefixEnd_961130 : Nat := 4983230072969 + 3 ^ 40 * 961130 * 2
def baseEnd_961130 : Nat := 329014440970619872103233

theorem tailTrace_961130 : CollatzResearch.WordTrace tailWord_961130 prefixEnd_961130 329014440970619872103233 := by
  unfold tailWord_961130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8763822751999408195156211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23370194005331755187083229 8763822751999408195156211)
  ·
    refine ⟨13145734127999112292734317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8763822751999408195156211 13145734127999112292734317)
    ·
      refine ⟨4929650297999667109775369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13145734127999112292734317 4929650297999667109775369)
      ·
        refine ⟨3697237723499750332331527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4929650297999667109775369 3697237723499750332331527)
        ·
          refine ⟨5545856585249625498497291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3697237723499750332331527 5545856585249625498497291)
          ·
            refine ⟨8318784877874438247745937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545856585249625498497291 8318784877874438247745937)
            ·
              refine ⟨6239088658405828685809453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318784877874438247745937 6239088658405828685809453)
              ·
                refine ⟨2339658246902185757178545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6239088658405828685809453 2339658246902185757178545)
                ·
                  refine ⟨1754743685176639317883909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2339658246902185757178545 1754743685176639317883909)
                  ·
                    refine ⟨329014440970619872103233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1754743685176639317883909 329014440970619872103233)
                    ·
                      rfl

theorem cell22_961130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_961130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961130 prefixEnd_961130 := by exact prefixLift 961130
  have htrace : WordTrace (prefixWord ++ tailWord_961130) baseStart_961130 baseEnd_961130 := by
    simpa [prefixWord, tailWord_961130, baseEnd_961130] using wordTrace_append hprefix tailTrace_961130
  have hstable : (prefixWord ++ tailWord_961130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961130).length < 2 ^ (prefixWord ++ tailWord_961130).sum := by decide
  have hdescent : baseEnd_961130 < baseStart_961130 := by decide
  rcases family_descends (prefixWord ++ tailWord_961130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961134 : List Nat := [4, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_961134 : Nat := 118140960795 + 961134 * 2 ^ 59
def prefixEnd_961134 : Nat := 4983230072969 + 3 ^ 40 * 961134 * 2
def baseEnd_961134 : Nat := 109671936750788398334407

theorem tailTrace_961134 : CollatzResearch.WordTrace tailWord_961134 prefixEnd_961134 109671936750788398334407 := by
  unfold tailWord_961134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4381929612497892682971307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23370291266655427642513637 4381929612497892682971307)
  ·
    refine ⟨6572894418746839024456961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4381929612497892682971307 6572894418746839024456961)
    ·
      refine ⟨4929670814060129268342721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6572894418746839024456961 4929670814060129268342721)
      ·
        refine ⟨3697253110545096951257041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4929670814060129268342721 3697253110545096951257041)
        ·
          refine ⟨2772939832908822713442781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3697253110545096951257041 2772939832908822713442781)
          ·
            refine ⟨1039852437340808517541043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2772939832908822713442781 1039852437340808517541043)
            ·
              refine ⟨1559778656011212776311565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1039852437340808517541043 1559778656011212776311565)
              ·
                refine ⟨584916996004204791116837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1559778656011212776311565 584916996004204791116837)
                ·
                  refine ⟨109671936750788398334407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 584916996004204791116837 109671936750788398334407)
                  ·
                    rfl

theorem cell22_961134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_961134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961134 prefixEnd_961134 := by exact prefixLift 961134
  have htrace : WordTrace (prefixWord ++ tailWord_961134) baseStart_961134 baseEnd_961134 := by
    simpa [prefixWord, tailWord_961134, baseEnd_961134] using wordTrace_append hprefix tailTrace_961134
  have hstable : (prefixWord ++ tailWord_961134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961134).length < 2 ^ (prefixWord ++ tailWord_961134).sum := by decide
  have hdescent : baseEnd_961134 < baseStart_961134 := by decide
  rcases family_descends (prefixWord ++ tailWord_961134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961207 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 5]
def baseStart_961207 : Nat := 118140960795 + 961207 * 2 ^ 59
def prefixEnd_961207 : Nat := 4983230072969 + 3 ^ 40 * 961207 * 2
def baseEnd_961207 : Nat := 109680266548072445975999

theorem tailTrace_961207 : CollatzResearch.WordTrace tailWord_961207 prefixEnd_961207 109680266548072445975999 := by
  unfold tailWord_961207
  simp only [CollatzResearch.WordTrace]
  refine ⟨35058099428718674931177875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23372066285812449954118583 35058099428718674931177875)
  ·
    refine ⟨52587149143078012396766813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35058099428718674931177875 52587149143078012396766813)
    ·
      refine ⟨19720180928654254648787555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52587149143078012396766813 19720180928654254648787555)
      ·
        refine ⟨29580271392981381973181333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19720180928654254648787555 29580271392981381973181333)
        ·
          refine ⟨1386575221546002279992875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29580271392981381973181333 1386575221546002279992875)
          ·
            refine ⟨2079862832319003419989313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386575221546002279992875 2079862832319003419989313)
            ·
              refine ⟨1559897124239252564991985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2079862832319003419989313 1559897124239252564991985)
              ·
                refine ⟨1169922843179439423743989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559897124239252564991985 1169922843179439423743989)
                ·
                  refine ⟨109680266548072445975999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1169922843179439423743989 109680266548072445975999)
                  ·
                    rfl

theorem cell22_961207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 5].length) (baseStart_961207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961207 prefixEnd_961207 := by exact prefixLift 961207
  have htrace : WordTrace (prefixWord ++ tailWord_961207) baseStart_961207 baseEnd_961207 := by
    simpa [prefixWord, tailWord_961207, baseEnd_961207] using wordTrace_append hprefix tailTrace_961207
  have hstable : (prefixWord ++ tailWord_961207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961207).length < 2 ^ (prefixWord ++ tailWord_961207).sum := by decide
  have hdescent : baseEnd_961207 < baseStart_961207 := by decide
  rcases family_descends (prefixWord ++ tailWord_961207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961252 : List Nat := [2, 3, 1, 1, 1, 4, 1, 5, 4]
def baseStart_961252 : Nat := 118140960795 + 961252 * 2 ^ 59
def prefixEnd_961252 : Nat := 4983230072969 + 3 ^ 40 * 961252 * 2
def baseEnd_961252 : Nat := 109685401354617406850953

theorem tailTrace_961252 : CollatzResearch.WordTrace tailWord_961252 prefixEnd_961252 109685401354617406850953 := by
  unfold tailWord_961252
  simp only [CollatzResearch.WordTrace]
  refine ⟨17529870356777823808283005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23373160475703765077710673 17529870356777823808283005)
  ·
    refine ⟨6573701383791683928106127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17529870356777823808283005 6573701383791683928106127)
    ·
      refine ⟨9860552075687525892159191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6573701383791683928106127 9860552075687525892159191)
      ·
        refine ⟨14790828113531288838238787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9860552075687525892159191 14790828113531288838238787)
        ·
          refine ⟨22186242170296933257358181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14790828113531288838238787 22186242170296933257358181)
          ·
            refine ⟨4159920406930674985754659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22186242170296933257358181 4159920406930674985754659)
            ·
              refine ⟨6239880610396012478631989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159920406930674985754659 6239880610396012478631989)
              ·
                refine ⟨584988807224626169871749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6239880610396012478631989 584988807224626169871749)
                ·
                  refine ⟨109685401354617406850953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 584988807224626169871749 109685401354617406850953)
                  ·
                    rfl

theorem cell22_961252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_961252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961252 prefixEnd_961252 := by exact prefixLift 961252
  have htrace : WordTrace (prefixWord ++ tailWord_961252) baseStart_961252 baseEnd_961252 := by
    simpa [prefixWord, tailWord_961252, baseEnd_961252] using wordTrace_append hprefix tailTrace_961252
  have hstable : (prefixWord ++ tailWord_961252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961252).length < 2 ^ (prefixWord ++ tailWord_961252).sum := by decide
  have hdescent : baseEnd_961252 < baseStart_961252 := by decide
  rcases family_descends (prefixWord ++ tailWord_961252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961265 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 4, 4]
def baseStart_961265 : Nat := 118140960795 + 961265 * 2 ^ 59
def prefixEnd_961265 : Nat := 4983230072969 + 3 ^ 40 * 961265 * 2
def baseEnd_961265 : Nat := 329060654229524519977819

theorem tailTrace_961265 : CollatzResearch.WordTrace tailWord_961265 prefixEnd_961265 329060654229524519977819 := by
  unfold tailWord_961265
  simp only [CollatzResearch.WordTrace]
  refine ⟨35060214862508550836789249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23373476575005700557859499 35060214862508550836789249)
  ·
    refine ⟨26295161146881413127591937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35060214862508550836789249 26295161146881413127591937)
    ·
      refine ⟨19721370860161059845693953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26295161146881413127591937 19721370860161059845693953)
      ·
        refine ⟨14791028145120794884270465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19721370860161059845693953 14791028145120794884270465)
        ·
          refine ⟨11093271108840596163202849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14791028145120794884270465 11093271108840596163202849)
          ·
            refine ⟨8319953331630447122402137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11093271108840596163202849 8319953331630447122402137)
            ·
              refine ⟨6239964998722835341801603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8319953331630447122402137 6239964998722835341801603)
              ·
                refine ⟨9359947498084253012702405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239964998722835341801603 9359947498084253012702405)
                ·
                  refine ⟨1754990155890797439881701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9359947498084253012702405 1754990155890797439881701)
                  ·
                    refine ⟨329060654229524519977819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1754990155890797439881701 329060654229524519977819)
                    ·
                      rfl

theorem cell22_961265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_961265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961265 prefixEnd_961265 := by exact prefixLift 961265
  have htrace : WordTrace (prefixWord ++ tailWord_961265) baseStart_961265 baseEnd_961265 := by
    simpa [prefixWord, tailWord_961265, baseEnd_961265] using wordTrace_append hprefix tailTrace_961265
  have hstable : (prefixWord ++ tailWord_961265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961265).length < 2 ^ (prefixWord ++ tailWord_961265).sum := by decide
  have hdescent : baseEnd_961265 < baseStart_961265 := by decide
  rcases family_descends (prefixWord ++ tailWord_961265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961282 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_961282 : Nat := 118140960795 + 961282 * 2 ^ 59
def prefixEnd_961282 : Nat := 4983230072969 + 3 ^ 40 * 961282 * 2
def baseEnd_961282 : Nat := 329066473676942142302767

theorem tailTrace_961282 : CollatzResearch.WordTrace tailWord_961282 prefixEnd_961282 329066473676942142302767 := by
  unfold tailWord_961282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8765208725861740685039525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23373889935631308493438733 8765208725861740685039525)
  ·
    refine ⟨1643476636099076378444911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8765208725861740685039525 1643476636099076378444911)
    ·
      refine ⟨2465214954148614567667367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1643476636099076378444911 2465214954148614567667367)
      ·
        refine ⟨3697822431222921851501051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465214954148614567667367 3697822431222921851501051)
        ·
          refine ⟨5546733646834382777251577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3697822431222921851501051 5546733646834382777251577)
          ·
            refine ⟨4160050235125787082938683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5546733646834382777251577 4160050235125787082938683)
            ·
              refine ⟨6240075352688680624408025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4160050235125787082938683 6240075352688680624408025)
              ·
                refine ⟨4680056514516510468306019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6240075352688680624408025 4680056514516510468306019)
                ·
                  refine ⟨7020084771774765702459029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680056514516510468306019 7020084771774765702459029)
                  ·
                    refine ⟨329066473676942142302767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7020084771774765702459029 329066473676942142302767)
                    ·
                      rfl

theorem cell22_961282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_961282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961282 prefixEnd_961282 := by exact prefixLift 961282
  have htrace : WordTrace (prefixWord ++ tailWord_961282) baseStart_961282 baseEnd_961282 := by
    simpa [prefixWord, tailWord_961282, baseEnd_961282] using wordTrace_append hprefix tailTrace_961282
  have hstable : (prefixWord ++ tailWord_961282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961282).length < 2 ^ (prefixWord ++ tailWord_961282).sum := by decide
  have hdescent : baseEnd_961282 < baseStart_961282 := by decide
  rcases family_descends (prefixWord ++ tailWord_961282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961340 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_961340 : Nat := 118140960795 + 961340 * 2 ^ 59
def prefixEnd_961340 : Nat := 4983230072969 + 3 ^ 40 * 961340 * 2
def baseEnd_961340 : Nat := 329086328262249324352589

theorem tailTrace_961340 : CollatzResearch.WordTrace tailWord_961340 prefixEnd_961340 329086328262249324352589 := by
  unfold tailWord_961340
  simp only [CollatzResearch.WordTrace]
  refine ⟨17531475168618419322884737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23375300224824559097179649 17531475168618419322884737)
  ·
    refine ⟨13148606376463814492163553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17531475168618419322884737 13148606376463814492163553)
    ·
      refine ⟨9861454782347860869122665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13148606376463814492163553 9861454782347860869122665)
      ·
        refine ⟨7396091086760895651841999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9861454782347860869122665 7396091086760895651841999)
        ·
          refine ⟨11094136630141343477762999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7396091086760895651841999 11094136630141343477762999)
          ·
            refine ⟨16641204945212015216644499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094136630141343477762999 16641204945212015216644499)
            ·
              refine ⟨24961807417818022824966749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16641204945212015216644499 24961807417818022824966749)
              ·
                refine ⟨9360677781681758559362531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24961807417818022824966749 9360677781681758559362531)
                ·
                  refine ⟨14041016672522637839043797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9360677781681758559362531 14041016672522637839043797)
                  ·
                    refine ⟨329086328262249324352589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14041016672522637839043797 329086328262249324352589)
                    ·
                      rfl

theorem cell22_961340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_961340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961340 prefixEnd_961340 := by exact prefixLift 961340
  have htrace : WordTrace (prefixWord ++ tailWord_961340) baseStart_961340 baseEnd_961340 := by
    simpa [prefixWord, tailWord_961340, baseEnd_961340] using wordTrace_append hprefix tailTrace_961340
  have hstable : (prefixWord ++ tailWord_961340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961340).length < 2 ^ (prefixWord ++ tailWord_961340).sum := by decide
  have hdescent : baseEnd_961340 < baseStart_961340 := by decide
  rcases family_descends (prefixWord ++ tailWord_961340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961402 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 6, 3]
def baseStart_961402 : Nat := 118140960795 + 961402 * 2 ^ 59
def prefixEnd_961402 : Nat := 4983230072969 + 3 ^ 40 * 961402 * 2
def baseEnd_961402 : Nat := 329107552129301829302399

theorem tailTrace_961402 : CollatzResearch.WordTrace tailWord_961402 prefixEnd_961402 329107552129301829302399 := by
  unfold tailWord_961402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8766302915753055808631615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23376807775341482156350973 8766302915753055808631615)
  ·
    refine ⟨13149454373629583712947423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8766302915753055808631615 13149454373629583712947423)
    ·
      refine ⟨19724181560444375569421135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13149454373629583712947423 19724181560444375569421135)
      ·
        refine ⟨29586272340666563354131703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19724181560444375569421135 29586272340666563354131703)
        ·
          refine ⟨44379408510999845031197555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29586272340666563354131703 44379408510999845031197555)
          ·
            refine ⟨66569112766499767546796333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44379408510999845031197555 66569112766499767546796333)
            ·
              refine ⟨24963417287437412830048625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66569112766499767546796333 24963417287437412830048625)
              ·
                refine ⟨18722562965578059622536469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24963417287437412830048625 18722562965578059622536469)
                ·
                  refine ⟨877620139011471544806397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18722562965578059622536469 877620139011471544806397)
                  ·
                    refine ⟨329107552129301829302399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877620139011471544806397 329107552129301829302399)
                    ·
                      rfl

theorem cell22_961402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_961402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961402 prefixEnd_961402 := by exact prefixLift 961402
  have htrace : WordTrace (prefixWord ++ tailWord_961402) baseStart_961402 baseEnd_961402 := by
    simpa [prefixWord, tailWord_961402, baseEnd_961402] using wordTrace_append hprefix tailTrace_961402
  have hstable : (prefixWord ++ tailWord_961402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961402).length < 2 ^ (prefixWord ++ tailWord_961402).sum := by decide
  have hdescent : baseEnd_961402 < baseStart_961402 := by decide
  rcases family_descends (prefixWord ++ tailWord_961402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961417 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 1, 6]
def baseStart_961417 : Nat := 118140960795 + 961417 * 2 ^ 59
def prefixEnd_961417 : Nat := 4983230072969 + 3 ^ 40 * 961417 * 2
def baseEnd_961417 : Nat := 329112686935846790177353

theorem tailTrace_961417 : CollatzResearch.WordTrace tailWord_961417 prefixEnd_961417 329112686935846790177353 := by
  unfold tailWord_961417
  simp only [CollatzResearch.WordTrace]
  refine ⟨35065758757957880796322505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23377172505305253864215003 35065758757957880796322505)
  ·
    refine ⟨26299319068468410597241879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35065758757957880796322505 26299319068468410597241879)
    ·
      refine ⟨39448978602702615895862819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26299319068468410597241879 39448978602702615895862819)
      ·
        refine ⟨59173467904053923843794229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39448978602702615895862819 59173467904053923843794229)
        ·
          refine ⟨5547512616005055360355709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59173467904053923843794229 5547512616005055360355709)
          ·
            refine ⟨2080317231001895760133391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5547512616005055360355709 2080317231001895760133391)
            ·
              refine ⟨3120475846502843640200087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080317231001895760133391 3120475846502843640200087)
              ·
                refine ⟨4680713769754265460300131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120475846502843640200087 4680713769754265460300131)
                ·
                  refine ⟨7021070654631398190450197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680713769754265460300131 7021070654631398190450197)
                  ·
                    refine ⟨329112686935846790177353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7021070654631398190450197 329112686935846790177353)
                    ·
                      rfl

theorem cell22_961417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_961417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961417 prefixEnd_961417 := by exact prefixLift 961417
  have htrace : WordTrace (prefixWord ++ tailWord_961417) baseStart_961417 baseEnd_961417 := by
    simpa [prefixWord, tailWord_961417, baseEnd_961417] using wordTrace_append hprefix tailTrace_961417
  have hstable : (prefixWord ++ tailWord_961417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961417).length < 2 ^ (prefixWord ++ tailWord_961417).sum := by decide
  have hdescent : baseEnd_961417 < baseStart_961417 := by decide
  rcases family_descends (prefixWord ++ tailWord_961417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961436 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 4, 3]
def baseStart_961436 : Nat := 118140960795 + 961436 * 2 ^ 59
def prefixEnd_961436 : Nat := 4983230072969 + 3 ^ 40 * 961436 * 2
def baseEnd_961436 : Nat := 329119191024137073952295

theorem tailTrace_961436 : CollatzResearch.WordTrace tailWord_961436 prefixEnd_961436 329119191024137073952295 := by
  unfold tailWord_961436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17533225872444523520632081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23377634496592698027509441 17533225872444523520632081)
  ·
    refine ⟨13149919404333392640474061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17533225872444523520632081 13149919404333392640474061)
    ·
      refine ⟨4931219776625022240177773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13149919404333392640474061 4931219776625022240177773)
      ·
        refine ⟨1849207416234383340066665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4931219776625022240177773 1849207416234383340066665)
        ·
          refine ⟨1386905562175787505049999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1849207416234383340066665 1386905562175787505049999)
          ·
            refine ⟨2080358343263681257574999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386905562175787505049999 2080358343263681257574999)
            ·
              refine ⟨3120537514895521886362499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080358343263681257574999 3120537514895521886362499)
              ·
                refine ⟨4680806272343282829543749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120537514895521886362499 4680806272343282829543749)
                ·
                  refine ⟨877651176064365530539453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4680806272343282829543749 877651176064365530539453)
                  ·
                    refine ⟨329119191024137073952295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877651176064365530539453 329119191024137073952295)
                    ·
                      rfl

theorem cell22_961436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_961436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961436 prefixEnd_961436 := by exact prefixLift 961436
  have htrace : WordTrace (prefixWord ++ tailWord_961436) baseStart_961436 baseEnd_961436 := by
    simpa [prefixWord, tailWord_961436, baseEnd_961436] using wordTrace_append hprefix tailTrace_961436
  have hstable : (prefixWord ++ tailWord_961436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961436).length < 2 ^ (prefixWord ++ tailWord_961436).sum := by decide
  have hdescent : baseEnd_961436 < baseStart_961436 := by decide
  rcases family_descends (prefixWord ++ tailWord_961436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961453 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_961453 : Nat := 118140960795 + 961453 * 2 ^ 59
def prefixEnd_961453 : Nat := 4983230072969 + 3 ^ 40 * 961453 * 2
def baseEnd_961453 : Nat := 329125010471554696277243

theorem tailTrace_961453 : CollatzResearch.WordTrace tailWord_961453 prefixEnd_961453 329125010471554696277243 := by
  unfold tailWord_961453
  simp only [CollatzResearch.WordTrace]
  refine ⟨35067071785827458944633013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23378047857218305963088675 35067071785827458944633013)
  ·
    refine ⟨3287537979921324276059345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35067071785827458944633013 3287537979921324276059345)
    ·
      refine ⟨2465653484940993207044509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3287537979921324276059345 2465653484940993207044509)
      ·
        refine ⟨924620056852872452641691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2465653484940993207044509 924620056852872452641691)
        ·
          refine ⟨1386930085279308678962537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924620056852872452641691 1386930085279308678962537)
          ·
            refine ⟨1040197563959481509221903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386930085279308678962537 1040197563959481509221903)
            ·
              refine ⟨1560296345939222263832855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040197563959481509221903 1560296345939222263832855)
              ·
                refine ⟨2340444518908833395749283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560296345939222263832855 2340444518908833395749283)
                ·
                  refine ⟨3510666778363250093623925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340444518908833395749283 3510666778363250093623925)
                  ·
                    refine ⟨329125010471554696277243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3510666778363250093623925 329125010471554696277243)
                    ·
                      rfl

theorem cell22_961453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_961453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961453 prefixEnd_961453 := by exact prefixLift 961453
  have htrace : WordTrace (prefixWord ++ tailWord_961453) baseStart_961453 baseEnd_961453 := by
    simpa [prefixWord, tailWord_961453, baseEnd_961453] using wordTrace_append hprefix tailTrace_961453
  have hstable : (prefixWord ++ tailWord_961453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961453).length < 2 ^ (prefixWord ++ tailWord_961453).sum := by decide
  have hdescent : baseEnd_961453 < baseStart_961453 := by decide
  rcases family_descends (prefixWord ++ tailWord_961453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961464 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 3, 3]
def baseStart_961464 : Nat := 118140960795 + 961464 * 2 ^ 59
def prefixEnd_961464 : Nat := 4983230072969 + 3 ^ 40 * 961464 * 2
def baseEnd_961464 : Nat := 329128775996354334252209

theorem tailTrace_961464 : CollatzResearch.WordTrace tailWord_961464 prefixEnd_961464 329128775996354334252209 := by
  unfold tailWord_961464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17533736494393803911641723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23378315325858405215522297 17533736494393803911641723)
  ·
    refine ⟨26300604741590705867462585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17533736494393803911641723 26300604741590705867462585)
    ·
      refine ⟨19725453556193029400596939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26300604741590705867462585 19725453556193029400596939)
      ·
        refine ⟨29588180334289544100895409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19725453556193029400596939 29588180334289544100895409)
        ·
          refine ⟨22191135250717158075671557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29588180334289544100895409 22191135250717158075671557)
          ·
            refine ⟨4160837859509467139188417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22191135250717158075671557 4160837859509467139188417)
            ·
              refine ⟨3120628394632100354391313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4160837859509467139188417 3120628394632100354391313)
              ·
                refine ⟨2340471295974075265793485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120628394632100354391313 2340471295974075265793485)
                ·
                  refine ⟨877676735990278224672557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2340471295974075265793485 877676735990278224672557)
                  ·
                    refine ⟨329128775996354334252209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877676735990278224672557 329128775996354334252209)
                    ·
                      rfl

theorem cell22_961464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_961464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961464 prefixEnd_961464 := by exact prefixLift 961464
  have htrace : WordTrace (prefixWord ++ tailWord_961464) baseStart_961464 baseEnd_961464 := by
    simpa [prefixWord, tailWord_961464, baseEnd_961464] using wordTrace_append hprefix tailTrace_961464
  have hstable : (prefixWord ++ tailWord_961464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961464).length < 2 ^ (prefixWord ++ tailWord_961464).sum := by decide
  have hdescent : baseEnd_961464 < baseStart_961464 := by decide
  rcases family_descends (prefixWord ++ tailWord_961464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961485 : List Nat := [1, 6, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_961485 : Nat := 118140960795 + 961485 * 2 ^ 59
def prefixEnd_961485 : Nat := 4983230072969 + 3 ^ 40 * 961485 * 2
def baseEnd_961485 : Nat := 329135964725517279477145

theorem tailTrace_961485 : CollatzResearch.WordTrace tailWord_961485 prefixEnd_961485 329135964725517279477145 := by
  unfold tailWord_961485
  simp only [CollatzResearch.WordTrace]
  refine ⟨35068238921711528409797909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23378825947807685606531939 35068238921711528409797909)
  ·
    refine ⟨1643823699455227894209277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35068238921711528409797909 1643823699455227894209277)
    ·
      refine ⟨616433887295710460328479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1643823699455227894209277 616433887295710460328479)
      ·
        refine ⟨924650830943565690492719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 616433887295710460328479 924650830943565690492719)
        ·
          refine ⟨1386976246415348535739079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 924650830943565690492719 1386976246415348535739079)
          ·
            refine ⟨2080464369623022803608619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386976246415348535739079 2080464369623022803608619)
            ·
              refine ⟨3120696554434534205412929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2080464369623022803608619 3120696554434534205412929)
              ·
                refine ⟨2340522415825900654059697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3120696554434534205412929 2340522415825900654059697)
                ·
                  refine ⟨1755391811869425490544773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2340522415825900654059697 1755391811869425490544773)
                  ·
                    refine ⟨329135964725517279477145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1755391811869425490544773 329135964725517279477145)
                    ·
                      rfl

theorem cell22_961485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_961485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961485 prefixEnd_961485 := by exact prefixLift 961485
  have htrace : WordTrace (prefixWord ++ tailWord_961485) baseStart_961485 baseEnd_961485 := by
    simpa [prefixWord, tailWord_961485, baseEnd_961485] using wordTrace_append hprefix tailTrace_961485
  have hstable : (prefixWord ++ tailWord_961485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961485).length < 2 ^ (prefixWord ++ tailWord_961485).sum := by decide
  have hdescent : baseEnd_961485 < baseStart_961485 := by decide
  rcases family_descends (prefixWord ++ tailWord_961485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961511 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 5]
def baseStart_961511 : Nat := 118140960795 + 961511 * 2 ^ 59
def prefixEnd_961511 : Nat := 4983230072969 + 3 ^ 40 * 961511 * 2
def baseEnd_961511 : Nat := 109714955018953959442355

theorem tailTrace_961511 : CollatzResearch.WordTrace tailWord_961511 prefixEnd_961511 109714955018953959442355 := by
  unfold tailWord_961511
  simp only [CollatzResearch.WordTrace]
  refine ⟨35069187219617334850244387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23379458146411556566829591 35069187219617334850244387)
  ·
    refine ⟨52603780829426002275366581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35069187219617334850244387 52603780829426002275366581)
    ·
      refine ⟨4931604452758687713315617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52603780829426002275366581 4931604452758687713315617)
      ·
        refine ⟨3698703339569015784986713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4931604452758687713315617 3698703339569015784986713)
        ·
          refine ⟨2774027504676761838740035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3698703339569015784986713 2774027504676761838740035)
          ·
            refine ⟨4161041257015142758110053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774027504676761838740035 4161041257015142758110053)
            ·
              refine ⟨780195235690339267145635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4161041257015142758110053 780195235690339267145635)
              ·
                refine ⟨1170292853535508900718453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780195235690339267145635 1170292853535508900718453)
                ·
                  refine ⟨109714955018953959442355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1170292853535508900718453 109714955018953959442355)
                  ·
                    rfl

theorem cell22_961511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 5].length) (baseStart_961511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961511 prefixEnd_961511 := by exact prefixLift 961511
  have htrace : WordTrace (prefixWord ++ tailWord_961511) baseStart_961511 baseEnd_961511 := by
    simpa [prefixWord, tailWord_961511, baseEnd_961511] using wordTrace_append hprefix tailTrace_961511
  have hstable : (prefixWord ++ tailWord_961511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961511).length < 2 ^ (prefixWord ++ tailWord_961511).sum := by decide
  have hdescent : baseEnd_961511 < baseStart_961511 := by decide
  rcases family_descends (prefixWord ++ tailWord_961511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961541 : List Nat := [1, 3, 1, 1, 2, 3, 5, 1, 1, 4]
def baseStart_961541 : Nat := 118140960795 + 961541 * 2 ^ 59
def prefixEnd_961541 : Nat := 4983230072969 + 3 ^ 40 * 961541 * 2
def baseEnd_961541 : Nat := 329155134669951800076973

theorem tailTrace_961541 : CollatzResearch.WordTrace tailWord_961541 prefixEnd_961541 329155134669951800076973 := by
  unfold tailWord_961541
  simp only [CollatzResearch.WordTrace]
  refine ⟨35070281409508649973836477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23380187606339099982557651 35070281409508649973836477)
  ·
    refine ⟨13151355528565743740188679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35070281409508649973836477 13151355528565743740188679)
    ·
      refine ⟨19727033292848615610283019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13151355528565743740188679 19727033292848615610283019)
      ·
        refine ⟨29590549939272923415424529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19727033292848615610283019 29590549939272923415424529)
        ·
          refine ⟨22192912454454692561568397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29590549939272923415424529 22192912454454692561568397)
          ·
            refine ⟨8322342170420509710588149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22192912454454692561568397 8322342170420509710588149)
            ·
              refine ⟨780219578476922785367639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8322342170420509710588149 780219578476922785367639)
              ·
                refine ⟨1170329367715384178051459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780219578476922785367639 1170329367715384178051459)
                ·
                  refine ⟨1755494051573076267077189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170329367715384178051459 1755494051573076267077189)
                  ·
                    refine ⟨329155134669951800076973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1755494051573076267077189 329155134669951800076973)
                    ·
                      rfl

theorem cell22_961541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_961541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961541 prefixEnd_961541 := by exact prefixLift 961541
  have htrace : WordTrace (prefixWord ++ tailWord_961541) baseStart_961541 baseEnd_961541 := by
    simpa [prefixWord, tailWord_961541, baseEnd_961541] using wordTrace_append hprefix tailTrace_961541
  have hstable : (prefixWord ++ tailWord_961541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961541).length < 2 ^ (prefixWord ++ tailWord_961541).sum := by decide
  have hdescent : baseEnd_961541 < baseStart_961541 := by decide
  rcases family_descends (prefixWord ++ tailWord_961541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961571 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 2, 3]
def baseStart_961571 : Nat := 118140960795 + 961571 * 2 ^ 59
def prefixEnd_961571 : Nat := 4983230072969 + 3 ^ 40 * 961571 * 2
def baseEnd_961571 : Nat := 329165404283041721826881

theorem tailTrace_961571 : CollatzResearch.WordTrace tailWord_961571 prefixEnd_961571 329165404283041721826881 := by
  unfold tailWord_961571
  simp only [CollatzResearch.WordTrace]
  refine ⟨35071375599399965097428567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23380917066266643398285711 35071375599399965097428567)
  ·
    refine ⟨52607063399099947646142851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35071375599399965097428567 52607063399099947646142851)
    ·
      refine ⟨78910595098649921469214277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52607063399099947646142851 78910595098649921469214277)
      ·
        refine ⟨14795736580996860275477677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78910595098649921469214277 14795736580996860275477677)
        ·
          refine ⟨5548401217873822603304129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14795736580996860275477677 5548401217873822603304129)
          ·
            refine ⟨4161300913405366952478097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5548401217873822603304129 4161300913405366952478097)
            ·
              refine ⟨3120975685054025214358573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161300913405366952478097 3120975685054025214358573)
              ·
                refine ⟨1170365881895259455384465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3120975685054025214358573 1170365881895259455384465)
                ·
                  refine ⟨877774411421444591538349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1170365881895259455384465 877774411421444591538349)
                  ·
                    refine ⟨329165404283041721826881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877774411421444591538349 329165404283041721826881)
                    ·
                      rfl

theorem cell22_961571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 3].length) (baseStart_961571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961571 prefixEnd_961571 := by exact prefixLift 961571
  have htrace : WordTrace (prefixWord ++ tailWord_961571) baseStart_961571 baseEnd_961571 := by
    simpa [prefixWord, tailWord_961571, baseEnd_961571] using wordTrace_append hprefix tailTrace_961571
  have hstable : (prefixWord ++ tailWord_961571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961571).length < 2 ^ (prefixWord ++ tailWord_961571).sum := by decide
  have hdescent : baseEnd_961571 < baseStart_961571 := by decide
  rcases family_descends (prefixWord ++ tailWord_961571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961584 : List Nat := [2, 1, 1, 1, 2, 4, 5, 6]
def baseStart_961584 : Nat := 118140960795 + 961584 * 2 ^ 59
def prefixEnd_961584 : Nat := 4983230072969 + 3 ^ 40 * 961584 * 2
def baseEnd_961584 : Nat := 36574428272079335694649

theorem tailTrace_961584 : CollatzResearch.WordTrace tailWord_961584 prefixEnd_961584 36574428272079335694649 := by
  unfold tailWord_961584
  simp only [CollatzResearch.WordTrace]
  refine ⟨17535924874176434158825903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23381233165568578878434537 17535924874176434158825903)
  ·
    refine ⟨26303887311264651238238855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17535924874176434158825903 26303887311264651238238855)
    ·
      refine ⟨39455830966896976857358283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26303887311264651238238855 39455830966896976857358283)
      ·
        refine ⟨59183746450345465286037425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39455830966896976857358283 59183746450345465286037425)
        ·
          refine ⟨44387809837759098964528069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59183746450345465286037425 44387809837759098964528069)
          ·
            refine ⟨8322714344579831055849013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44387809837759098964528069 8322714344579831055849013)
            ·
              refine ⟨780254469804359161485845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8322714344579831055849013 780254469804359161485845)
              ·
                refine ⟨36574428272079335694649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 780254469804359161485845 36574428272079335694649)
                ·
                  rfl

theorem cell22_961584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 6].length) (baseStart_961584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961584 prefixEnd_961584 := by exact prefixLift 961584
  have htrace : WordTrace (prefixWord ++ tailWord_961584) baseStart_961584 baseEnd_961584 := by
    simpa [prefixWord, tailWord_961584, baseEnd_961584] using wordTrace_append hprefix tailTrace_961584
  have hstable : (prefixWord ++ tailWord_961584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961584).length < 2 ^ (prefixWord ++ tailWord_961584).sum := by decide
  have hdescent : baseEnd_961584 < baseStart_961584 := by decide
  rcases family_descends (prefixWord ++ tailWord_961584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961599 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 7, 3]
def baseStart_961599 : Nat := 118140960795 + 961599 * 2 ^ 59
def prefixEnd_961599 : Nat := 4983230072969 + 3 ^ 40 * 961599 * 2
def baseEnd_961599 : Nat := 329174989255258982126795

theorem tailTrace_961599 : CollatzResearch.WordTrace tailWord_961599 prefixEnd_961599 329174989255258982126795 := by
  unfold tailWord_961599
  simp only [CollatzResearch.WordTrace]
  refine ⟨35072396843298525879447851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23381597895532350586298567 35072396843298525879447851)
  ·
    refine ⟨52608595264947788819171777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35072396843298525879447851 52608595264947788819171777)
    ·
      refine ⟨39456446448710841614378833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52608595264947788819171777 39456446448710841614378833)
      ·
        refine ⟨29592334836533131210784125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39456446448710841614378833 29592334836533131210784125)
        ·
          refine ⟨11097125563699924204044047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29592334836533131210784125 11097125563699924204044047)
          ·
            refine ⟨16645688345549886306066071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11097125563699924204044047 16645688345549886306066071)
            ·
              refine ⟨24968532518324829459099107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16645688345549886306066071 24968532518324829459099107)
              ·
                refine ⟨37452798777487244188648661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24968532518324829459099107 37452798777487244188648661)
                ·
                  refine ⟨877799971347357285671453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37452798777487244188648661 877799971347357285671453)
                  ·
                    refine ⟨329174989255258982126795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877799971347357285671453 329174989255258982126795)
                    ·
                      rfl

theorem cell22_961599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 3].length) (baseStart_961599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961599 prefixEnd_961599 := by exact prefixLift 961599
  have htrace : WordTrace (prefixWord ++ tailWord_961599) baseStart_961599 baseEnd_961599 := by
    simpa [prefixWord, tailWord_961599, baseEnd_961599] using wordTrace_append hprefix tailTrace_961599
  have hstable : (prefixWord ++ tailWord_961599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961599).length < 2 ^ (prefixWord ++ tailWord_961599).sum := by decide
  have hdescent : baseEnd_961599 < baseStart_961599 := by decide
  rcases family_descends (prefixWord ++ tailWord_961599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961622 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_961622 : Nat := 118140960795 + 961622 * 2 ^ 59
def prefixEnd_961622 : Nat := 4983230072969 + 3 ^ 40 * 961622 * 2
def baseEnd_961622 : Nat := 329182862625294588801725

theorem tailTrace_961622 : CollatzResearch.WordTrace tailWord_961622 prefixEnd_961622 329182862625294588801725 := by
  unfold tailWord_961622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192077232638450050470945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23382157148143467205023413 2192077232638450050470945)
  ·
    refine ⟨1644057924478837537853209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2192077232638450050470945 1644057924478837537853209)
    ·
      refine ⟨1233043443359128153389907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1644057924478837537853209 1233043443359128153389907)
      ·
        refine ⟨1849565165038692230084861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233043443359128153389907 1849565165038692230084861)
        ·
          refine ⟨693586936889509586281823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1849565165038692230084861 693586936889509586281823)
          ·
            refine ⟨1040380405334264379422735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693586936889509586281823 1040380405334264379422735)
            ·
              refine ⟨1560570608001396569134103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040380405334264379422735 1560570608001396569134103)
              ·
                refine ⟨2340855912002094853701155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560570608001396569134103 2340855912002094853701155)
                ·
                  refine ⟨3511283868003142280551733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2340855912002094853701155 3511283868003142280551733)
                  ·
                    refine ⟨329182862625294588801725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3511283868003142280551733 329182862625294588801725)
                    ·
                      rfl

theorem cell22_961622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_961622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961622 prefixEnd_961622 := by exact prefixLift 961622
  have htrace : WordTrace (prefixWord ++ tailWord_961622) baseStart_961622 baseEnd_961622 := by
    simpa [prefixWord, tailWord_961622, baseEnd_961622] using wordTrace_append hprefix tailTrace_961622
  have hstable : (prefixWord ++ tailWord_961622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961622).length < 2 ^ (prefixWord ++ tailWord_961622).sum := by decide
  have hdescent : baseEnd_961622 < baseStart_961622 := by decide
  rcases family_descends (prefixWord ++ tailWord_961622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961718 : List Nat := [5, 1, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_961718 : Nat := 118140960795 + 961718 * 2 ^ 59
def prefixEnd_961718 : Nat := 4983230072969 + 3 ^ 40 * 961718 * 2
def baseEnd_961718 : Nat := 329215725387182338401431

theorem tailTrace_961718 : CollatzResearch.WordTrace tailWord_961718 prefixEnd_961718 329215725387182338401431 := by
  unfold tailWord_961718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192296070616713075189363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23384491419911606135353205 2192296070616713075189363)
  ·
    refine ⟨3288444105925069612784045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2192296070616713075189363 3288444105925069612784045)
    ·
      refine ⟨1233166539721901104794017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3288444105925069612784045 1233166539721901104794017)
      ·
        refine ⟨924874904791425828595513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1233166539721901104794017 924874904791425828595513)
        ·
          refine ⟨693656178593569371446635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 924874904791425828595513 693656178593569371446635)
          ·
            refine ⟨1040484267890354057169953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693656178593569371446635 1040484267890354057169953)
            ·
              refine ⟨780363200917765542877465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040484267890354057169953 780363200917765542877465)
              ·
                refine ⟨585272400688324157158099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780363200917765542877465 585272400688324157158099)
                ·
                  refine ⟨877908601032486235737149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585272400688324157158099 877908601032486235737149)
                  ·
                    refine ⟨329215725387182338401431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877908601032486235737149 329215725387182338401431)
                    ·
                      rfl

theorem cell22_961718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_961718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961718 prefixEnd_961718 := by exact prefixLift 961718
  have htrace : WordTrace (prefixWord ++ tailWord_961718) baseStart_961718 baseEnd_961718 := by
    simpa [prefixWord, tailWord_961718, baseEnd_961718] using wordTrace_append hprefix tailTrace_961718
  have hstable : (prefixWord ++ tailWord_961718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961718).length < 2 ^ (prefixWord ++ tailWord_961718).sum := by decide
  have hdescent : baseEnd_961718 < baseStart_961718 := by decide
  rcases family_descends (prefixWord ++ tailWord_961718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961721 : List Nat := [1, 2, 1, 4, 1, 3, 2, 2, 2, 4]
def baseStart_961721 : Nat := 118140960795 + 961721 * 2 ^ 59
def prefixEnd_961721 : Nat := 4983230072969 + 3 ^ 40 * 961721 * 2
def baseEnd_961721 : Nat := 329216752348491330576421

theorem tailTrace_961721 : CollatzResearch.WordTrace tailWord_961721 prefixEnd_961721 329216752348491330576421 := by
  unfold tailWord_961721
  simp only [CollatzResearch.WordTrace]
  refine ⟨35076846548856540715389017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23384564365904360476926011 35076846548856540715389017)
  ·
    refine ⟨26307634911642405536541763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35076846548856540715389017 26307634911642405536541763)
    ·
      refine ⟨39461452367463608304812645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26307634911642405536541763 39461452367463608304812645)
      ·
        refine ⟨7399022318899426557152371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39461452367463608304812645 7399022318899426557152371)
        ·
          refine ⟨11098533478349139835728557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399022318899426557152371 11098533478349139835728557)
          ·
            refine ⟨4161950054380927438398209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11098533478349139835728557 4161950054380927438398209)
            ·
              refine ⟨3121462540785695578798657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4161950054380927438398209 3121462540785695578798657)
              ·
                refine ⟨2341096905589271684098993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3121462540785695578798657 2341096905589271684098993)
                ·
                  refine ⟨1755822679191953763074245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2341096905589271684098993 1755822679191953763074245)
                  ·
                    refine ⟨329216752348491330576421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1755822679191953763074245 329216752348491330576421)
                    ·
                      rfl

theorem cell22_961721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_961721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961721 prefixEnd_961721 := by exact prefixLift 961721
  have htrace : WordTrace (prefixWord ++ tailWord_961721) baseStart_961721 baseEnd_961721 := by
    simpa [prefixWord, tailWord_961721, baseEnd_961721] using wordTrace_append hprefix tailTrace_961721
  have hstable : (prefixWord ++ tailWord_961721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961721).length < 2 ^ (prefixWord ++ tailWord_961721).sum := by decide
  have hdescent : baseEnd_961721 < baseStart_961721 := by decide
  rcases family_descends (prefixWord ++ tailWord_961721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961751 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 5, 3]
def baseStart_961751 : Nat := 118140960795 + 961751 * 2 ^ 59
def prefixEnd_961751 : Nat := 4983230072969 + 3 ^ 40 * 961751 * 2
def baseEnd_961751 : Nat := 329227021961581252326329

theorem tailTrace_961751 : CollatzResearch.WordTrace tailWord_961751 prefixEnd_961751 329227021961581252326329 := by
  unfold tailWord_961751
  simp only [CollatzResearch.WordTrace]
  refine ⟨35077940738747855838981107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23385293825831903892654071 35077940738747855838981107)
  ·
    refine ⟨52616911108121783758471661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35077940738747855838981107 52616911108121783758471661)
    ·
      refine ⟨19731341665545668909426873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52616911108121783758471661 19731341665545668909426873)
      ·
        refine ⟨14798506249159251682070155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19731341665545668909426873 14798506249159251682070155)
        ·
          refine ⟨22197759373738877523105233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14798506249159251682070155 22197759373738877523105233)
          ·
            refine ⟨16648319530304158142328925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22197759373738877523105233 16648319530304158142328925)
            ·
              refine ⟨6243119823864059303373347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16648319530304158142328925 6243119823864059303373347)
              ·
                refine ⟨9364679735796088955060021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6243119823864059303373347 9364679735796088955060021)
                ·
                  refine ⟨877938725230883339536877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9364679735796088955060021 877938725230883339536877)
                  ·
                    refine ⟨329227021961581252326329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 877938725230883339536877 329227021961581252326329)
                    ·
                      rfl

theorem cell22_961751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_961751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961751 prefixEnd_961751 := by exact prefixLift 961751
  have htrace : WordTrace (prefixWord ++ tailWord_961751) baseStart_961751 baseEnd_961751 := by
    simpa [prefixWord, tailWord_961751, baseEnd_961751] using wordTrace_append hprefix tailTrace_961751
  have hstable : (prefixWord ++ tailWord_961751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961751).length < 2 ^ (prefixWord ++ tailWord_961751).sum := by decide
  have hdescent : baseEnd_961751 < baseStart_961751 := by decide
  rcases family_descends (prefixWord ++ tailWord_961751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961828 : List Nat := [2, 3, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_961828 : Nat := 118140960795 + 961828 * 2 ^ 59
def prefixEnd_961828 : Nat := 4983230072969 + 3 ^ 40 * 961828 * 2
def baseEnd_961828 : Nat := 329253380635178718151093

theorem tailTrace_961828 : CollatzResearch.WordTrace tailWord_961828 prefixEnd_961828 329253380635178718151093 := by
  unfold tailWord_961828
  simp only [CollatzResearch.WordTrace]
  refine ⟨17540374579734448994767069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23387166106312598659689425 17540374579734448994767069)
  ·
    refine ⟨6577640467400418373037651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17540374579734448994767069 6577640467400418373037651)
    ·
      refine ⟨9866460701100627559556477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6577640467400418373037651 9866460701100627559556477)
      ·
        refine ⟨3699922762912735334833679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9866460701100627559556477 3699922762912735334833679)
        ·
          refine ⟨5549884144369103002250519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3699922762912735334833679 5549884144369103002250519)
          ·
            refine ⟨8324826216553654503375779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5549884144369103002250519 8324826216553654503375779)
            ·
              refine ⟨12487239324830481755063669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8324826216553654503375779 12487239324830481755063669)
              ·
                refine ⟨1170678686702857664537219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12487239324830481755063669 1170678686702857664537219)
                ·
                  refine ⟨1756018030054286496805829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1170678686702857664537219 1756018030054286496805829)
                  ·
                    refine ⟨329253380635178718151093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1756018030054286496805829 329253380635178718151093)
                    ·
                      rfl

theorem cell22_961828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_961828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961828 prefixEnd_961828 := by exact prefixLift 961828
  have htrace : WordTrace (prefixWord ++ tailWord_961828) baseStart_961828 baseEnd_961828 := by
    simpa [prefixWord, tailWord_961828, baseEnd_961828] using wordTrace_append hprefix tailTrace_961828
  have hstable : (prefixWord ++ tailWord_961828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961828).length < 2 ^ (prefixWord ++ tailWord_961828).sum := by decide
  have hdescent : baseEnd_961828 < baseStart_961828 := by decide
  rcases family_descends (prefixWord ++ tailWord_961828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961843 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 6]
def baseStart_961843 : Nat := 118140960795 + 961843 * 2 ^ 59
def prefixEnd_961843 : Nat := 4983230072969 + 3 ^ 40 * 961843 * 2
def baseEnd_961843 : Nat := 109752838480574559675349

theorem tailTrace_961843 : CollatzResearch.WordTrace tailWord_961843 prefixEnd_961843 109752838480574559675349 := by
  unfold tailWord_961843
  simp only [CollatzResearch.WordTrace]
  refine ⟨35081296254414555551330183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23387530836276370367553455 35081296254414555551330183)
  ·
    refine ⟨52621944381621833326995275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35081296254414555551330183 52621944381621833326995275)
    ·
      refine ⟨78932916572432749990492913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52621944381621833326995275 78932916572432749990492913)
      ·
        refine ⟨59199687429324562492869685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78932916572432749990492913 59199687429324562492869685)
        ·
          refine ⟨5549970696499177733706533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59199687429324562492869685 5549970696499177733706533)
          ·
            refine ⟨1040619505593595825069975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5549970696499177733706533 1040619505593595825069975)
            ·
              refine ⟨1560929258390393737604963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040619505593595825069975 1560929258390393737604963)
              ·
                refine ⟨2341393887585590606407445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560929258390393737604963 2341393887585590606407445)
                ·
                  refine ⟨109752838480574559675349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2341393887585590606407445 109752838480574559675349)
                  ·
                    rfl

theorem cell22_961843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 6].length) (baseStart_961843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961843 prefixEnd_961843 := by exact prefixLift 961843
  have htrace : WordTrace (prefixWord ++ tailWord_961843) baseStart_961843 baseEnd_961843 := by
    simpa [prefixWord, tailWord_961843, baseEnd_961843] using wordTrace_append hprefix tailTrace_961843
  have hstable : (prefixWord ++ tailWord_961843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961843).length < 2 ^ (prefixWord ++ tailWord_961843).sum := by decide
  have hdescent : baseEnd_961843 < baseStart_961843 := by decide
  rcases family_descends (prefixWord ++ tailWord_961843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961856 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 4, 4]
def baseStart_961856 : Nat := 118140960795 + 961856 * 2 ^ 59
def prefixEnd_961856 : Nat := 4983230072969 + 3 ^ 40 * 961856 * 2
def baseEnd_961856 : Nat := 329262965607395978451007

theorem tailTrace_961856 : CollatzResearch.WordTrace tailWord_961856 prefixEnd_961856 329262965607395978451007 := by
  unfold tailWord_961856
  simp only [CollatzResearch.WordTrace]
  refine ⟨17540885201683729385776711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23387846935578305847702281 17540885201683729385776711)
  ·
    refine ⟨26311327802525594078665067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17540885201683729385776711 26311327802525594078665067)
    ·
      refine ⟨39466991703788391117997601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26311327802525594078665067 39466991703788391117997601)
      ·
        refine ⟨29600243777841293338498201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39466991703788391117997601 29600243777841293338498201)
        ·
          refine ⟨22200182833380970003873651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29600243777841293338498201 22200182833380970003873651)
          ·
            refine ⟨33300274250071455005810477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22200182833380970003873651 33300274250071455005810477)
            ·
              refine ⟨12487602843776795627178929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33300274250071455005810477 12487602843776795627178929)
              ·
                refine ⟨9365702132832596720384197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12487602843776795627178929 9365702132832596720384197)
                ·
                  refine ⟨1756069149906111885072037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9365702132832596720384197 1756069149906111885072037)
                  ·
                    refine ⟨329262965607395978451007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1756069149906111885072037 329262965607395978451007)
                    ·
                      rfl

theorem cell22_961856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_961856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961856 prefixEnd_961856 := by exact prefixLift 961856
  have htrace : WordTrace (prefixWord ++ tailWord_961856) baseStart_961856 baseEnd_961856 := by
    simpa [prefixWord, tailWord_961856, baseEnd_961856] using wordTrace_append hprefix tailTrace_961856
  have hstable : (prefixWord ++ tailWord_961856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961856).length < 2 ^ (prefixWord ++ tailWord_961856).sum := by decide
  have hdescent : baseEnd_961856 < baseStart_961856 := by decide
  rcases family_descends (prefixWord ++ tailWord_961856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961873 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 2, 4]
def baseStart_961873 : Nat := 118140960795 + 961873 * 2 ^ 59
def prefixEnd_961873 : Nat := 4983230072969 + 3 ^ 40 * 961873 * 2
def baseEnd_961873 : Nat := 329268785054813600775955

theorem tailTrace_961873 : CollatzResearch.WordTrace tailWord_961873 prefixEnd_961873 329268785054813600775955 := by
  unfold tailWord_961873
  simp only [CollatzResearch.WordTrace]
  refine ⟨35082390444305870674922273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23388260296203913783281515 35082390444305870674922273)
  ·
    refine ⟨26311792833229403006191705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35082390444305870674922273 26311792833229403006191705)
    ·
      refine ⟨19733844624922052254643779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26311792833229403006191705 19733844624922052254643779)
      ·
        refine ⟨29600766937383078381965669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19733844624922052254643779 29600766937383078381965669)
        ·
          refine ⟨5550143800759327196618563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29600766937383078381965669 5550143800759327196618563)
          ·
            refine ⟨8325215701138990794927845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550143800759327196618563 8325215701138990794927845)
            ·
              refine ⟨1560977943963560774048971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8325215701138990794927845 1560977943963560774048971)
              ·
                refine ⟨2341466915945341161073457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1560977943963560774048971 2341466915945341161073457)
                ·
                  refine ⟨1756100186959005870805093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2341466915945341161073457 1756100186959005870805093)
                  ·
                    refine ⟨329268785054813600775955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1756100186959005870805093 329268785054813600775955)
                    ·
                      rfl

theorem cell22_961873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_961873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961873 prefixEnd_961873 := by exact prefixLift 961873
  have htrace : WordTrace (prefixWord ++ tailWord_961873) baseStart_961873 baseEnd_961873 := by
    simpa [prefixWord, tailWord_961873, baseEnd_961873] using wordTrace_append hprefix tailTrace_961873
  have hstable : (prefixWord ++ tailWord_961873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961873).length < 2 ^ (prefixWord ++ tailWord_961873).sum := by decide
  have hdescent : baseEnd_961873 < baseStart_961873 := by decide
  rcases family_descends (prefixWord ++ tailWord_961873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961903 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 3, 3]
def baseStart_961903 : Nat := 118140960795 + 961903 * 2 ^ 59
def prefixEnd_961903 : Nat := 4983230072969 + 3 ^ 40 * 961903 * 2
def baseEnd_961903 : Nat := 329279054667903522525863

theorem tailTrace_961903 : CollatzResearch.WordTrace tailWord_961903 prefixEnd_961903 329279054667903522525863 := by
  unfold tailWord_961903
  simp only [CollatzResearch.WordTrace]
  refine ⟨35083484634197185798514363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23388989756131457199009575 35083484634197185798514363)
  ·
    refine ⟨52625226951295778697771545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35083484634197185798514363 52625226951295778697771545)
    ·
      refine ⟨39468920213471834023328659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52625226951295778697771545 39468920213471834023328659)
      ·
        refine ⟨59203380320207751034992989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39468920213471834023328659 59203380320207751034992989)
        ·
          refine ⟨22201267620077906638122371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59203380320207751034992989 22201267620077906638122371)
          ·
            refine ⟨33301901430116859957183557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22201267620077906638122371 33301901430116859957183557)
            ·
              refine ⟨6244106518146911241971917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33301901430116859957183557 6244106518146911241971917)
              ·
                refine ⟨2341539944305091715739469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6244106518146911241971917 2341539944305091715739469)
                ·
                  refine ⟨878077479114409393402301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2341539944305091715739469 878077479114409393402301)
                  ·
                    refine ⟨329279054667903522525863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 878077479114409393402301 329279054667903522525863)
                    ·
                      rfl

theorem cell22_961903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 3].length) (baseStart_961903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961903 prefixEnd_961903 := by exact prefixLift 961903
  have htrace : WordTrace (prefixWord ++ tailWord_961903) baseStart_961903 baseEnd_961903 := by
    simpa [prefixWord, tailWord_961903, baseEnd_961903] using wordTrace_append hprefix tailTrace_961903
  have hstable : (prefixWord ++ tailWord_961903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961903).length < 2 ^ (prefixWord ++ tailWord_961903).sum := by decide
  have hdescent : baseEnd_961903 < baseStart_961903 := by decide
  rcases family_descends (prefixWord ++ tailWord_961903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961922 : List Nat := [3, 4, 2, 1, 1, 2, 3, 6]
def baseStart_961922 : Nat := 118140960795 + 961922 * 2 ^ 59
def prefixEnd_961922 : Nat := 4983230072969 + 3 ^ 40 * 961922 * 2
def baseEnd_961922 : Nat := 36587284306243756255645

theorem tailTrace_961922 : CollatzResearch.WordTrace tailWord_961922 prefixEnd_961922 36587284306243756255645 := by
  unfold tailWord_961922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8771044405282088010864005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23389451747418901362304013 8771044405282088010864005)
  ·
    refine ⟨1644570825990391502037001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8771044405282088010864005 1644570825990391502037001)
    ·
      refine ⟨1233428119492793626527751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1644570825990391502037001 1233428119492793626527751)
      ·
        refine ⟨1850142179239190439791627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1233428119492793626527751 1850142179239190439791627)
        ·
          refine ⟨2775213268858785659687441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850142179239190439791627 2775213268858785659687441)
          ·
            refine ⟨2081409951644089244765581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2775213268858785659687441 2081409951644089244765581)
            ·
              refine ⟨780528731866533466787093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2081409951644089244765581 780528731866533466787093)
              ·
                refine ⟨36587284306243756255645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 780528731866533466787093 36587284306243756255645)
                ·
                  rfl

theorem cell22_961922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_961922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961922 prefixEnd_961922 := by exact prefixLift 961922
  have htrace : WordTrace (prefixWord ++ tailWord_961922) baseStart_961922 baseEnd_961922 := by
    simpa [prefixWord, tailWord_961922, baseEnd_961922] using wordTrace_append hprefix tailTrace_961922
  have hstable : (prefixWord ++ tailWord_961922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961922).length < 2 ^ (prefixWord ++ tailWord_961922).sum := by decide
  have hdescent : baseEnd_961922 < baseStart_961922 := by decide
  rcases family_descends (prefixWord ++ tailWord_961922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961931 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 1, 7]
def baseStart_961931 : Nat := 118140960795 + 961931 * 2 ^ 59
def prefixEnd_961931 : Nat := 4983230072969 + 3 ^ 40 * 961931 * 2
def baseEnd_961931 : Nat := 329288639640120782825777

theorem tailTrace_961931 : CollatzResearch.WordTrace tailWord_961931 prefixEnd_961931 329288639640120782825777 := by
  unfold tailWord_961931
  simp only [CollatzResearch.WordTrace]
  refine ⟨35084505878095746580533647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23389670585397164387022431 35084505878095746580533647)
  ·
    refine ⟨52626758817143619870800471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35084505878095746580533647 52626758817143619870800471)
    ·
      refine ⟨78940138225715429806200707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52626758817143619870800471 78940138225715429806200707)
      ·
        refine ⟨118410207338573144709301061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78940138225715429806200707 118410207338573144709301061)
        ·
          refine ⟨22201913875982464632993949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118410207338573144709301061 22201913875982464632993949)
          ·
            refine ⟨8325717703493424237372731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22201913875982464632993949 8325717703493424237372731)
            ·
              refine ⟨12488576555240136356059097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8325717703493424237372731 12488576555240136356059097)
              ·
                refine ⟨9366432416430102267044323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12488576555240136356059097 9366432416430102267044323)
                ·
                  refine ⟨14049648624645153400566485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9366432416430102267044323 14049648624645153400566485)
                  ·
                    refine ⟨329288639640120782825777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14049648624645153400566485 329288639640120782825777)
                    ·
                      rfl

theorem cell22_961931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_961931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961931 prefixEnd_961931 := by exact prefixLift 961931
  have htrace : WordTrace (prefixWord ++ tailWord_961931) baseStart_961931 baseEnd_961931 := by
    simpa [prefixWord, tailWord_961931, baseEnd_961931] using wordTrace_append hprefix tailTrace_961931
  have hstable : (prefixWord ++ tailWord_961931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961931).length < 2 ^ (prefixWord ++ tailWord_961931).sum := by decide
  have hdescent : baseEnd_961931 < baseStart_961931 := by decide
  rcases family_descends (prefixWord ++ tailWord_961931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961965 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_961965 : Nat := 118140960795 + 961965 * 2 ^ 59
def prefixEnd_961965 : Nat := 4983230072969 + 3 ^ 40 * 961965 * 2
def baseEnd_961965 : Nat := 329300278534956027475673

theorem tailTrace_961965 : CollatzResearch.WordTrace tailWord_961965 prefixEnd_961965 329300278534956027475673 := by
  unfold tailWord_961965
  simp only [CollatzResearch.WordTrace]
  refine ⟨35085745959972570387271349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23390497306648380258180899 35085745959972570387271349)
  ·
    refine ⟨3289288683747428473806689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35085745959972570387271349 3289288683747428473806689)
    ·
      refine ⟨2466966512810571355355017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3289288683747428473806689 2466966512810571355355017)
      ·
        refine ⟨1850224884607928516516263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2466966512810571355355017 1850224884607928516516263)
        ·
          refine ⟨2775337326911892774774395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850224884607928516516263 2775337326911892774774395)
          ·
            refine ⟨4163005990367839162161593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775337326911892774774395 4163005990367839162161593)
            ·
              refine ⟨3122254492775879371621195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4163005990367839162161593 3122254492775879371621195)
              ·
                refine ⟨4683381739163819057431793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122254492775879371621195 4683381739163819057431793)
                ·
                  refine ⟨3512536304372864293073845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4683381739163819057431793 3512536304372864293073845)
                  ·
                    refine ⟨329300278534956027475673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3512536304372864293073845 329300278534956027475673)
                    ·
                      rfl

theorem cell22_961965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_961965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961965 prefixEnd_961965 := by exact prefixLift 961965
  have htrace : WordTrace (prefixWord ++ tailWord_961965) baseStart_961965 baseEnd_961965 := by
    simpa [prefixWord, tailWord_961965, baseEnd_961965] using wordTrace_append hprefix tailTrace_961965
  have hstable : (prefixWord ++ tailWord_961965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961965).length < 2 ^ (prefixWord ++ tailWord_961965).sum := by decide
  have hdescent : baseEnd_961965 < baseStart_961965 := by decide
  rcases family_descends (prefixWord ++ tailWord_961965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_961995 : List Nat := [1, 1, 1, 1, 3, 3, 5, 3, 4]
def baseStart_961995 : Nat := 118140960795 + 961995 * 2 ^ 59
def prefixEnd_961995 : Nat := 4983230072969 + 3 ^ 40 * 961995 * 2
def baseEnd_961995 : Nat := 109770182716015316408527

theorem tailTrace_961995 : CollatzResearch.WordTrace tailWord_961995 prefixEnd_961995 109770182716015316408527 := by
  unfold tailWord_961995
  simp only [CollatzResearch.WordTrace]
  refine ⟨35086840149863885510863439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23391226766575923673908959 35086840149863885510863439)
  ·
    refine ⟨52630260224795828266295159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35086840149863885510863439 52630260224795828266295159)
    ·
      refine ⟨78945390337193742399442739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52630260224795828266295159 78945390337193742399442739)
      ·
        refine ⟨118418085505790613599164109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78945390337193742399442739 118418085505790613599164109)
        ·
          refine ⟨44406782064671480099686541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118418085505790613599164109 44406782064671480099686541)
          ·
            refine ⟨16652543274251805037382453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44406782064671480099686541 16652543274251805037382453)
            ·
              refine ⟨1561175931961106722254605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16652543274251805037382453 1561175931961106722254605)
              ·
                refine ⟨585440974485415020845477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1561175931961106722254605 585440974485415020845477)
                ·
                  refine ⟨109770182716015316408527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585440974485415020845477 109770182716015316408527)
                  ·
                    rfl

theorem cell22_961995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 4].length) (baseStart_961995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_961995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_961995 prefixEnd_961995 := by exact prefixLift 961995
  have htrace : WordTrace (prefixWord ++ tailWord_961995) baseStart_961995 baseEnd_961995 := by
    simpa [prefixWord, tailWord_961995, baseEnd_961995] using wordTrace_append hprefix tailTrace_961995
  have hstable : (prefixWord ++ tailWord_961995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_961995).length < 2 ^ (prefixWord ++ tailWord_961995).sum := by decide
  have hdescent : baseEnd_961995 < baseStart_961995 := by decide
  rcases family_descends (prefixWord ++ tailWord_961995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962008 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 4, 4]
def baseStart_962008 : Nat := 118140960795 + 962008 * 2 ^ 59
def prefixEnd_962008 : Nat := 4983230072969 + 3 ^ 40 * 962008 * 2
def baseEnd_962008 : Nat := 329314998313718248650541

theorem tailTrace_962008 : CollatzResearch.WordTrace tailWord_962008 prefixEnd_962008 329314998313718248650541 := by
  unfold tailWord_962008
  simp only [CollatzResearch.WordTrace]
  refine ⟨17543657149408394365543339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23391542865877859154057785 17543657149408394365543339)
  ·
    refine ⟨26315485724112591548315009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17543657149408394365543339 26315485724112591548315009)
    ·
      refine ⟨19736614293084443661236257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26315485724112591548315009 19736614293084443661236257)
      ·
        refine ⟨14802460719813332745927193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19736614293084443661236257 14802460719813332745927193)
        ·
          refine ⟨11101845539859999559445395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14802460719813332745927193 11101845539859999559445395)
          ·
            refine ⟨16652768309789999339168093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11101845539859999559445395 16652768309789999339168093)
            ·
              refine ⟨6244788116171249752188035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16652768309789999339168093 6244788116171249752188035)
              ·
                refine ⟨9367182174256874628282053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244788116171249752188035 9367182174256874628282053)
                ·
                  refine ⟨1756346657673163992802885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9367182174256874628282053 1756346657673163992802885)
                  ·
                    refine ⟨329314998313718248650541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1756346657673163992802885 329314998313718248650541)
                    ·
                      rfl

theorem cell22_962008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_962008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962008 prefixEnd_962008 := by exact prefixLift 962008
  have htrace : WordTrace (prefixWord ++ tailWord_962008) baseStart_962008 baseEnd_962008 := by
    simpa [prefixWord, tailWord_962008, baseEnd_962008] using wordTrace_append hprefix tailTrace_962008
  have hstable : (prefixWord ++ tailWord_962008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962008).length < 2 ^ (prefixWord ++ tailWord_962008).sum := by decide
  have hdescent : baseEnd_962008 < baseStart_962008 := by decide
  rcases family_descends (prefixWord ++ tailWord_962008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962010 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 4, 3]
def baseStart_962010 : Nat := 118140960795 + 962010 * 2 ^ 59
def prefixEnd_962010 : Nat := 4983230072969 + 3 ^ 40 * 962010 * 2
def baseEnd_962010 : Nat := 329315682954590910100535

theorem tailTrace_962010 : CollatzResearch.WordTrace tailWord_962010 prefixEnd_962010 329315682954590910100535 := by
  unfold tailWord_962010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8771846811202385768164871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23391591496539695381772989 8771846811202385768164871)
  ·
    refine ⟨13157770216803578652247307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8771846811202385768164871 13157770216803578652247307)
    ·
      refine ⟨19736655325205367978370961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13157770216803578652247307 19736655325205367978370961)
      ·
        refine ⟨14802491493904025983778221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19736655325205367978370961 14802491493904025983778221)
        ·
          refine ⟨5550934310214009743916833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14802491493904025983778221 5550934310214009743916833)
          ·
            refine ⟨4163200732660507307937625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5550934310214009743916833 4163200732660507307937625)
            ·
              refine ⟨3122400549495380480953219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4163200732660507307937625 3122400549495380480953219)
              ·
                refine ⟨4683600824243070721429829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122400549495380480953219 4683600824243070721429829)
                ·
                  refine ⟨878175154545575760268093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4683600824243070721429829 878175154545575760268093)
                  ·
                    refine ⟨329315682954590910100535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 878175154545575760268093 329315682954590910100535)
                    ·
                      rfl

theorem cell22_962010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_962010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962010 prefixEnd_962010 := by exact prefixLift 962010
  have htrace : WordTrace (prefixWord ++ tailWord_962010) baseStart_962010 baseEnd_962010 := by
    simpa [prefixWord, tailWord_962010, baseEnd_962010] using wordTrace_append hprefix tailTrace_962010
  have hstable : (prefixWord ++ tailWord_962010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962010).length < 2 ^ (prefixWord ++ tailWord_962010).sum := by decide
  have hdescent : baseEnd_962010 < baseStart_962010 := by decide
  rcases family_descends (prefixWord ++ tailWord_962010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962023 : List Nat := [1, 1, 5, 2, 1, 2, 1, 9]
def baseStart_962023 : Nat := 118140960795 + 962023 * 2 ^ 59
def prefixEnd_962023 : Nat := 4983230072969 + 3 ^ 40 * 962023 * 2
def baseEnd_962023 : Nat := 36591125902251467725055

theorem tailTrace_962023 : CollatzResearch.WordTrace tailWord_962023 prefixEnd_962023 36591125902251467725055 := by
  unfold tailWord_962023
  simp only [CollatzResearch.WordTrace]
  refine ⟨35087861393762446292882723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23391907595841630861921815 35087861393762446292882723)
  ·
    refine ⟨52631792090643669439324085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35087861393762446292882723 52631792090643669439324085)
    ·
      refine ⟨4934230508497844009936633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52631792090643669439324085 4934230508497844009936633)
      ·
        refine ⟨3700672881373383007452475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4934230508497844009936633 3700672881373383007452475)
        ·
          refine ⟨5551009322060074511178713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3700672881373383007452475 5551009322060074511178713)
          ·
            refine ⟨4163256991545055883384035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5551009322060074511178713 4163256991545055883384035)
            ·
              refine ⟨6244885487317583825076053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163256991545055883384035 6244885487317583825076053)
              ·
                refine ⟨36591125902251467725055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6244885487317583825076053 36591125902251467725055)
                ·
                  rfl

theorem cell22_962023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 9].length) (baseStart_962023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962023 prefixEnd_962023 := by exact prefixLift 962023
  have htrace : WordTrace (prefixWord ++ tailWord_962023) baseStart_962023 baseEnd_962023 := by
    simpa [prefixWord, tailWord_962023, baseEnd_962023] using wordTrace_append hprefix tailTrace_962023
  have hstable : (prefixWord ++ tailWord_962023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962023).length < 2 ^ (prefixWord ++ tailWord_962023).sum := by decide
  have hdescent : baseEnd_962023 < baseStart_962023 := by decide
  rcases family_descends (prefixWord ++ tailWord_962023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962119 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 5]
def baseStart_962119 : Nat := 118140960795 + 962119 * 2 ^ 59
def prefixEnd_962119 : Nat := 4983230072969 + 3 ^ 40 * 962119 * 2
def baseEnd_962119 : Nat := 109784331960716986375067

theorem tailTrace_962119 : CollatzResearch.WordTrace tailWord_962119 prefixEnd_962119 109784331960716986375067 := by
  unfold tailWord_962119
  simp only [CollatzResearch.WordTrace]
  refine ⟨35091362801414654688377411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23394241867609769792251607 35091362801414654688377411)
  ·
    refine ⟨52637044202121982032566117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35091362801414654688377411 52637044202121982032566117)
    ·
      refine ⟨9869445787897871631106147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52637044202121982032566117 9869445787897871631106147)
      ·
        refine ⟨14804168681846807446659221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9869445787897871631106147 14804168681846807446659221)
        ·
          refine ⟨693945406961569099062151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14804168681846807446659221 693945406961569099062151)
          ·
            refine ⟨1040918110442353648593227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693945406961569099062151 1040918110442353648593227)
            ·
              refine ⟨1561377165663530472889841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040918110442353648593227 1561377165663530472889841)
              ·
                refine ⟨1171032874247647854667381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1561377165663530472889841 1171032874247647854667381)
                ·
                  refine ⟨109784331960716986375067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1171032874247647854667381 109784331960716986375067)
                  ·
                    rfl

theorem cell22_962119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 5].length) (baseStart_962119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962119 prefixEnd_962119 := by exact prefixLift 962119
  have htrace : WordTrace (prefixWord ++ tailWord_962119) baseStart_962119 baseEnd_962119 := by
    simpa [prefixWord, tailWord_962119, baseEnd_962119] using wordTrace_append hprefix tailTrace_962119
  have hstable : (prefixWord ++ tailWord_962119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962119).length < 2 ^ (prefixWord ++ tailWord_962119).sum := by decide
  have hdescent : baseEnd_962119 < baseStart_962119 := by decide
  rcases family_descends (prefixWord ++ tailWord_962119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962130 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_962130 : Nat := 118140960795 + 962130 * 2 ^ 59
def prefixEnd_962130 : Nat := 4983230072969 + 3 ^ 40 * 962130 * 2
def baseEnd_962130 : Nat := 109785587135650199033389

theorem tailTrace_962130 : CollatzResearch.WordTrace tailWord_962130 prefixEnd_962130 109785587135650199033389 := by
  unfold tailWord_962130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8772941001093700891756961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23394509336249869044685229 8772941001093700891756961)
  ·
    refine ⟨6579705750820275668817721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8772941001093700891756961 6579705750820275668817721)
    ·
      refine ⟨4934779313115206751613291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6579705750820275668817721 4934779313115206751613291)
      ·
        refine ⟨7402168969672810127419937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4934779313115206751613291 7402168969672810127419937)
        ·
          refine ⟨5551626727254607595564953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7402168969672810127419937 5551626727254607595564953)
          ·
            refine ⟨4163720045440955696673715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5551626727254607595564953 4163720045440955696673715)
            ·
              refine ⟨6245580068161433545010573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163720045440955696673715 6245580068161433545010573)
              ·
                refine ⟨2342092525560537579378965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6245580068161433545010573 2342092525560537579378965)
                ·
                  refine ⟨109785587135650199033389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2342092525560537579378965 109785587135650199033389)
                  ·
                    rfl

theorem cell22_962130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_962130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962130 prefixEnd_962130 := by exact prefixLift 962130
  have htrace : WordTrace (prefixWord ++ tailWord_962130) baseStart_962130 baseEnd_962130 := by
    simpa [prefixWord, tailWord_962130, baseEnd_962130] using wordTrace_append hprefix tailTrace_962130
  have hstable : (prefixWord ++ tailWord_962130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962130).length < 2 ^ (prefixWord ++ tailWord_962130).sum := by decide
  have hdescent : baseEnd_962130 < baseStart_962130 := by decide
  rcases family_descends (prefixWord ++ tailWord_962130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962160 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 1, 6]
def baseStart_962160 : Nat := 118140960795 + 962160 * 2 ^ 59
def prefixEnd_962160 : Nat := 4983230072969 + 3 ^ 40 * 962160 * 2
def baseEnd_962160 : Nat := 329367031020040518850075

theorem tailTrace_962160 : CollatzResearch.WordTrace tailWord_962160 prefixEnd_962160 329367031020040518850075 := by
  unfold tailWord_962160
  simp only [CollatzResearch.WordTrace]
  refine ⟨17546429097133059345309967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23395238796177412460413289 17546429097133059345309967)
  ·
    refine ⟨26319643645699589017964951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17546429097133059345309967 26319643645699589017964951)
    ·
      refine ⟨39479465468549383526947427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26319643645699589017964951 39479465468549383526947427)
      ·
        refine ⟨59219198202824075290421141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39479465468549383526947427 59219198202824075290421141)
        ·
          refine ⟨2775899915757378529238491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59219198202824075290421141 2775899915757378529238491)
          ·
            refine ⟨4163849873636067793857737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775899915757378529238491 4163849873636067793857737)
            ·
              refine ⟨3122887405227050845393303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4163849873636067793857737 3122887405227050845393303)
              ·
                refine ⟨4684331107840576268089955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3122887405227050845393303 4684331107840576268089955)
                ·
                  refine ⟨7026496661760864402134933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684331107840576268089955 7026496661760864402134933)
                  ·
                    refine ⟨329367031020040518850075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7026496661760864402134933 329367031020040518850075)
                    ·
                      rfl

theorem cell22_962160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_962160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962160 prefixEnd_962160 := by exact prefixLift 962160
  have htrace : WordTrace (prefixWord ++ tailWord_962160) baseStart_962160 baseEnd_962160 := by
    simpa [prefixWord, tailWord_962160, baseEnd_962160] using wordTrace_append hprefix tailTrace_962160
  have hstable : (prefixWord ++ tailWord_962160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962160).length < 2 ^ (prefixWord ++ tailWord_962160).sum := by decide
  have hdescent : baseEnd_962160 < baseStart_962160 := by decide
  rcases family_descends (prefixWord ++ tailWord_962160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962162 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_962162 : Nat := 118140960795 + 962162 * 2 ^ 59
def prefixEnd_962162 : Nat := 4983230072969 + 3 ^ 40 * 962162 * 2
def baseEnd_962162 : Nat := 329367715660913180300069

theorem tailTrace_962162 : CollatzResearch.WordTrace tailWord_962162 prefixEnd_962162 329367715660913180300069 := by
  unfold tailWord_962162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8773232785064718258048185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23395287426839248688128493 8773232785064718258048185)
  ·
    refine ⟨6579924588798538693536139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8773232785064718258048185 6579924588798538693536139)
    ·
      refine ⟨9869886883197808040304209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6579924588798538693536139 9869886883197808040304209)
      ·
        refine ⟨7402415162398356030228157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9869886883197808040304209 7402415162398356030228157)
        ·
          refine ⟨2775905685899383511335559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7402415162398356030228157 2775905685899383511335559)
          ·
            refine ⟨4163858528849075267003339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2775905685899383511335559 4163858528849075267003339)
            ·
              refine ⟨6245787793273612900505009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4163858528849075267003339 6245787793273612900505009)
              ·
                refine ⟨4684340844955209675378757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6245787793273612900505009 4684340844955209675378757)
                ·
                  refine ⟨878313908429101814133517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4684340844955209675378757 878313908429101814133517)
                  ·
                    refine ⟨329367715660913180300069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 878313908429101814133517 329367715660913180300069)
                    ·
                      rfl

theorem cell22_962162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_962162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962162 prefixEnd_962162 := by exact prefixLift 962162
  have htrace : WordTrace (prefixWord ++ tailWord_962162) baseStart_962162 baseEnd_962162 := by
    simpa [prefixWord, tailWord_962162, baseEnd_962162] using wordTrace_append hprefix tailTrace_962162
  have hstable : (prefixWord ++ tailWord_962162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962162).length < 2 ^ (prefixWord ++ tailWord_962162).sum := by decide
  have hdescent : baseEnd_962162 < baseStart_962162 := by decide
  rcases family_descends (prefixWord ++ tailWord_962162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962177 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 2, 4]
def baseStart_962177 : Nat := 118140960795 + 962177 * 2 ^ 59
def prefixEnd_962177 : Nat := 4983230072969 + 3 ^ 40 * 962177 * 2
def baseEnd_962177 : Nat := 329372850467458141175023

theorem tailTrace_962177 : CollatzResearch.WordTrace tailWord_962177 prefixEnd_962177 329372850467458141175023 := by
  unfold tailWord_962177
  simp only [CollatzResearch.WordTrace]
  refine ⟨35093478235204530593988785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23395652156803020395992523 35093478235204530593988785)
  ·
    refine ⟨26320108676403397945491589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35093478235204530593988785 26320108676403397945491589)
    ·
      refine ⟨4935020376825637114779673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26320108676403397945491589 4935020376825637114779673)
      ·
        refine ⟨3701265282619227836084755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4935020376825637114779673 3701265282619227836084755)
        ·
          refine ⟨5551897923928841754127133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3701265282619227836084755 5551897923928841754127133)
          ·
            refine ⟨2081961721473315657797675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5551897923928841754127133 2081961721473315657797675)
            ·
              refine ⟨3122942582209973486696513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2081961721473315657797675 3122942582209973486696513)
              ·
                refine ⟨2342206936657480115022385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3122942582209973486696513 2342206936657480115022385)
                ·
                  refine ⟨1756655202493110086266789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2342206936657480115022385 1756655202493110086266789)
                  ·
                    refine ⟨329372850467458141175023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1756655202493110086266789 329372850467458141175023)
                    ·
                      rfl

theorem cell22_962177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_962177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962177 prefixEnd_962177 := by exact prefixLift 962177
  have htrace : WordTrace (prefixWord ++ tailWord_962177) baseStart_962177 baseEnd_962177 := by
    simpa [prefixWord, tailWord_962177, baseEnd_962177] using wordTrace_append hprefix tailTrace_962177
  have hstable : (prefixWord ++ tailWord_962177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962177).length < 2 ^ (prefixWord ++ tailWord_962177).sum := by decide
  have hdescent : baseEnd_962177 < baseStart_962177 := by decide
  rcases family_descends (prefixWord ++ tailWord_962177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962196 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_962196 : Nat := 118140960795 + 962196 * 2 ^ 59
def prefixEnd_962196 : Nat := 4983230072969 + 3 ^ 40 * 962196 * 2
def baseEnd_962196 : Nat := 329379354555748424949965

theorem tailTrace_962196 : CollatzResearch.WordTrace tailWord_962196 prefixEnd_962196 329379354555748424949965 := by
  unfold tailWord_962196
  simp only [CollatzResearch.WordTrace]
  refine ⟨17547085611067848419465221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23396114148090464559286961 17547085611067848419465221)
  ·
    refine ⟨3290078552075221578649729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17547085611067848419465221 3290078552075221578649729)
    ·
      refine ⟨2467558914056416183987297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3290078552075221578649729 2467558914056416183987297)
      ·
        refine ⟨1850669185542312137990473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2467558914056416183987297 1850669185542312137990473)
        ·
          refine ⟨1388001889156734103492855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1850669185542312137990473 1388001889156734103492855)
          ·
            refine ⟨2082002833735101155239283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388001889156734103492855 2082002833735101155239283)
            ·
              refine ⟨3123004250602651732858925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082002833735101155239283 3123004250602651732858925)
              ·
                refine ⟨1171126593975994399822097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3123004250602651732858925 1171126593975994399822097)
                ·
                  refine ⟨878344945481995799866573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1171126593975994399822097 878344945481995799866573)
                  ·
                    refine ⟨329379354555748424949965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 878344945481995799866573 329379354555748424949965)
                    ·
                      rfl

theorem cell22_962196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_962196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962196 prefixEnd_962196 := by exact prefixLift 962196
  have htrace : WordTrace (prefixWord ++ tailWord_962196) baseStart_962196 baseEnd_962196 := by
    simpa [prefixWord, tailWord_962196, baseEnd_962196] using wordTrace_append hprefix tailTrace_962196
  have hstable : (prefixWord ++ tailWord_962196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962196).length < 2 ^ (prefixWord ++ tailWord_962196).sum := by decide
  have hdescent : baseEnd_962196 < baseStart_962196 := by decide
  rcases family_descends (prefixWord ++ tailWord_962196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962237 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 5]
def baseStart_962237 : Nat := 118140960795 + 962237 * 2 ^ 59
def prefixEnd_962237 : Nat := 4983230072969 + 3 ^ 40 * 962237 * 2
def baseEnd_962237 : Nat := 109797796564545994891613

theorem tailTrace_962237 : CollatzResearch.WordTrace tailWord_962237 prefixEnd_962237 109797796564545994891613 := by
  unfold tailWord_962237
  simp only [CollatzResearch.WordTrace]
  refine ⟨35095666614987160841172965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23397111076658107227448643 35095666614987160841172965)
  ·
    refine ⟨6580437490310092657719931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35095666614987160841172965 6580437490310092657719931)
    ·
      refine ⟨9870656235465138986579897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6580437490310092657719931 9870656235465138986579897)
      ·
        refine ⟨7402992176598854239934923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9870656235465138986579897 7402992176598854239934923)
        ·
          refine ⟨11104488264898281359902385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7402992176598854239934923 11104488264898281359902385)
          ·
            refine ⟨8328366198673711019926789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11104488264898281359902385 8328366198673711019926789)
            ·
              refine ⟨1561568662251320816236273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8328366198673711019926789 1561568662251320816236273)
              ·
                refine ⟨1171176496688490612177205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1561568662251320816236273 1171176496688490612177205)
                ·
                  refine ⟨109797796564545994891613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1171176496688490612177205 109797796564545994891613)
                  ·
                    rfl

theorem cell22_962237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_962237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962237 prefixEnd_962237 := by exact prefixLift 962237
  have htrace : WordTrace (prefixWord ++ tailWord_962237) baseStart_962237 baseEnd_962237 := by
    simpa [prefixWord, tailWord_962237, baseEnd_962237] using wordTrace_append hprefix tailTrace_962237
  have hstable : (prefixWord ++ tailWord_962237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962237).length < 2 ^ (prefixWord ++ tailWord_962237).sum := by decide
  have hdescent : baseEnd_962237 < baseStart_962237 := by decide
  rcases family_descends (prefixWord ++ tailWord_962237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962265 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 8]
def baseStart_962265 : Nat := 118140960795 + 962265 * 2 ^ 59
def prefixEnd_962265 : Nat := 4983230072969 + 3 ^ 40 * 962265 * 2
def baseEnd_962265 : Nat := 109800991555285081658251

theorem tailTrace_962265 : CollatzResearch.WordTrace tailWord_962265 prefixEnd_962265 109800991555285081658251 := by
  unfold tailWord_962265
  simp only [CollatzResearch.WordTrace]
  refine ⟨35096687858885721623192249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23397791905923814415461499 35096687858885721623192249)
  ·
    refine ⟨26322515894164291217394187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35096687858885721623192249 26322515894164291217394187)
    ·
      refine ⟨39483773841246436826091281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26322515894164291217394187 39483773841246436826091281)
      ·
        refine ⟨29612830380934827619568461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39483773841246436826091281 29612830380934827619568461)
        ·
          refine ⟨11104811392850560357338173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29612830380934827619568461 11104811392850560357338173)
          ·
            refine ⟨4164304272318960134001815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11104811392850560357338173 4164304272318960134001815)
            ·
              refine ⟨6246456408478440201002723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4164304272318960134001815 6246456408478440201002723)
              ·
                refine ⟨9369684612717660301504085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6246456408478440201002723 9369684612717660301504085)
                ·
                  refine ⟨109800991555285081658251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9369684612717660301504085 109800991555285081658251)
                  ·
                    rfl

theorem cell22_962265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_962265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962265 prefixEnd_962265 := by exact prefixLift 962265
  have htrace : WordTrace (prefixWord ++ tailWord_962265) baseStart_962265 baseEnd_962265 := by
    simpa [prefixWord, tailWord_962265, baseEnd_962265] using wordTrace_append hprefix tailTrace_962265
  have hstable : (prefixWord ++ tailWord_962265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962265).length < 2 ^ (prefixWord ++ tailWord_962265).sum := by decide
  have hdescent : baseEnd_962265 < baseStart_962265 := by decide
  rcases family_descends (prefixWord ++ tailWord_962265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962284 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 1, 4]
def baseStart_962284 : Nat := 118140960795 + 962284 * 2 ^ 59
def prefixEnd_962284 : Nat := 4983230072969 + 3 ^ 40 * 962284 * 2
def baseEnd_962284 : Nat := 329409478754145528749695

theorem tailTrace_962284 : CollatzResearch.WordTrace tailWord_962284 prefixEnd_962284 329409478754145528749695 := by
  unfold tailWord_962284
  simp only [CollatzResearch.WordTrace]
  refine ⟨17548690422908443934066953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23398253897211258578755937 17548690422908443934066953)
  ·
    refine ⟨13161517817181332950550215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17548690422908443934066953 13161517817181332950550215)
    ·
      refine ⟨19742276725771999425825323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13161517817181332950550215 19742276725771999425825323)
      ·
        refine ⟨29613415088657999138737985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19742276725771999425825323 29613415088657999138737985)
        ·
          refine ⟨22210061316493499354053489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29613415088657999138737985 22210061316493499354053489)
          ·
            refine ⟨16657545987370124515540117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22210061316493499354053489 16657545987370124515540117)
            ·
              refine ⟨780822468157974586665943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16657545987370124515540117 780822468157974586665943)
              ·
                refine ⟨1171233702236961879998915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 780822468157974586665943 1171233702236961879998915)
                ·
                  refine ⟨1756850553355442819998373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171233702236961879998915 1756850553355442819998373)
                  ·
                    refine ⟨329409478754145528749695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1756850553355442819998373 329409478754145528749695)
                    ·
                      rfl

theorem cell22_962284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_962284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962284 prefixEnd_962284 := by exact prefixLift 962284
  have htrace : WordTrace (prefixWord ++ tailWord_962284) baseStart_962284 baseEnd_962284 := by
    simpa [prefixWord, tailWord_962284, baseEnd_962284] using wordTrace_append hprefix tailTrace_962284
  have hstable : (prefixWord ++ tailWord_962284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962284).length < 2 ^ (prefixWord ++ tailWord_962284).sum := by decide
  have hdescent : baseEnd_962284 < baseStart_962284 := by decide
  rcases family_descends (prefixWord ++ tailWord_962284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962314 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 1, 5]
def baseStart_962314 : Nat := 118140960795 + 962314 * 2 ^ 59
def prefixEnd_962314 : Nat := 4983230072969 + 3 ^ 40 * 962314 * 2
def baseEnd_962314 : Nat := 329419748367235450499603

theorem tailTrace_962314 : CollatzResearch.WordTrace tailWord_962314 prefixEnd_962314 329419748367235450499603 := by
  unfold tailWord_962314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8774618758927050747931499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23398983357138801994483997 8774618758927050747931499)
  ·
    refine ⟨13161928138390576121897249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8774618758927050747931499 13161928138390576121897249)
    ·
      refine ⟨9871446103792932091422937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13161928138390576121897249 9871446103792932091422937)
      ·
        refine ⟨7403584577844699068567203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9871446103792932091422937 7403584577844699068567203)
        ·
          refine ⟨11105376866767048602850805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7403584577844699068567203 11105376866767048602850805)
          ·
            refine ⟨1041129081259410806517263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11105376866767048602850805 1041129081259410806517263)
            ·
              refine ⟨1561693621889116209775895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041129081259410806517263 1561693621889116209775895)
              ·
                refine ⟨2342540432833674314663843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1561693621889116209775895 2342540432833674314663843)
                ·
                  refine ⟨3513810649250511471995765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2342540432833674314663843 3513810649250511471995765)
                  ·
                    refine ⟨329419748367235450499603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3513810649250511471995765 329419748367235450499603)
                    ·
                      rfl

theorem cell22_962314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_962314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962314 prefixEnd_962314 := by exact prefixLift 962314
  have htrace : WordTrace (prefixWord ++ tailWord_962314) baseStart_962314 baseEnd_962314 := by
    simpa [prefixWord, tailWord_962314, baseEnd_962314] using wordTrace_append hprefix tailTrace_962314
  have hstable : (prefixWord ++ tailWord_962314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962314).length < 2 ^ (prefixWord ++ tailWord_962314).sum := by decide
  have hdescent : baseEnd_962314 < baseStart_962314 := by decide
  rcases family_descends (prefixWord ++ tailWord_962314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962327 : List Nat := [1, 1, 3, 4, 2, 2, 1, 8]
def baseStart_962327 : Nat := 118140960795 + 962327 * 2 ^ 59
def prefixEnd_962327 : Nat := 4983230072969 + 3 ^ 40 * 962327 * 2
def baseEnd_962327 : Nat := 36602688725878638880507

theorem tailTrace_962327 : CollatzResearch.WordTrace tailWord_962327 prefixEnd_962327 36602688725878638880507 := by
  unfold tailWord_962327
  simp only [CollatzResearch.WordTrace]
  refine ⟨35098949184661106211949235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23399299456440737474632823 35098949184661106211949235)
  ·
    refine ⟨52648423776991659317923853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35098949184661106211949235 52648423776991659317923853)
    ·
      refine ⟨19743158916371872244221445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52648423776991659317923853 19743158916371872244221445)
      ·
        refine ⟨3701842296819726045791521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19743158916371872244221445 3701842296819726045791521)
        ·
          refine ⟨2776381722614794534343641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3701842296819726045791521 2776381722614794534343641)
          ·
            refine ⟨2082286291961095900757731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2776381722614794534343641 2082286291961095900757731)
            ·
              refine ⟨3123429437941643851136597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082286291961095900757731 3123429437941643851136597)
              ·
                refine ⟨36602688725878638880507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3123429437941643851136597 36602688725878638880507)
                ·
                  rfl

theorem cell22_962327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 8].length) (baseStart_962327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962327 prefixEnd_962327 := by exact prefixLift 962327
  have htrace : WordTrace (prefixWord ++ tailWord_962327) baseStart_962327 baseEnd_962327 := by
    simpa [prefixWord, tailWord_962327, baseEnd_962327] using wordTrace_append hprefix tailTrace_962327
  have hstable : (prefixWord ++ tailWord_962327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962327).length < 2 ^ (prefixWord ++ tailWord_962327).sum := by decide
  have hdescent : baseEnd_962327 < baseStart_962327 := by decide
  rcases family_descends (prefixWord ++ tailWord_962327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962410 : List Nat := [3, 1, 3, 4, 1, 1, 1, 4, 1, 3]
def baseStart_962410 : Nat := 118140960795 + 962410 * 2 ^ 59
def prefixEnd_962410 : Nat := 4983230072969 + 3 ^ 40 * 962410 * 2
def baseEnd_962410 : Nat := 329452611129123200099309

theorem tailTrace_962410 : CollatzResearch.WordTrace tailWord_962410 prefixEnd_962410 329452611129123200099309 := by
  unfold tailWord_962410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8775494110840102846805171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23401317628906940924813789 8775494110840102846805171)
  ·
    refine ⟨13163241166260154270207757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8775494110840102846805171 13163241166260154270207757)
    ·
      refine ⟨4936215437347557851327909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13163241166260154270207757 4936215437347557851327909)
      ·
        refine ⟨925540394502667097123983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4936215437347557851327909 925540394502667097123983)
        ·
          refine ⟨1388310591754000645685975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 925540394502667097123983 1388310591754000645685975)
          ·
            refine ⟨2082465887631000968528963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388310591754000645685975 2082465887631000968528963)
            ·
              refine ⟨3123698831446501452793445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082465887631000968528963 3123698831446501452793445)
              ·
                refine ⟨585693530896219022398771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3123698831446501452793445 585693530896219022398771)
                ·
                  refine ⟨878540296344328533598157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585693530896219022398771 878540296344328533598157)
                  ·
                    refine ⟨329452611129123200099309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 878540296344328533598157 329452611129123200099309)
                    ·
                      rfl

theorem cell22_962410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_962410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962410 prefixEnd_962410 := by exact prefixLift 962410
  have htrace : WordTrace (prefixWord ++ tailWord_962410) baseStart_962410 baseEnd_962410 := by
    simpa [prefixWord, tailWord_962410, baseEnd_962410] using wordTrace_append hprefix tailTrace_962410
  have hstable : (prefixWord ++ tailWord_962410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962410).length < 2 ^ (prefixWord ++ tailWord_962410).sum := by decide
  have hdescent : baseEnd_962410 < baseStart_962410 := by decide
  rcases family_descends (prefixWord ++ tailWord_962410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962417 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 6]
def baseStart_962417 : Nat := 118140960795 + 962417 * 2 ^ 59
def prefixEnd_962417 : Nat := 4983230072969 + 3 ^ 40 * 962417 * 2
def baseEnd_962417 : Nat := 109818335790725838391429

theorem tailTrace_962417 : CollatzResearch.WordTrace tailWord_962417 prefixEnd_962417 109818335790725838391429 := by
  unfold tailWord_962417
  simp only [CollatzResearch.WordTrace]
  refine ⟨35102231754335051582725505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23401487836223367721817003 35102231754335051582725505)
  ·
    refine ⟨26326673815751288687044129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35102231754335051582725505 26326673815751288687044129)
    ·
      refine ⟨19745005361813466515283097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26326673815751288687044129 19745005361813466515283097)
      ·
        refine ⟨14808754021360099886462323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19745005361813466515283097 14808754021360099886462323)
        ·
          refine ⟨22213131032040149829693485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14808754021360099886462323 22213131032040149829693485)
          ·
            refine ⟨8329924137015056186135057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22213131032040149829693485 8329924137015056186135057)
            ·
              refine ⟨6247443102761292139601293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8329924137015056186135057 6247443102761292139601293)
              ·
                refine ⟨2342791163535484552350485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6247443102761292139601293 2342791163535484552350485)
                ·
                  refine ⟨109818335790725838391429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2342791163535484552350485 109818335790725838391429)
                  ·
                    rfl

theorem cell22_962417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_962417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962417 prefixEnd_962417 := by exact prefixLift 962417
  have htrace : WordTrace (prefixWord ++ tailWord_962417) baseStart_962417 baseEnd_962417 := by
    simpa [prefixWord, tailWord_962417, baseEnd_962417] using wordTrace_append hprefix tailTrace_962417
  have hstable : (prefixWord ++ tailWord_962417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962417).length < 2 ^ (prefixWord ++ tailWord_962417).sum := by decide
  have hdescent : baseEnd_962417 < baseStart_962417 := by decide
  rcases family_descends (prefixWord ++ tailWord_962417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962507 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 9]
def baseStart_962507 : Nat := 118140960795 + 962507 * 2 ^ 59
def prefixEnd_962507 : Nat := 4983230072969 + 3 ^ 40 * 962507 * 2
def baseEnd_962507 : Nat := 109828605403815760141337

theorem tailTrace_962507 : CollatzResearch.WordTrace tailWord_962507 prefixEnd_962507 109828605403815760141337 := by
  unfold tailWord_962507
  simp only [CollatzResearch.WordTrace]
  refine ⟨35105514324008996953501775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23403676216005997969001183 35105514324008996953501775)
  ·
    refine ⟨52658271486013495430252663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35105514324008996953501775 52658271486013495430252663)
    ·
      refine ⟨78987407229020243145378995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52658271486013495430252663 78987407229020243145378995)
      ·
        refine ⟨118481110843530364718068493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78987407229020243145378995 118481110843530364718068493)
        ·
          refine ⟨44430416566323886769275685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118481110843530364718068493 44430416566323886769275685)
          ·
            refine ⟨8330703106185728769239191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44430416566323886769275685 8330703106185728769239191)
            ·
              refine ⟨12496054659278593153858787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8330703106185728769239191 12496054659278593153858787)
              ·
                refine ⟨18744081988917889730788181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12496054659278593153858787 18744081988917889730788181)
                ·
                  refine ⟨109828605403815760141337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18744081988917889730788181 109828605403815760141337)
                  ·
                    rfl

theorem cell22_962507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 9].length) (baseStart_962507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962507 prefixEnd_962507 := by exact prefixLift 962507
  have htrace : WordTrace (prefixWord ++ tailWord_962507) baseStart_962507 baseEnd_962507 := by
    simpa [prefixWord, tailWord_962507, baseEnd_962507] using wordTrace_append hprefix tailTrace_962507
  have hstable : (prefixWord ++ tailWord_962507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962507).length < 2 ^ (prefixWord ++ tailWord_962507).sum := by decide
  have hdescent : baseEnd_962507 < baseStart_962507 := by decide
  rcases family_descends (prefixWord ++ tailWord_962507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962584 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_962584 : Nat := 118140960795 + 962584 * 2 ^ 59
def prefixEnd_962584 : Nat := 4983230072969 + 3 ^ 40 * 962584 * 2
def baseEnd_962584 : Nat := 329512174885044746248775

theorem tailTrace_962584 : CollatzResearch.WordTrace tailWord_962584 prefixEnd_962584 329512174885044746248775 := by
  unfold tailWord_962584
  simp only [CollatzResearch.WordTrace]
  refine ⟨17554161372365019552027403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23405548496486692736036537 17554161372365019552027403)
  ·
    refine ⟨26331242058547529328041105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17554161372365019552027403 26331242058547529328041105)
    ·
      refine ⟨19748431543910646996030829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26331242058547529328041105 19748431543910646996030829)
      ·
        refine ⟨7405661828966492623511561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19748431543910646996030829 7405661828966492623511561)
        ·
          refine ⟨5554246371724869467633671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7405661828966492623511561 5554246371724869467633671)
          ·
            refine ⟨8331369557587304201450507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5554246371724869467633671 8331369557587304201450507)
            ·
              refine ⟨12497054336380956302175761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8331369557587304201450507 12497054336380956302175761)
              ·
                refine ⟨9372790752285717226631821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12497054336380956302175761 9372790752285717226631821)
                ·
                  refine ⟨3514796532107143959986933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9372790752285717226631821 3514796532107143959986933)
                  ·
                    refine ⟨329512174885044746248775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3514796532107143959986933 329512174885044746248775)
                    ·
                      rfl

theorem cell22_962584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_962584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962584 prefixEnd_962584 := by exact prefixLift 962584
  have htrace : WordTrace (prefixWord ++ tailWord_962584) baseStart_962584 baseEnd_962584 := by
    simpa [prefixWord, tailWord_962584, baseEnd_962584] using wordTrace_append hprefix tailTrace_962584
  have hstable : (prefixWord ++ tailWord_962584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962584).length < 2 ^ (prefixWord ++ tailWord_962584).sum := by decide
  have hdescent : baseEnd_962584 < baseStart_962584 := by decide
  rcases family_descends (prefixWord ++ tailWord_962584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962616 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 1, 6]
def baseStart_962616 : Nat := 118140960795 + 962616 * 2 ^ 59
def prefixEnd_962616 : Nat := 4983230072969 + 3 ^ 40 * 962616 * 2
def baseEnd_962616 : Nat := 329523129139007329448677

theorem tailTrace_962616 : CollatzResearch.WordTrace tailWord_962616 prefixEnd_962616 329523129139007329448677 := by
  unfold tailWord_962616
  simp only [CollatzResearch.WordTrace]
  refine ⟨17554744940307054284609851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23406326587076072379479801 17554744940307054284609851)
  ·
    refine ⟨26332117410460581426914777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17554744940307054284609851 26332117410460581426914777)
    ·
      refine ⟨19749088057845436070186083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26332117410460581426914777 19749088057845436070186083)
      ·
        refine ⟨29623632086768154105279125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19749088057845436070186083 29623632086768154105279125)
        ·
          refine ⟨1388607754067257223684959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29623632086768154105279125 1388607754067257223684959)
          ·
            refine ⟨2082911631100885835527439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1388607754067257223684959 2082911631100885835527439)
            ·
              refine ⟨3124367446651328753291159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2082911631100885835527439 3124367446651328753291159)
              ·
                refine ⟨4686551169976993129936739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3124367446651328753291159 4686551169976993129936739)
                ·
                  refine ⟨7029826754965489694905109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4686551169976993129936739 7029826754965489694905109)
                  ·
                    refine ⟨329523129139007329448677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7029826754965489694905109 329523129139007329448677)
                    ·
                      rfl

theorem cell22_962616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_962616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962616 prefixEnd_962616 := by exact prefixLift 962616
  have htrace : WordTrace (prefixWord ++ tailWord_962616) baseStart_962616 baseEnd_962616 := by
    simpa [prefixWord, tailWord_962616, baseEnd_962616] using wordTrace_append hprefix tailTrace_962616
  have hstable : (prefixWord ++ tailWord_962616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962616).length < 2 ^ (prefixWord ++ tailWord_962616).sum := by decide
  have hdescent : baseEnd_962616 < baseStart_962616 := by decide
  rcases family_descends (prefixWord ++ tailWord_962616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962622 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_962622 : Nat := 118140960795 + 962622 * 2 ^ 59
def prefixEnd_962622 : Nat := 4983230072969 + 3 ^ 40 * 962622 * 2
def baseEnd_962622 : Nat := 329525183061625313798659

theorem tailTrace_962622 : CollatzResearch.WordTrace tailWord_962622 prefixEnd_962622 329525183061625313798659 := by
  unfold tailWord_962622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4388713589824046449242265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23406472479061581062625413 4388713589824046449242265)
  ·
    refine ⟨3291535192368034836931699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4388713589824046449242265 3291535192368034836931699)
    ·
      refine ⟨4937302788552052255397549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3291535192368034836931699 4937302788552052255397549)
      ·
        refine ⟨1851488545707019595774081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4937302788552052255397549 1851488545707019595774081)
        ·
          refine ⟨1388616409280264696830561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1851488545707019595774081 1388616409280264696830561)
          ·
            refine ⟨1041462306960198522622921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1388616409280264696830561 1041462306960198522622921)
            ·
              refine ⟨781096730220148891967191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041462306960198522622921 781096730220148891967191)
              ·
                refine ⟨1171645095330223337950787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781096730220148891967191 1171645095330223337950787)
                ·
                  refine ⟨1757467642995335006926181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1171645095330223337950787 1757467642995335006926181)
                  ·
                    refine ⟨329525183061625313798659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1757467642995335006926181 329525183061625313798659)
                    ·
                      rfl

theorem cell22_962622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_962622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962622 prefixEnd_962622 := by exact prefixLift 962622
  have htrace : WordTrace (prefixWord ++ tailWord_962622) baseStart_962622 baseEnd_962622 := by
    simpa [prefixWord, tailWord_962622, baseEnd_962622] using wordTrace_append hprefix tailTrace_962622
  have hstable : (prefixWord ++ tailWord_962622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962622).length < 2 ^ (prefixWord ++ tailWord_962622).sum := by decide
  have hdescent : baseEnd_962622 < baseStart_962622 := by decide
  rcases family_descends (prefixWord ++ tailWord_962622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962738 : List Nat := [3, 2, 1, 1, 1, 3, 2, 5, 4]
def baseStart_962738 : Nat := 118140960795 + 962738 * 2 ^ 59
def prefixEnd_962738 : Nat := 4983230072969 + 3 ^ 40 * 962738 * 2
def baseEnd_962738 : Nat := 109854964077413225966101

theorem tailTrace_962738 : CollatzResearch.WordTrace tailWord_962738 prefixEnd_962738 109854964077413225966101 := by
  unfold tailWord_962738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8778484896543030851290217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23409293057448082270107245 8778484896543030851290217)
  ·
    refine ⟨6583863672407273138467663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8778484896543030851290217 6583863672407273138467663)
    ·
      refine ⟨9875795508610909707701495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6583863672407273138467663 9875795508610909707701495)
      ·
        refine ⟨14813693262916364561552243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9875795508610909707701495 14813693262916364561552243)
        ·
          refine ⟨22220539894374546842328365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14813693262916364561552243 22220539894374546842328365)
          ·
            refine ⟨8332702460390455065873137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22220539894374546842328365 8332702460390455065873137)
            ·
              refine ⟨6249526845292841299404853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8332702460390455065873137 6249526845292841299404853)
              ·
                refine ⟨585893141746203871819205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6249526845292841299404853 585893141746203871819205)
                ·
                  refine ⟨109854964077413225966101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 585893141746203871819205 109854964077413225966101)
                  ·
                    rfl

theorem cell22_962738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_962738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962738 prefixEnd_962738 := by exact prefixLift 962738
  have htrace : WordTrace (prefixWord ++ tailWord_962738) baseStart_962738 baseEnd_962738 := by
    simpa [prefixWord, tailWord_962738, baseEnd_962738] using wordTrace_append hprefix tailTrace_962738
  have hstable : (prefixWord ++ tailWord_962738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962738).length < 2 ^ (prefixWord ++ tailWord_962738).sum := by decide
  have hdescent : baseEnd_962738 < baseStart_962738 := by decide
  rcases family_descends (prefixWord ++ tailWord_962738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962770 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_962770 : Nat := 118140960795 + 962770 * 2 ^ 59
def prefixEnd_962770 : Nat := 4983230072969 + 3 ^ 40 * 962770 * 2
def baseEnd_962770 : Nat := 329575846486202261098205

theorem tailTrace_962770 : CollatzResearch.WordTrace tailWord_962770 prefixEnd_962770 329575846486202261098205 := by
  unfold tailWord_962770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8778776680514048217581441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23410071148037461913550509 8778776680514048217581441)
  ·
    refine ⟨6584082510385536163186081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8778776680514048217581441 6584082510385536163186081)
    ·
      refine ⟨4938061882789152122389561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6584082510385536163186081 4938061882789152122389561)
      ·
        refine ⟨3703546412091864091792171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4938061882789152122389561 3703546412091864091792171)
        ·
          refine ⟨5555319618137796137688257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3703546412091864091792171 5555319618137796137688257)
          ·
            refine ⟨4166489713603347103266193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5555319618137796137688257 4166489713603347103266193)
            ·
              refine ⟨3124867285202510327449645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4166489713603347103266193 3124867285202510327449645)
              ·
                refine ⟨1171825231950941372793617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3124867285202510327449645 1171825231950941372793617)
                ·
                  refine ⟨878868923963206029595213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1171825231950941372793617 878868923963206029595213)
                  ·
                    refine ⟨329575846486202261098205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 878868923963206029595213 329575846486202261098205)
                    ·
                      rfl

theorem cell22_962770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_962770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962770 prefixEnd_962770 := by exact prefixLift 962770
  have htrace : WordTrace (prefixWord ++ tailWord_962770) baseStart_962770 baseEnd_962770 := by
    simpa [prefixWord, tailWord_962770, baseEnd_962770] using wordTrace_append hprefix tailTrace_962770
  have hstable : (prefixWord ++ tailWord_962770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962770).length < 2 ^ (prefixWord ++ tailWord_962770).sum := by decide
  have hdescent : baseEnd_962770 < baseStart_962770 := by decide
  rcases family_descends (prefixWord ++ tailWord_962770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962798 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_962798 : Nat := 118140960795 + 962798 * 2 ^ 59
def prefixEnd_962798 : Nat := 4983230072969 + 3 ^ 40 * 962798 * 2
def baseEnd_962798 : Nat := 329585431458419521398119

theorem tailTrace_962798 : CollatzResearch.WordTrace tailWord_962798 prefixEnd_962798 329585431458419521398119 := by
  unfold tailWord_962798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4389515995744344206543131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23410751977303169101563365 4389515995744344206543131)
  ·
    refine ⟨6584273993616516309814697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4389515995744344206543131 6584273993616516309814697)
    ·
      refine ⟨4938205495212387232361023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6584273993616516309814697 4938205495212387232361023)
      ·
        refine ⟨7407308242818580848541535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938205495212387232361023 7407308242818580848541535)
        ·
          refine ⟨11110962364227871272812303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7407308242818580848541535 11110962364227871272812303)
          ·
            refine ⟨16666443546341806909218455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11110962364227871272812303 16666443546341806909218455)
            ·
              refine ⟨24999665319512710363827683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16666443546341806909218455 24999665319512710363827683)
              ·
                refine ⟨37499497979269065545741525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24999665319512710363827683 37499497979269065545741525)
                ·
                  refine ⟨878894483889118723728317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37499497979269065545741525 878894483889118723728317)
                  ·
                    refine ⟨329585431458419521398119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 878894483889118723728317 329585431458419521398119)
                    ·
                      rfl

theorem cell22_962798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_962798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962798 prefixEnd_962798 := by exact prefixLift 962798
  have htrace : WordTrace (prefixWord ++ tailWord_962798) baseStart_962798 baseEnd_962798 := by
    simpa [prefixWord, tailWord_962798, baseEnd_962798] using wordTrace_append hprefix tailTrace_962798
  have hstable : (prefixWord ++ tailWord_962798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962798).length < 2 ^ (prefixWord ++ tailWord_962798).sum := by decide
  have hdescent : baseEnd_962798 < baseStart_962798 := by decide
  rcases family_descends (prefixWord ++ tailWord_962798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962815 : List Nat := [1, 1, 2, 2, 1, 4, 1, 6, 1, 3]
def baseStart_962815 : Nat := 118140960795 + 962815 * 2 ^ 59
def prefixEnd_962815 : Nat := 4983230072969 + 3 ^ 40 * 962815 * 2
def baseEnd_962815 : Nat := 329591250905837143723067

theorem tailTrace_962815 : CollatzResearch.WordTrace tailWord_962815 prefixEnd_962815 329591250905837143723067 := by
  unfold tailWord_962815
  simp only [CollatzResearch.WordTrace]
  refine ⟨35116748006893165555713899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23411165337928777037142599 35116748006893165555713899)
  ·
    refine ⟨52675122010339748333570849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35116748006893165555713899 52675122010339748333570849)
    ·
      refine ⟨39506341507754811250178137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52675122010339748333570849 39506341507754811250178137)
      ·
        refine ⟨29629756130816108437633603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39506341507754811250178137 29629756130816108437633603)
        ·
          refine ⟨44444634196224162656450405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29629756130816108437633603 44444634196224162656450405)
          ·
            refine ⟨8333368911792030498084451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44444634196224162656450405 8333368911792030498084451)
            ·
              refine ⟨12500053367688045747126677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8333368911792030498084451 12500053367688045747126677)
              ·
                refine ⟨585940001610377144396563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12500053367688045747126677 585940001610377144396563)
                ·
                  refine ⟨878910002415565716594845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 585940001610377144396563 878910002415565716594845)
                  ·
                    refine ⟨329591250905837143723067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 878910002415565716594845 329591250905837143723067)
                    ·
                      rfl

theorem cell22_962815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 1, 3].length) (baseStart_962815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962815 prefixEnd_962815 := by exact prefixLift 962815
  have htrace : WordTrace (prefixWord ++ tailWord_962815) baseStart_962815 baseEnd_962815 := by
    simpa [prefixWord, tailWord_962815, baseEnd_962815] using wordTrace_append hprefix tailTrace_962815
  have hstable : (prefixWord ++ tailWord_962815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962815).length < 2 ^ (prefixWord ++ tailWord_962815).sum := by decide
  have hdescent : baseEnd_962815 < baseStart_962815 := by decide
  rcases family_descends (prefixWord ++ tailWord_962815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962920 : List Nat := [2, 1, 4, 2, 2, 1, 2, 2, 2, 4]
def baseStart_962920 : Nat := 118140960795 + 962920 * 2 ^ 59
def prefixEnd_962920 : Nat := 4983230072969 + 3 ^ 40 * 962920 * 2
def baseEnd_962920 : Nat := 329627194551651869847745

theorem tailTrace_962920 : CollatzResearch.WordTrace tailWord_962920 prefixEnd_962920 329627194551651869847745 := by
  unfold tailWord_962920
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560288835756384244143107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23413718447675178992190809 17560288835756384244143107)
  ·
    refine ⟨26340433253634576366214661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17560288835756384244143107 26340433253634576366214661)
    ·
      refine ⟨4938831235056483068665249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26340433253634576366214661 4938831235056483068665249)
      ·
        refine ⟨3704123426292362301498937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4938831235056483068665249 3704123426292362301498937)
        ·
          refine ⟨2778092569719271726124203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3704123426292362301498937 2778092569719271726124203)
          ·
            refine ⟨4167138854578907589186305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778092569719271726124203 4167138854578907589186305)
            ·
              refine ⟨3125354140934180691889729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4167138854578907589186305 3125354140934180691889729)
              ·
                refine ⟨2344015605700635518917297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125354140934180691889729 2344015605700635518917297)
                ·
                  refine ⟨1758011704275476639187973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344015605700635518917297 1758011704275476639187973)
                  ·
                    refine ⟨329627194551651869847745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1758011704275476639187973 329627194551651869847745)
                    ·
                      rfl

theorem cell22_962920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_962920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962920 prefixEnd_962920 := by exact prefixLift 962920
  have htrace : WordTrace (prefixWord ++ tailWord_962920) baseStart_962920 baseEnd_962920 := by
    simpa [prefixWord, tailWord_962920, baseEnd_962920] using wordTrace_append hprefix tailTrace_962920
  have hstable : (prefixWord ++ tailWord_962920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962920).length < 2 ^ (prefixWord ++ tailWord_962920).sum := by decide
  have hdescent : baseEnd_962920 < baseStart_962920 := by decide
  rcases family_descends (prefixWord ++ tailWord_962920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962922 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 2, 3]
def baseStart_962922 : Nat := 118140960795 + 962922 * 2 ^ 59
def prefixEnd_962922 : Nat := 4983230072969 + 3 ^ 40 * 962922 * 2
def baseEnd_962922 : Nat := 329627879192524531297739

theorem tailTrace_962922 : CollatzResearch.WordTrace tailWord_962922 prefixEnd_962922 329627879192524531297739 := by
  unfold tailWord_962922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8780162654376380707464755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23413767078337015219906013 8780162654376380707464755)
  ·
    refine ⟨13170243981564571061197133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8780162654376380707464755 13170243981564571061197133)
    ·
      refine ⟨4938841493086714147948925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13170243981564571061197133 4938841493086714147948925)
      ·
        refine ⟨1852065559907517805480847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4938841493086714147948925 1852065559907517805480847)
        ·
          refine ⟨2778098339861276708221271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852065559907517805480847 2778098339861276708221271)
          ·
            refine ⟨4167147509791915062331907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778098339861276708221271 4167147509791915062331907)
            ·
              refine ⟨6250721264687872593497861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4167147509791915062331907 6250721264687872593497861)
              ·
                refine ⟨1172010237128976111280849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6250721264687872593497861 1172010237128976111280849)
                ·
                  refine ⟨879007677846732083460637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1172010237128976111280849 879007677846732083460637)
                  ·
                    refine ⟨329627879192524531297739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 879007677846732083460637 329627879192524531297739)
                    ·
                      rfl

theorem cell22_962922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_962922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962922 prefixEnd_962922 := by exact prefixLift 962922
  have htrace : WordTrace (prefixWord ++ tailWord_962922) baseStart_962922 baseEnd_962922 := by
    simpa [prefixWord, tailWord_962922, baseEnd_962922] using wordTrace_append hprefix tailTrace_962922
  have hstable : (prefixWord ++ tailWord_962922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962922).length < 2 ^ (prefixWord ++ tailWord_962922).sum := by decide
  have hdescent : baseEnd_962922 < baseStart_962922 := by decide
  rcases family_descends (prefixWord ++ tailWord_962922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962924 : List Nat := [2, 2, 1, 1, 6, 2, 2, 2, 4]
def baseStart_962924 : Nat := 118140960795 + 962924 * 2 ^ 59
def prefixEnd_962924 : Nat := 4983230072969 + 3 ^ 40 * 962924 * 2
def baseEnd_962924 : Nat := 109876187944465730915911

theorem tailTrace_962924 : CollatzResearch.WordTrace tailWord_962924 prefixEnd_962924 109876187944465730915911 := by
  unfold tailWord_962924
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560361781749138585715913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23413815708998851447621217 17560361781749138585715913)
  ·
    refine ⟨13170271336311853939286935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17560361781749138585715913 13170271336311853939286935)
    ·
      refine ⟨19755407004467780908930403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13170271336311853939286935 19755407004467780908930403)
      ·
        refine ⟨29633110506701671363395605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19755407004467780908930403 29633110506701671363395605)
        ·
          refine ⟨1389052055001640845159169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29633110506701671363395605 1389052055001640845159169)
          ·
            refine ⟨1041789041251230633869377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389052055001640845159169 1041789041251230633869377)
            ·
              refine ⟨781341780938422975402033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041789041251230633869377 781341780938422975402033)
              ·
                refine ⟨586006335703817231551525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781341780938422975402033 586006335703817231551525)
                ·
                  refine ⟨109876187944465730915911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 586006335703817231551525 109876187944465730915911)
                  ·
                    rfl

theorem cell22_962924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_962924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962924 prefixEnd_962924 := by exact prefixLift 962924
  have htrace : WordTrace (prefixWord ++ tailWord_962924) baseStart_962924 baseEnd_962924 := by
    simpa [prefixWord, tailWord_962924, baseEnd_962924] using wordTrace_append hprefix tailTrace_962924
  have hstable : (prefixWord ++ tailWord_962924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962924).length < 2 ^ (prefixWord ++ tailWord_962924).sum := by decide
  have hdescent : baseEnd_962924 < baseStart_962924 := by decide
  rcases family_descends (prefixWord ++ tailWord_962924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962948 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_962948 : Nat := 118140960795 + 962948 * 2 ^ 59
def prefixEnd_962948 : Nat := 4983230072969 + 3 ^ 40 * 962948 * 2
def baseEnd_962948 : Nat := 329636779523869130147659

theorem tailTrace_962948 : CollatzResearch.WordTrace tailWord_962948 prefixEnd_962948 329636779523869130147659 := by
  unfold tailWord_962948
  simp only [CollatzResearch.WordTrace]
  refine ⟨17560799457705664635152749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23414399276940886180203665 17560799457705664635152749)
  ·
    refine ⟨6585299796639624238182281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17560799457705664635152749 6585299796639624238182281)
    ·
      refine ⟨4938974847479718178636711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6585299796639624238182281 4938974847479718178636711)
      ·
        refine ⟨7408462271219577267955067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4938974847479718178636711 7408462271219577267955067)
        ·
          refine ⟨11112693406829365901932601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408462271219577267955067 11112693406829365901932601)
          ·
            refine ⟨8334520055122024426449451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11112693406829365901932601 8334520055122024426449451)
            ·
              refine ⟨12501780082683036639674177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8334520055122024426449451 12501780082683036639674177)
              ·
                refine ⟨9376335062012277479755633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12501780082683036639674177 9376335062012277479755633)
                ·
                  refine ⟨7032251296509208109816725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9376335062012277479755633 7032251296509208109816725)
                  ·
                    refine ⟨329636779523869130147659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7032251296509208109816725 329636779523869130147659)
                    ·
                      rfl

theorem cell22_962948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_962948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962948 prefixEnd_962948 := by exact prefixLift 962948
  have htrace : WordTrace (prefixWord ++ tailWord_962948) baseStart_962948 baseEnd_962948 := by
    simpa [prefixWord, tailWord_962948, baseEnd_962948] using wordTrace_append hprefix tailTrace_962948
  have hstable : (prefixWord ++ tailWord_962948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962948).length < 2 ^ (prefixWord ++ tailWord_962948).sum := by decide
  have hdescent : baseEnd_962948 < baseStart_962948 := by decide
  rcases family_descends (prefixWord ++ tailWord_962948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962954 : List Nat := [3, 1, 2, 5, 1, 2, 1, 1, 2, 4]
def baseStart_962954 : Nat := 118140960795 + 962954 * 2 ^ 59
def prefixEnd_962954 : Nat := 4983230072969 + 3 ^ 40 * 962954 * 2
def baseEnd_962954 : Nat := 329638833446487114497641

theorem tailTrace_962954 : CollatzResearch.WordTrace tailWord_962954 prefixEnd_962954 329638833446487114497641 := by
  unfold tailWord_962954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8780454438347398073755979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23414545168926394863349277 8780454438347398073755979)
  ·
    refine ⟨13170681657521097110633969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8780454438347398073755979 13170681657521097110633969)
    ·
      refine ⟨9878011243140822832975477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13170681657521097110633969 9878011243140822832975477)
      ·
        refine ⟨926063554044452140591451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9878011243140822832975477 926063554044452140591451)
        ·
          refine ⟨1389095331066678210887177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926063554044452140591451 1389095331066678210887177)
          ·
            refine ⟨1041821498300008658165383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389095331066678210887177 1041821498300008658165383)
            ·
              refine ⟨1562732247450012987248075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041821498300008658165383 1562732247450012987248075)
              ·
                refine ⟨2344098371175019480872113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562732247450012987248075 2344098371175019480872113)
                ·
                  refine ⟨1758073778381264610654085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344098371175019480872113 1758073778381264610654085)
                  ·
                    refine ⟨329638833446487114497641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1758073778381264610654085 329638833446487114497641)
                    ·
                      rfl

theorem cell22_962954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_962954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962954 prefixEnd_962954 := by exact prefixLift 962954
  have htrace : WordTrace (prefixWord ++ tailWord_962954) baseStart_962954 baseEnd_962954 := by
    simpa [prefixWord, tailWord_962954, baseEnd_962954] using wordTrace_append hprefix tailTrace_962954
  have hstable : (prefixWord ++ tailWord_962954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962954).length < 2 ^ (prefixWord ++ tailWord_962954).sum := by decide
  have hdescent : baseEnd_962954 < baseStart_962954 := by decide
  rcases family_descends (prefixWord ++ tailWord_962954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962967 : List Nat := [1, 1, 3, 3, 1, 1, 3, 5, 1, 3]
def baseStart_962967 : Nat := 118140960795 + 962967 * 2 ^ 59
def prefixEnd_962967 : Nat := 4983230072969 + 3 ^ 40 * 962967 * 2
def baseEnd_962967 : Nat := 329643283612159413922601

theorem tailTrace_962967 : CollatzResearch.WordTrace tailWord_962967 prefixEnd_962967 329643283612159413922601 := by
  unfold tailWord_962967
  simp only [CollatzResearch.WordTrace]
  refine ⟨35122291902342495515247155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23414861268228330343498103 35122291902342495515247155)
  ·
    refine ⟨52683437853513743272870733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35122291902342495515247155 52683437853513743272870733)
    ·
      refine ⟨19756289195067653727326525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52683437853513743272870733 19756289195067653727326525)
      ·
        refine ⟨7408608448150370147747447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19756289195067653727326525 7408608448150370147747447)
        ·
          refine ⟨11112912672225555221621171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408608448150370147747447 11112912672225555221621171)
          ·
            refine ⟨16669369008338332832431757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11112912672225555221621171 16669369008338332832431757)
            ·
              refine ⟨6251013378126874812161909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16669369008338332832431757 6251013378126874812161909)
              ·
                refine ⟨586032504199394513640179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6251013378126874812161909 586032504199394513640179)
                ·
                  refine ⟨879048756299091770460269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586032504199394513640179 879048756299091770460269)
                  ·
                    refine ⟨329643283612159413922601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 879048756299091770460269 329643283612159413922601)
                    ·
                      rfl

theorem cell22_962967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_962967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962967 prefixEnd_962967 := by exact prefixLift 962967
  have htrace : WordTrace (prefixWord ++ tailWord_962967) baseStart_962967 baseEnd_962967 := by
    simpa [prefixWord, tailWord_962967, baseEnd_962967] using wordTrace_append hprefix tailTrace_962967
  have hstable : (prefixWord ++ tailWord_962967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962967).length < 2 ^ (prefixWord ++ tailWord_962967).sum := by decide
  have hdescent : baseEnd_962967 < baseStart_962967 := by decide
  rcases family_descends (prefixWord ++ tailWord_962967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962980 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 5]
def baseStart_962980 : Nat := 118140960795 + 962980 * 2 ^ 59
def prefixEnd_962980 : Nat := 4983230072969 + 3 ^ 40 * 962980 * 2
def baseEnd_962980 : Nat := 109882577925943904449187

theorem tailTrace_962980 : CollatzResearch.WordTrace tailWord_962980 prefixEnd_962980 109882577925943904449187 := by
  unfold tailWord_962980
  simp only [CollatzResearch.WordTrace]
  refine ⟨17561383025647699367735197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23415177367530265823646929 17561383025647699367735197)
  ·
    refine ⟨6585518634617887262900699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17561383025647699367735197 6585518634617887262900699)
    ·
      refine ⟨9878277951926830894351049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6585518634617887262900699 9878277951926830894351049)
      ·
        refine ⟨7408708463945123170763287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9878277951926830894351049 7408708463945123170763287)
        ·
          refine ⟨11113062695917684756144931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7408708463945123170763287 11113062695917684756144931)
          ·
            refine ⟨16669594043876527134217397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11113062695917684756144931 16669594043876527134217397)
            ·
              refine ⟨1562774441613424418832881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16669594043876527134217397 1562774441613424418832881)
              ·
                refine ⟨1172080831210068314124661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562774441613424418832881 1172080831210068314124661)
                ·
                  refine ⟨109882577925943904449187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1172080831210068314124661 109882577925943904449187)
                  ·
                    rfl

theorem cell22_962980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_962980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962980 prefixEnd_962980 := by exact prefixLift 962980
  have htrace : WordTrace (prefixWord ++ tailWord_962980) baseStart_962980 baseEnd_962980 := by
    simpa [prefixWord, tailWord_962980, baseEnd_962980] using wordTrace_append hprefix tailTrace_962980
  have hstable : (prefixWord ++ tailWord_962980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962980).length < 2 ^ (prefixWord ++ tailWord_962980).sum := by decide
  have hdescent : baseEnd_962980 < baseStart_962980 := by decide
  rcases family_descends (prefixWord ++ tailWord_962980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_962984 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 3, 3]
def baseStart_962984 : Nat := 118140960795 + 962984 * 2 ^ 59
def prefixEnd_962984 : Nat := 4983230072969 + 3 ^ 40 * 962984 * 2
def baseEnd_962984 : Nat := 329649103059577036247549

theorem tailTrace_962984 : CollatzResearch.WordTrace tailWord_962984 prefixEnd_962984 329649103059577036247549 := by
  unfold tailWord_962984
  simp only [CollatzResearch.WordTrace]
  refine ⟨17561455971640453709308003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23415274628853938279077337 17561455971640453709308003)
  ·
    refine ⟨26342183957460680563962005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17561455971640453709308003 26342183957460680563962005)
    ·
      refine ⟨1234789873005969401435719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26342183957460680563962005 1234789873005969401435719)
      ·
        refine ⟨1852184809508954102153579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234789873005969401435719 1852184809508954102153579)
        ·
          refine ⟨2778277214263431153230369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852184809508954102153579 2778277214263431153230369)
          ·
            refine ⟨2083707910697573364922777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2778277214263431153230369 2083707910697573364922777)
            ·
              refine ⟨1562780933023180023692083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083707910697573364922777 1562780933023180023692083)
              ·
                refine ⟨2344171399534770035538125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562780933023180023692083 2344171399534770035538125)
                ·
                  refine ⟨879064274825538763326797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2344171399534770035538125 879064274825538763326797)
                  ·
                    refine ⟨329649103059577036247549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 879064274825538763326797 329649103059577036247549)
                    ·
                      rfl

theorem cell22_962984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_962984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_962984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_962984 prefixEnd_962984 := by exact prefixLift 962984
  have htrace : WordTrace (prefixWord ++ tailWord_962984) baseStart_962984 baseEnd_962984 := by
    simpa [prefixWord, tailWord_962984, baseEnd_962984] using wordTrace_append hprefix tailTrace_962984
  have hstable : (prefixWord ++ tailWord_962984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_962984).length < 2 ^ (prefixWord ++ tailWord_962984).sum := by decide
  have hdescent : baseEnd_962984 < baseStart_962984 := by decide
  rcases family_descends (prefixWord ++ tailWord_962984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963023 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 3, 5]
def baseStart_963023 : Nat := 118140960795 + 963023 * 2 ^ 59
def prefixEnd_963023 : Nat := 4983230072969 + 3 ^ 40 * 963023 * 2
def baseEnd_963023 : Nat := 329662453556593934522429

theorem tailTrace_963023 : CollatzResearch.WordTrace tailWord_963023 prefixEnd_963023 329662453556593934522429 := by
  unfold tailWord_963023
  simp only [CollatzResearch.WordTrace]
  refine ⟨35124334390139617079285723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23416222926759744719523815 35124334390139617079285723)
  ·
    refine ⟨52686501585209425618928585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35124334390139617079285723 52686501585209425618928585)
    ·
      refine ⟨39514876188907069214196439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52686501585209425618928585 39514876188907069214196439)
      ·
        refine ⟨59272314283360603821294659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39514876188907069214196439 59272314283360603821294659)
        ·
          refine ⟨88908471425040905731941989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59272314283360603821294659 88908471425040905731941989)
          ·
            refine ⟨16670338392195169824739123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88908471425040905731941989 16670338392195169824739123)
            ·
              refine ⟨25005507588292754737108685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16670338392195169824739123 25005507588292754737108685)
              ·
                refine ⟨9377065345609783026415757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25005507588292754737108685 9377065345609783026415757)
                ·
                  refine ⟨3516399504603668634905909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9377065345609783026415757 3516399504603668634905909)
                  ·
                    refine ⟨329662453556593934522429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3516399504603668634905909 329662453556593934522429)
                    ·
                      rfl

theorem cell22_963023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_963023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963023 prefixEnd_963023 := by exact prefixLift 963023
  have htrace : WordTrace (prefixWord ++ tailWord_963023) baseStart_963023 baseEnd_963023 := by
    simpa [prefixWord, tailWord_963023, baseEnd_963023] using wordTrace_append hprefix tailTrace_963023
  have hstable : (prefixWord ++ tailWord_963023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963023).length < 2 ^ (prefixWord ++ tailWord_963023).sum := by decide
  have hdescent : baseEnd_963023 < baseStart_963023 := by decide
  rcases family_descends (prefixWord ++ tailWord_963023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963040 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 4, 3]
def baseStart_963040 : Nat := 118140960795 + 963040 * 2 ^ 59
def prefixEnd_963040 : Nat := 4983230072969 + 3 ^ 40 * 963040 * 2
def baseEnd_963040 : Nat := 329668273004011556847377

theorem tailTrace_963040 : CollatzResearch.WordTrace tailWord_963040 prefixEnd_963040 329668273004011556847377 := by
  unfold tailWord_963040
  simp only [CollatzResearch.WordTrace]
  refine ⟨17562477215539014491327287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23416636287385352655103049 17562477215539014491327287)
  ·
    refine ⟨26343715823308521736990931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17562477215539014491327287 26343715823308521736990931)
    ·
      refine ⟨39515573734962782605486397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26343715823308521736990931 39515573734962782605486397)
      ·
        refine ⟨14818340150611043477057399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39515573734962782605486397 14818340150611043477057399)
        ·
          refine ⟨22227510225916565215586099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14818340150611043477057399 22227510225916565215586099)
          ·
            refine ⟨33341265338874847823379149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22227510225916565215586099 33341265338874847823379149)
            ·
              refine ⟨12502974502078067933767181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33341265338874847823379149 12502974502078067933767181)
              ·
                refine ⟨4688615438279275475162693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12502974502078067933767181 4688615438279275475162693)
                ·
                  refine ⟨879115394677364151593005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4688615438279275475162693 879115394677364151593005)
                  ·
                    refine ⟨329668273004011556847377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 879115394677364151593005 329668273004011556847377)
                    ·
                      rfl

theorem cell22_963040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 4, 3].length) (baseStart_963040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963040 prefixEnd_963040 := by exact prefixLift 963040
  have htrace : WordTrace (prefixWord ++ tailWord_963040) baseStart_963040 baseEnd_963040 := by
    simpa [prefixWord, tailWord_963040, baseEnd_963040] using wordTrace_append hprefix tailTrace_963040
  have hstable : (prefixWord ++ tailWord_963040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963040).length < 2 ^ (prefixWord ++ tailWord_963040).sum := by decide
  have hdescent : baseEnd_963040 < baseStart_963040 := by decide
  rcases family_descends (prefixWord ++ tailWord_963040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963057 : List Nat := [1, 2, 2, 2, 3, 1, 3, 3, 2, 3]
def baseStart_963057 : Nat := 118140960795 + 963057 * 2 ^ 59
def prefixEnd_963057 : Nat := 4983230072969 + 3 ^ 40 * 963057 * 2
def baseEnd_963057 : Nat := 329674092451429179172325

theorem tailTrace_963057 : CollatzResearch.WordTrace tailWord_963057 prefixEnd_963057 329674092451429179172325 := by
  unfold tailWord_963057
  simp only [CollatzResearch.WordTrace]
  refine ⟨35125574472016440886023425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23417049648010960590682283 35125574472016440886023425)
  ·
    refine ⟨26344180854012330664517569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35125574472016440886023425 26344180854012330664517569)
    ·
      refine ⟨19758135640509247998388177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26344180854012330664517569 19758135640509247998388177)
      ·
        refine ⟨14818601730381935998791133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19758135640509247998388177 14818601730381935998791133)
        ·
          refine ⟨5556975648893225999546675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14818601730381935998791133 5556975648893225999546675)
          ·
            refine ⟨8335463473339838999320013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5556975648893225999546675 8335463473339838999320013)
            ·
              refine ⟨3125798802502439624745005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8335463473339838999320013 3125798802502439624745005)
              ·
                refine ⟨1172174550938414859279377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3125798802502439624745005 1172174550938414859279377)
                ·
                  refine ⟨879130913203811144459533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1172174550938414859279377 879130913203811144459533)
                  ·
                    refine ⟨329674092451429179172325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 879130913203811144459533 329674092451429179172325)
                    ·
                      rfl

theorem cell22_963057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_963057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963057 prefixEnd_963057 := by exact prefixLift 963057
  have htrace : WordTrace (prefixWord ++ tailWord_963057) baseStart_963057 baseEnd_963057 := by
    simpa [prefixWord, tailWord_963057, baseEnd_963057] using wordTrace_append hprefix tailTrace_963057
  have hstable : (prefixWord ++ tailWord_963057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963057).length < 2 ^ (prefixWord ++ tailWord_963057).sum := by decide
  have hdescent : baseEnd_963057 < baseStart_963057 := by decide
  rcases family_descends (prefixWord ++ tailWord_963057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963061 : List Nat := [1, 3, 5, 1, 2, 2, 1, 2, 1, 4]
def baseStart_963061 : Nat := 118140960795 + 963061 * 2 ^ 59
def prefixEnd_963061 : Nat := 4983230072969 + 3 ^ 40 * 963061 * 2
def baseEnd_963061 : Nat := 329675461733174502072313

theorem tailTrace_963061 : CollatzResearch.WordTrace tailWord_963061 prefixEnd_963061 329675461733174502072313 := by
  unfold tailWord_963061
  simp only [CollatzResearch.WordTrace]
  refine ⟨35125720364001949569169037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23417146909334633046112691 35125720364001949569169037)
  ·
    refine ⟨13172145136500731088438389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35125720364001949569169037 13172145136500731088438389)
    ·
      refine ⟨1234888606546943539541099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13172145136500731088438389 1234888606546943539541099)
      ·
        refine ⟨1852332909820415309311649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234888606546943539541099 1852332909820415309311649)
        ·
          refine ⟨1389249682365311481983737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852332909820415309311649 1389249682365311481983737)
          ·
            refine ⟨1041937261773983611487803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389249682365311481983737 1041937261773983611487803)
            ·
              refine ⟨1562905892660975417231705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041937261773983611487803 1562905892660975417231705)
              ·
                refine ⟨1172179419495731562923779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1562905892660975417231705 1172179419495731562923779)
                ·
                  refine ⟨1758269129243597344385669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172179419495731562923779 1758269129243597344385669)
                  ·
                    refine ⟨329675461733174502072313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1758269129243597344385669 329675461733174502072313)
                    ·
                      rfl

theorem cell22_963061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_963061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963061 prefixEnd_963061 := by exact prefixLift 963061
  have htrace : WordTrace (prefixWord ++ tailWord_963061) baseStart_963061 baseEnd_963061 := by
    simpa [prefixWord, tailWord_963061, baseEnd_963061] using wordTrace_append hprefix tailTrace_963061
  have hstable : (prefixWord ++ tailWord_963061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963061).length < 2 ^ (prefixWord ++ tailWord_963061).sum := by decide
  have hdescent : baseEnd_963061 < baseStart_963061 := by decide
  rcases family_descends (prefixWord ++ tailWord_963061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963074 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_963074 : Nat := 118140960795 + 963074 * 2 ^ 59
def prefixEnd_963074 : Nat := 4983230072969 + 3 ^ 40 * 963074 * 2
def baseEnd_963074 : Nat := 329679911898846801497273

theorem tailTrace_963074 : CollatzResearch.WordTrace tailWord_963074 prefixEnd_963074 329679911898846801497273 := by
  unfold tailWord_963074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8781548628238713197348069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23417463008636568526261517 8781548628238713197348069)
  ·
    refine ⟨1646540367794758724502763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8781548628238713197348069 1646540367794758724502763)
    ·
      refine ⟨2469810551692138086754145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1646540367794758724502763 2469810551692138086754145)
      ·
        refine ⟨1852357913769103565065609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2469810551692138086754145 1852357913769103565065609)
        ·
          refine ⟨1389268435326827673799207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1852357913769103565065609 1389268435326827673799207)
          ·
            refine ⟨2083902652990241510698811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389268435326827673799207 2083902652990241510698811)
            ·
              refine ⟨3125853979485362266048217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2083902652990241510698811 3125853979485362266048217)
              ·
                refine ⟨2344390484614021699536163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3125853979485362266048217 2344390484614021699536163)
                ·
                  refine ⟨3516585726921032549304245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2344390484614021699536163 3516585726921032549304245)
                  ·
                    refine ⟨329679911898846801497273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3516585726921032549304245 329679911898846801497273)
                    ·
                      rfl

theorem cell22_963074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_963074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963074 prefixEnd_963074 := by exact prefixLift 963074
  have htrace : WordTrace (prefixWord ++ tailWord_963074) baseStart_963074 baseEnd_963074 := by
    simpa [prefixWord, tailWord_963074, baseEnd_963074] using wordTrace_append hprefix tailTrace_963074
  have hstable : (prefixWord ++ tailWord_963074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963074).length < 2 ^ (prefixWord ++ tailWord_963074).sum := by decide
  have hdescent : baseEnd_963074 < baseStart_963074 := by decide
  rcases family_descends (prefixWord ++ tailWord_963074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963100 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_963100 : Nat := 118140960795 + 963100 * 2 ^ 59
def prefixEnd_963100 : Nat := 4983230072969 + 3 ^ 40 * 963100 * 2
def baseEnd_963100 : Nat := 329688812230191400347193

theorem tailTrace_963100 : CollatzResearch.WordTrace tailWord_963100 prefixEnd_963100 329688812230191400347193 := by
  unfold tailWord_963100
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563571405430329614919377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23418095207240439486559169 17563571405430329614919377)
  ·
    refine ⟨13172678554072747211189533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17563571405430329614919377 13172678554072747211189533)
    ·
      refine ⟨4939754457777280204196075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13172678554072747211189533 4939754457777280204196075)
      ·
        refine ⟨7409631686665920306294113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4939754457777280204196075 7409631686665920306294113)
        ·
          refine ⟨5557223764999440229720585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7409631686665920306294113 5557223764999440229720585)
          ·
            refine ⟨4167917823749580172290439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5557223764999440229720585 4167917823749580172290439)
            ·
              refine ⟨6251876735624370258435659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4167917823749580172290439 6251876735624370258435659)
              ·
                refine ⟨9377815103436555387653489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6251876735624370258435659 9377815103436555387653489)
                ·
                  refine ⟨7033361327577416540740117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9377815103436555387653489 7033361327577416540740117)
                  ·
                    refine ⟨329688812230191400347193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7033361327577416540740117 329688812230191400347193)
                    ·
                      rfl

theorem cell22_963100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_963100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963100 prefixEnd_963100 := by exact prefixLift 963100
  have htrace : WordTrace (prefixWord ++ tailWord_963100) baseStart_963100 baseEnd_963100 := by
    simpa [prefixWord, tailWord_963100, baseEnd_963100] using wordTrace_append hprefix tailTrace_963100
  have hstable : (prefixWord ++ tailWord_963100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963100).length < 2 ^ (prefixWord ++ tailWord_963100).sum := by decide
  have hdescent : baseEnd_963100 < baseStart_963100 := by decide
  rcases family_descends (prefixWord ++ tailWord_963100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963104 : List Nat := [2, 1, 1, 6, 3, 1, 1, 7]
def baseStart_963104 : Nat := 118140960795 + 963104 * 2 ^ 59
def prefixEnd_963104 : Nat := 4983230072969 + 3 ^ 40 * 963104 * 2
def baseEnd_963104 : Nat := 36632242390215191471909

theorem tailTrace_963104 : CollatzResearch.WordTrace tailWord_963104 prefixEnd_963104 36632242390215191471909 := by
  unfold tailWord_963104
  simp only [CollatzResearch.WordTrace]
  refine ⟨17563644351423083956492183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23418192468564111941989577 17563644351423083956492183)
  ·
    refine ⟨26345466527134625934738275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17563644351423083956492183 26345466527134625934738275)
    ·
      refine ⟨39518199790701938902107413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26345466527134625934738275 39518199790701938902107413)
      ·
        refine ⟨1852415615189153386036285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39518199790701938902107413 1852415615189153386036285)
        ·
          refine ⟨694655855695932519763607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1852415615189153386036285 694655855695932519763607)
          ·
            refine ⟨1041983783543898779645411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694655855695932519763607 1041983783543898779645411)
            ·
              refine ⟨1562975675315848169468117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1041983783543898779645411 1562975675315848169468117)
              ·
                refine ⟨36632242390215191471909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1562975675315848169468117 36632242390215191471909)
                ·
                  rfl

theorem cell22_963104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 7].length) (baseStart_963104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963104 prefixEnd_963104 := by exact prefixLift 963104
  have htrace : WordTrace (prefixWord ++ tailWord_963104) baseStart_963104 baseEnd_963104 := by
    simpa [prefixWord, tailWord_963104, baseEnd_963104] using wordTrace_append hprefix tailTrace_963104
  have hstable : (prefixWord ++ tailWord_963104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963104).length < 2 ^ (prefixWord ++ tailWord_963104).sum := by decide
  have hdescent : baseEnd_963104 < baseStart_963104 := by decide
  rcases family_descends (prefixWord ++ tailWord_963104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963149 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 5]
def baseStart_963149 : Nat := 118140960795 + 963149 * 2 ^ 59
def prefixEnd_963149 : Nat := 4983230072969 + 3 ^ 40 * 963149 * 2
def baseEnd_963149 : Nat := 109901861977190535290681

theorem tailTrace_963149 : CollatzResearch.WordTrace tailWord_963149 prefixEnd_963149 109901861977190535290681 := by
  unfold tailWord_963149
  simp only [CollatzResearch.WordTrace]
  refine ⟨35128929987683140598372501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23419286658455427065581667 35128929987683140598372501)
  ·
    refine ⟨1646668593172647215548711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35128929987683140598372501 1646668593172647215548711)
    ·
      refine ⟨2470002889758970823323067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1646668593172647215548711 2470002889758970823323067)
      ·
        refine ⟨3705004334638456234984601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470002889758970823323067 3705004334638456234984601)
        ·
          refine ⟨2778753250978842176238451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3705004334638456234984601 2778753250978842176238451)
          ·
            refine ⟨4168129876468263264357677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2778753250978842176238451 4168129876468263264357677)
            ·
              refine ⟨1563048703675598724134129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4168129876468263264357677 1563048703675598724134129)
              ·
                refine ⟨1172286527756699043100597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1563048703675598724134129 1172286527756699043100597)
                ·
                  refine ⟨109901861977190535290681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1172286527756699043100597 109901861977190535290681)
                  ·
                    rfl

theorem cell22_963149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_963149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963149 prefixEnd_963149 := by exact prefixLift 963149
  have htrace : WordTrace (prefixWord ++ tailWord_963149) baseStart_963149 baseEnd_963149 := by
    simpa [prefixWord, tailWord_963149, baseEnd_963149] using wordTrace_append hprefix tailTrace_963149
  have hstable : (prefixWord ++ tailWord_963149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963149).length < 2 ^ (prefixWord ++ tailWord_963149).sum := by decide
  have hdescent : baseEnd_963149 < baseStart_963149 := by decide
  rcases family_descends (prefixWord ++ tailWord_963149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963160 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 6]
def baseStart_963160 : Nat := 118140960795 + 963160 * 2 ^ 59
def prefixEnd_963160 : Nat := 4983230072969 + 3 ^ 40 * 963160 * 2
def baseEnd_963160 : Nat := 109903117152123747949003

theorem tailTrace_963160 : CollatzResearch.WordTrace tailWord_963160 prefixEnd_963160 109903117152123747949003 := by
  unfold tailWord_963160
  simp only [CollatzResearch.WordTrace]
  refine ⟨17564665595321644738511467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23419554127095526318015289 17564665595321644738511467)
  ·
    refine ⟨26346998392982467107767201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17564665595321644738511467 26346998392982467107767201)
    ·
      refine ⟨19760248794736850330825401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26346998392982467107767201 19760248794736850330825401)
      ·
        refine ⟨14820186596052637748119051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19760248794736850330825401 14820186596052637748119051)
        ·
          refine ⟨22230279894078956622178577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14820186596052637748119051 22230279894078956622178577)
          ·
            refine ⟨16672709920559217466633933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22230279894078956622178577 16672709920559217466633933)
            ·
              refine ⟨6252266220209706549987725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16672709920559217466633933 6252266220209706549987725)
              ·
                refine ⟨2344599832578639956245397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6252266220209706549987725 2344599832578639956245397)
                ·
                  refine ⟨109903117152123747949003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2344599832578639956245397 109903117152123747949003)
                  ·
                    rfl

theorem cell22_963160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_963160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963160 prefixEnd_963160 := by exact prefixLift 963160
  have htrace : WordTrace (prefixWord ++ tailWord_963160) baseStart_963160 baseEnd_963160 := by
    simpa [prefixWord, tailWord_963160, baseEnd_963160] using wordTrace_append hprefix tailTrace_963160
  have hstable : (prefixWord ++ tailWord_963160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963160).length < 2 ^ (prefixWord ++ tailWord_963160).sum := by decide
  have hdescent : baseEnd_963160 < baseStart_963160 := by decide
  rcases family_descends (prefixWord ++ tailWord_963160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963205 : List Nat := [1, 3, 1, 1, 4, 2, 10]
def baseStart_963205 : Nat := 118140960795 + 963205 * 2 ^ 59
def prefixEnd_963205 : Nat := 4983230072969 + 3 ^ 40 * 963205 * 2
def baseEnd_963205 : Nat := 12212027995407634313773

theorem tailTrace_963205 : CollatzResearch.WordTrace tailWord_963205 prefixEnd_963205 12212027995407634313773 := by
  unfold tailWord_963205
  simp only [CollatzResearch.WordTrace]
  refine ⟨35130972475480262162411069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23420648316986841441607379 35130972475480262162411069)
  ·
    refine ⟨13174114678305098310904151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35130972475480262162411069 13174114678305098310904151)
    ·
      refine ⟨19761172017457647466356227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13174114678305098310904151 19761172017457647466356227)
      ·
        refine ⟨29641758026186471199534341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19761172017457647466356227 29641758026186471199534341)
        ·
          refine ⟨5557829629909963349912689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29641758026186471199534341 5557829629909963349912689)
          ·
            refine ⟨4168372222432472512434517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5557829629909963349912689 4168372222432472512434517)
            ·
              refine ⟨12212027995407634313773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4168372222432472512434517 12212027995407634313773)
              ·
                rfl

theorem cell22_963205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 10].length) (baseStart_963205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963205 prefixEnd_963205 := by exact prefixLift 963205
  have htrace : WordTrace (prefixWord ++ tailWord_963205) baseStart_963205 baseEnd_963205 := by
    simpa [prefixWord, tailWord_963205, baseEnd_963205] using wordTrace_append hprefix tailTrace_963205
  have hstable : (prefixWord ++ tailWord_963205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963205).length < 2 ^ (prefixWord ++ tailWord_963205).sum := by decide
  have hdescent : baseEnd_963205 < baseStart_963205 := by decide
  rcases family_descends (prefixWord ++ tailWord_963205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963207 : List Nat := [1, 1, 4, 2, 1, 2, 3, 2, 2, 4]
def baseStart_963207 : Nat := 118140960795 + 963207 * 2 ^ 59
def prefixEnd_963207 : Nat := 4983230072969 + 3 ^ 40 * 963207 * 2
def baseEnd_963207 : Nat := 329725440516878787921865

theorem tailTrace_963207 : CollatzResearch.WordTrace tailWord_963207 prefixEnd_963207 329725440516878787921865 := by
  unfold tailWord_963207
  simp only [CollatzResearch.WordTrace]
  refine ⟨35131045421473016503983875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23420696947648677669322583 35131045421473016503983875)
  ·
    refine ⟨52696568132209524755975813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35131045421473016503983875 52696568132209524755975813)
    ·
      refine ⟨9880606524789285891745465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52696568132209524755975813 9880606524789285891745465)
      ·
        refine ⟨7410454893591964418809099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9880606524789285891745465 7410454893591964418809099)
        ·
          refine ⟨11115682340387946628213649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7410454893591964418809099 11115682340387946628213649)
          ·
            refine ⟨8336761755290959971160237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11115682340387946628213649 8336761755290959971160237)
            ·
              refine ⟨3126285658234109989185089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8336761755290959971160237 3126285658234109989185089)
              ·
                refine ⟨2344714243675582491888817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3126285658234109989185089 2344714243675582491888817)
                ·
                  refine ⟨1758535682756686868916613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344714243675582491888817 1758535682756686868916613)
                  ·
                    refine ⟨329725440516878787921865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1758535682756686868916613 329725440516878787921865)
                    ·
                      rfl

theorem cell22_963207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_963207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963207 prefixEnd_963207 := by exact prefixLift 963207
  have htrace : WordTrace (prefixWord ++ tailWord_963207) baseStart_963207 baseEnd_963207 := by
    simpa [prefixWord, tailWord_963207, baseEnd_963207] using wordTrace_append hprefix tailTrace_963207
  have hstable : (prefixWord ++ tailWord_963207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963207).length < 2 ^ (prefixWord ++ tailWord_963207).sum := by decide
  have hdescent : baseEnd_963207 < baseStart_963207 := by decide
  rcases family_descends (prefixWord ++ tailWord_963207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963235 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 4, 6]
def baseStart_963235 : Nat := 118140960795 + 963235 * 2 ^ 59
def prefixEnd_963235 : Nat := 4983230072969 + 3 ^ 40 * 963235 * 2
def baseEnd_963235 : Nat := 329735025489096048221779

theorem tailTrace_963235 : CollatzResearch.WordTrace tailWord_963235 prefixEnd_963235 329735025489096048221779 := by
  unfold tailWord_963235
  simp only [CollatzResearch.WordTrace]
  refine ⟨35132066665371577286003159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23421377776914384857335439 35132066665371577286003159)
  ·
    refine ⟨52698099998057365929004739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35132066665371577286003159 52698099998057365929004739)
    ·
      refine ⟨79047149997086048893507109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52698099998057365929004739 79047149997086048893507109)
      ·
        refine ⟨14821340624453634167532583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79047149997086048893507109 14821340624453634167532583)
        ·
          refine ⟨22232010936680451251298875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14821340624453634167532583 22232010936680451251298875)
          ·
            refine ⟨33348016405020676876948313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22232010936680451251298875 33348016405020676876948313)
            ·
              refine ⟨25011012303765507657711235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33348016405020676876948313 25011012303765507657711235)
              ·
                refine ⟨37516518455648261486566853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25011012303765507657711235 37516518455648261486566853)
                ·
                  refine ⟨7034347210434049028731285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37516518455648261486566853 7034347210434049028731285)
                  ·
                    refine ⟨329735025489096048221779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7034347210434049028731285 329735025489096048221779)
                    ·
                      rfl

theorem cell22_963235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_963235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963235 prefixEnd_963235 := by exact prefixLift 963235
  have htrace : WordTrace (prefixWord ++ tailWord_963235) baseStart_963235 baseEnd_963235 := by
    simpa [prefixWord, tailWord_963235, baseEnd_963235] using wordTrace_append hprefix tailTrace_963235
  have hstable : (prefixWord ++ tailWord_963235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963235).length < 2 ^ (prefixWord ++ tailWord_963235).sum := by decide
  have hdescent : baseEnd_963235 < baseStart_963235 := by decide
  rcases family_descends (prefixWord ++ tailWord_963235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963237 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 5, 3]
def baseStart_963237 : Nat := 118140960795 + 963237 * 2 ^ 59
def prefixEnd_963237 : Nat := 4983230072969 + 3 ^ 40 * 963237 * 2
def baseEnd_963237 : Nat := 329735710129968709671773

theorem tailTrace_963237 : CollatzResearch.WordTrace tailWord_963237 prefixEnd_963237 329735710129968709671773 := by
  unfold tailWord_963237
  simp only [CollatzResearch.WordTrace]
  refine ⟨35132139611364331627575965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23421426407576221085050643 35132139611364331627575965)
  ·
    refine ⟨13174552354261624360340987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35132139611364331627575965 13174552354261624360340987)
    ·
      refine ⟨19761828531392436540511481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13174552354261624360340987 19761828531392436540511481)
      ·
        refine ⟨14821371398544327405383611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19761828531392436540511481 14821371398544327405383611)
        ·
          refine ⟨22232057097816491108075417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14821371398544327405383611 22232057097816491108075417)
          ·
            refine ⟨16674042823362368331056563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22232057097816491108075417 16674042823362368331056563)
            ·
              refine ⟨25011064235043552496584845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16674042823362368331056563 25011064235043552496584845)
              ·
                refine ⟨9379149088141332186219317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25011064235043552496584845 9379149088141332186219317)
                ·
                  refine ⟨879295227013249892458061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9379149088141332186219317 879295227013249892458061)
                  ·
                    refine ⟨329735710129968709671773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 879295227013249892458061 329735710129968709671773)
                    ·
                      rfl

theorem cell22_963237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_963237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963237 prefixEnd_963237 := by exact prefixLift 963237
  have htrace : WordTrace (prefixWord ++ tailWord_963237) baseStart_963237 baseEnd_963237 := by
    simpa [prefixWord, tailWord_963237, baseEnd_963237] using wordTrace_append hprefix tailTrace_963237
  have hstable : (prefixWord ++ tailWord_963237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963237).length < 2 ^ (prefixWord ++ tailWord_963237).sum := by decide
  have hdescent : baseEnd_963237 < baseStart_963237 := by decide
  rcases family_descends (prefixWord ++ tailWord_963237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963374 : List Nat := [4, 1, 3, 2, 1, 1, 10]
def baseStart_963374 : Nat := 118140960795 + 963374 * 2 ^ 59
def prefixEnd_963374 : Nat := 4983230072969 + 3 ^ 40 * 963374 * 2
def baseEnd_963374 : Nat := 12214170667768371073939

theorem tailTrace_963374 : CollatzResearch.WordTrace tailWord_963374 prefixEnd_963374 12214170667768371073939 := by
  unfold tailWord_963374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4392142051483500503164147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23424757607912002683542117 4392142051483500503164147)
  ·
    refine ⟨6588213077225250754746221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4392142051483500503164147 6588213077225250754746221)
    ·
      refine ⟨2470579903959469033029833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6588213077225250754746221 2470579903959469033029833)
      ·
        refine ⟨1852934927969601774772375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2470579903959469033029833 1852934927969601774772375)
        ·
          refine ⟨2779402391954402662158563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1852934927969601774772375 2779402391954402662158563)
          ·
            refine ⟨4169103587931603993237845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779402391954402662158563 4169103587931603993237845)
            ·
              refine ⟨12214170667768371073939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4169103587931603993237845 12214170667768371073939)
              ·
                rfl

theorem cell22_963374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 10].length) (baseStart_963374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963374 prefixEnd_963374 := by exact prefixLift 963374
  have htrace : WordTrace (prefixWord ++ tailWord_963374) baseStart_963374 baseEnd_963374 := by
    simpa [prefixWord, tailWord_963374, baseEnd_963374] using wordTrace_append hprefix tailTrace_963374
  have hstable : (prefixWord ++ tailWord_963374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963374).length < 2 ^ (prefixWord ++ tailWord_963374).sum := by decide
  have hdescent : baseEnd_963374 < baseStart_963374 := by decide
  rcases family_descends (prefixWord ++ tailWord_963374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963380 : List Nat := [2, 5, 1, 1, 3, 1, 3, 2, 4]
def baseStart_963380 : Nat := 118140960795 + 963380 * 2 ^ 59
def prefixEnd_963380 : Nat := 4983230072969 + 3 ^ 40 * 963380 * 2
def baseEnd_963380 : Nat := 109928220650788001115445

theorem tailTrace_963380 : CollatzResearch.WordTrace tailWord_963380 prefixEnd_963380 109928220650788001115445 := by
  unfold tailWord_963380
  simp only [CollatzResearch.WordTrace]
  refine ⟨17568677624923133525015797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23424903499897511366687729 17568677624923133525015797)
  ·
    refine ⟨1647063527336543767970231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17568677624923133525015797 1647063527336543767970231)
    ·
      refine ⟨2470595291004815651955347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647063527336543767970231 2470595291004815651955347)
      ·
        refine ⟨3705892936507223477933021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2470595291004815651955347 3705892936507223477933021)
        ·
          refine ⟨1389709851190208804224883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3705892936507223477933021 1389709851190208804224883)
          ·
            refine ⟨2084564776785313206337325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389709851190208804224883 2084564776785313206337325)
            ·
              refine ⟨781711791294492452376497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2084564776785313206337325 781711791294492452376497)
              ·
                refine ⟨586283843470869339282373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 781711791294492452376497 586283843470869339282373)
                ·
                  refine ⟨109928220650788001115445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 586283843470869339282373 109928220650788001115445)
                  ·
                    rfl

theorem cell22_963380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_963380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963380 prefixEnd_963380 := by exact prefixLift 963380
  have htrace : WordTrace (prefixWord ++ tailWord_963380) baseStart_963380 baseEnd_963380 := by
    simpa [prefixWord, tailWord_963380, baseEnd_963380] using wordTrace_append hprefix tailTrace_963380
  have hstable : (prefixWord ++ tailWord_963380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963380).length < 2 ^ (prefixWord ++ tailWord_963380).sum := by decide
  have hdescent : baseEnd_963380 < baseStart_963380 := by decide
  rcases family_descends (prefixWord ++ tailWord_963380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963402 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_963402 : Nat := 118140960795 + 963402 * 2 ^ 59
def prefixEnd_963402 : Nat := 4983230072969 + 3 ^ 40 * 963402 * 2
def baseEnd_963402 : Nat := 109930731000654426432089

theorem tailTrace_963402 : CollatzResearch.WordTrace tailWord_963402 prefixEnd_963402 109930731000654426432089 := by
  unfold tailWord_963402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8784539413941641201833115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23425438437177709871554973 8784539413941641201833115)
  ·
    refine ⟨13176809120912461802749673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8784539413941641201833115 13176809120912461802749673)
    ·
      refine ⟨9882606840684346352062255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13176809120912461802749673 9882606840684346352062255)
      ·
        refine ⟨14823910261026519528093383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9882606840684346352062255 14823910261026519528093383)
        ·
          refine ⟨22235865391539779292140075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14823910261026519528093383 22235865391539779292140075)
          ·
            refine ⟨33353798087309668938210113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22235865391539779292140075 33353798087309668938210113)
            ·
              refine ⟨25015348565482251703657585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33353798087309668938210113 25015348565482251703657585)
              ·
                refine ⟨18761511424111688777743189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25015348565482251703657585 18761511424111688777743189)
                ·
                  refine ⟨109930731000654426432089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18761511424111688777743189 109930731000654426432089)
                  ·
                    rfl

theorem cell22_963402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_963402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963402 prefixEnd_963402 := by exact prefixLift 963402
  have htrace : WordTrace (prefixWord ++ tailWord_963402) baseStart_963402 baseEnd_963402 := by
    simpa [prefixWord, tailWord_963402, baseEnd_963402] using wordTrace_append hprefix tailTrace_963402
  have hstable : (prefixWord ++ tailWord_963402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963402).length < 2 ^ (prefixWord ++ tailWord_963402).sum := by decide
  have hdescent : baseEnd_963402 < baseStart_963402 := by decide
  rcases family_descends (prefixWord ++ tailWord_963402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963447 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 10]
def baseStart_963447 : Nat := 118140960795 + 963447 * 2 ^ 59
def prefixEnd_963447 : Nat := 4983230072969 + 3 ^ 40 * 963447 * 2
def baseEnd_963447 : Nat := 109935865807199387307043

theorem tailTrace_963447 : CollatzResearch.WordTrace tailWord_963447 prefixEnd_963447 109935865807199387307043 := by
  unfold tailWord_963447
  simp only [CollatzResearch.WordTrace]
  refine ⟨35139798940603537492720595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23426532627069024995147063 35139798940603537492720595)
  ·
    refine ⟨52709698410905306239080893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35139798940603537492720595 52709698410905306239080893)
    ·
      refine ⟨19766136904089489839655335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52709698410905306239080893 19766136904089489839655335)
      ·
        refine ⟨29649205356134234759483003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19766136904089489839655335 29649205356134234759483003)
        ·
          refine ⟨44473808034201352139224505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29649205356134234759483003 44473808034201352139224505)
          ·
            refine ⟨33355356025651014104418379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44473808034201352139224505 33355356025651014104418379)
            ·
              refine ⟨50033034038476521156627569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33355356025651014104418379 50033034038476521156627569)
              ·
                refine ⟨37524775528857390867470677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50033034038476521156627569 37524775528857390867470677)
                ·
                  refine ⟨109935865807199387307043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 37524775528857390867470677 109935865807199387307043)
                  ·
                    rfl

theorem cell22_963447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 10].length) (baseStart_963447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963447 prefixEnd_963447 := by exact prefixLift 963447
  have htrace : WordTrace (prefixWord ++ tailWord_963447) baseStart_963447 baseEnd_963447 := by
    simpa [prefixWord, tailWord_963447, baseEnd_963447] using wordTrace_append hprefix tailTrace_963447
  have hstable : (prefixWord ++ tailWord_963447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963447).length < 2 ^ (prefixWord ++ tailWord_963447).sum := by decide
  have hdescent : baseEnd_963447 < baseStart_963447 := by decide
  rcases family_descends (prefixWord ++ tailWord_963447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963449 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 3, 4]
def baseStart_963449 : Nat := 118140960795 + 963449 * 2 ^ 59
def prefixEnd_963449 : Nat := 4983230072969 + 3 ^ 40 * 963449 * 2
def baseEnd_963449 : Nat := 329808282062470823371123

theorem tailTrace_963449 : CollatzResearch.WordTrace tailWord_963449 prefixEnd_963449 329808282062470823371123 := by
  unfold tailWord_963449
  simp only [CollatzResearch.WordTrace]
  refine ⟨35139871886596291834293401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23426581257730861222862267 35139871886596291834293401)
  ·
    refine ⟨26354903914947218875720051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35139871886596291834293401 26354903914947218875720051)
    ·
      refine ⟨39532355872420828313580077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26354903914947218875720051 39532355872420828313580077)
      ·
        refine ⟨14824633452157810617592529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39532355872420828313580077 14824633452157810617592529)
        ·
          refine ⟨11118475089118357963194397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14824633452157810617592529 11118475089118357963194397)
          ·
            refine ⟨4169428158419384236197899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11118475089118357963194397 4169428158419384236197899)
            ·
              refine ⟨6254142237629076354296849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169428158419384236197899 6254142237629076354296849)
              ·
                refine ⟨4690606678221807265722637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6254142237629076354296849 4690606678221807265722637)
                ·
                  refine ⟨1758977504333177724645989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4690606678221807265722637 1758977504333177724645989)
                  ·
                    refine ⟨329808282062470823371123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1758977504333177724645989 329808282062470823371123)
                    ·
                      rfl

theorem cell22_963449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_963449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963449 prefixEnd_963449 := by exact prefixLift 963449
  have htrace : WordTrace (prefixWord ++ tailWord_963449) baseStart_963449 baseEnd_963449 := by
    simpa [prefixWord, tailWord_963449, baseEnd_963449] using wordTrace_append hprefix tailTrace_963449
  have hstable : (prefixWord ++ tailWord_963449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963449).length < 2 ^ (prefixWord ++ tailWord_963449).sum := by decide
  have hdescent : baseEnd_963449 < baseStart_963449 := by decide
  rcases family_descends (prefixWord ++ tailWord_963449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963464 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 8]
def baseStart_963464 : Nat := 118140960795 + 963464 * 2 ^ 59
def prefixEnd_963464 : Nat := 4983230072969 + 3 ^ 40 * 963464 * 2
def baseEnd_963464 : Nat := 109937805623005261415359

theorem tailTrace_963464 : CollatzResearch.WordTrace tailWord_963464 prefixEnd_963464 109937805623005261415359 := by
  unfold tailWord_963464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17570209490770974698044723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23426945987694632930726297 17570209490770974698044723)
  ·
    refine ⟨26355314236156462047067085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17570209490770974698044723 26355314236156462047067085)
    ·
      refine ⟨9883242838558673267650157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26355314236156462047067085 9883242838558673267650157)
      ·
        refine ⟨3706216064459502475368809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9883242838558673267650157 3706216064459502475368809)
        ·
          refine ⟨2779662048344626856526607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3706216064459502475368809 2779662048344626856526607)
          ·
            refine ⟨4169493072516940284789911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779662048344626856526607 4169493072516940284789911)
            ·
              refine ⟨6254239608775410427184867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4169493072516940284789911 6254239608775410427184867)
              ·
                refine ⟨9381359413163115640777301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6254239608775410427184867 9381359413163115640777301)
                ·
                  refine ⟨109937805623005261415359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9381359413163115640777301 109937805623005261415359)
                  ·
                    rfl

theorem cell22_963464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_963464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963464 prefixEnd_963464 := by exact prefixLift 963464
  have htrace : WordTrace (prefixWord ++ tailWord_963464) baseStart_963464 baseEnd_963464 := by
    simpa [prefixWord, tailWord_963464, baseEnd_963464] using wordTrace_append hprefix tailTrace_963464
  have hstable : (prefixWord ++ tailWord_963464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963464).length < 2 ^ (prefixWord ++ tailWord_963464).sum := by decide
  have hdescent : baseEnd_963464 < baseStart_963464 := by decide
  rcases family_descends (prefixWord ++ tailWord_963464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963466 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 3, 4]
def baseStart_963466 : Nat := 118140960795 + 963466 * 2 ^ 59
def prefixEnd_963466 : Nat := 4983230072969 + 3 ^ 40 * 963466 * 2
def baseEnd_963466 : Nat := 329814101509888445696071

theorem tailTrace_963466 : CollatzResearch.WordTrace tailWord_963466 prefixEnd_963466 329814101509888445696071 := by
  unfold tailWord_963466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8785122981883675934415563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23426994618356469158441501 8785122981883675934415563)
  ·
    refine ⟨13177684472825513901623345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8785122981883675934415563 13177684472825513901623345)
    ·
      refine ⟨9883263354619135426217509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13177684472825513901623345 9883263354619135426217509)
      ·
        refine ⟨1853111878991087892415783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9883263354619135426217509 1853111878991087892415783)
        ·
          refine ⟨2779667818486631838623675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1853111878991087892415783 2779667818486631838623675)
          ·
            refine ⟨4169501727729947757935513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2779667818486631838623675 4169501727729947757935513)
            ·
              refine ⟨3127126295797460818451635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4169501727729947757935513 3127126295797460818451635)
              ·
                refine ⟨4690689443696191227677453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3127126295797460818451635 4690689443696191227677453)
                ·
                  refine ⟨1759008541386071710379045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4690689443696191227677453 1759008541386071710379045)
                  ·
                    refine ⟨329814101509888445696071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1759008541386071710379045 329814101509888445696071)
                    ·
                      rfl

theorem cell22_963466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_963466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963466 prefixEnd_963466 := by exact prefixLift 963466
  have htrace : WordTrace (prefixWord ++ tailWord_963466) baseStart_963466 baseEnd_963466 := by
    simpa [prefixWord, tailWord_963466, baseEnd_963466] using wordTrace_append hprefix tailTrace_963466
  have hstable : (prefixWord ++ tailWord_963466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963466).length < 2 ^ (prefixWord ++ tailWord_963466).sum := by decide
  have hdescent : baseEnd_963466 < baseStart_963466 := by decide
  rcases family_descends (prefixWord ++ tailWord_963466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963479 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 1, 5]
def baseStart_963479 : Nat := 118140960795 + 963479 * 2 ^ 59
def prefixEnd_963479 : Nat := 4983230072969 + 3 ^ 40 * 963479 * 2
def baseEnd_963479 : Nat := 329818551675560745121031

theorem tailTrace_963479 : CollatzResearch.WordTrace tailWord_963479 prefixEnd_963479 329818551675560745121031 := by
  unfold tailWord_963479
  simp only [CollatzResearch.WordTrace]
  refine ⟨35140966076487606957885491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23427310717658404638590327 35140966076487606957885491)
  ·
    refine ⟨52711449114731410436828237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35140966076487606957885491 52711449114731410436828237)
    ·
      refine ⟨19766793418024278913810589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52711449114731410436828237 19766793418024278913810589)
      ·
        refine ⟨7412547531759104592678971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19766793418024278913810589 7412547531759104592678971)
        ·
          refine ⟨11118821297638656889018457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7412547531759104592678971 11118821297638656889018457)
          ·
            refine ⟨8339115973228992666763843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11118821297638656889018457 8339115973228992666763843)
            ·
              refine ⟨12508673959843489000145765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8339115973228992666763843 12508673959843489000145765)
              ·
                refine ⟨2345376367470654187527331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12508673959843489000145765 2345376367470654187527331)
                ·
                  refine ⟨3518064551205981281290997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2345376367470654187527331 3518064551205981281290997)
                  ·
                    refine ⟨329818551675560745121031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3518064551205981281290997 329818551675560745121031)
                    ·
                      rfl

theorem cell22_963479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_963479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963479 prefixEnd_963479 := by exact prefixLift 963479
  have htrace : WordTrace (prefixWord ++ tailWord_963479) baseStart_963479 baseEnd_963479 := by
    simpa [prefixWord, tailWord_963479, baseEnd_963479] using wordTrace_append hprefix tailTrace_963479
  have hstable : (prefixWord ++ tailWord_963479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963479).length < 2 ^ (prefixWord ++ tailWord_963479).sum := by decide
  have hdescent : baseEnd_963479 < baseStart_963479 := by decide
  rcases family_descends (prefixWord ++ tailWord_963479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963509 : List Nat := [1, 3, 3, 2, 1, 1, 2, 9]
def baseStart_963509 : Nat := 118140960795 + 963509 * 2 ^ 59
def prefixEnd_963509 : Nat := 4983230072969 + 3 ^ 40 * 963509 * 2
def baseEnd_963509 : Nat := 36647646809850074096771

theorem tailTrace_963509 : CollatzResearch.WordTrace tailWord_963509 prefixEnd_963509 36647646809850074096771 := by
  unfold tailWord_963509
  simp only [CollatzResearch.WordTrace]
  refine ⟨35142060266378922081477581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23428040177585948054318387 35142060266378922081477581)
  ·
    refine ⟨13178272599892095780554093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35142060266378922081477581 13178272599892095780554093)
    ·
      refine ⟨4941852224959535917707785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13178272599892095780554093 4941852224959535917707785)
      ·
        refine ⟨3706389168719651938280839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4941852224959535917707785 3706389168719651938280839)
        ·
          refine ⟨5559583753079477907421259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3706389168719651938280839 5559583753079477907421259)
          ·
            refine ⟨8339375629619216861131889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5559583753079477907421259 8339375629619216861131889)
            ·
              refine ⟨6254531722214412645848917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8339375629619216861131889 6254531722214412645848917)
              ·
                refine ⟨36647646809850074096771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6254531722214412645848917 36647646809850074096771)
                ·
                  rfl

theorem cell22_963509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 9].length) (baseStart_963509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963509 prefixEnd_963509 := by exact prefixLift 963509
  have htrace : WordTrace (prefixWord ++ tailWord_963509) baseStart_963509 baseEnd_963509 := by
    simpa [prefixWord, tailWord_963509, baseEnd_963509] using wordTrace_append hprefix tailTrace_963509
  have hstable : (prefixWord ++ tailWord_963509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963509).length < 2 ^ (prefixWord ++ tailWord_963509).sum := by decide
  have hdescent : baseEnd_963509 < baseStart_963509 := by decide
  rcases family_descends (prefixWord ++ tailWord_963509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963601 : List Nat := [1, 2, 2, 1, 1, 2, 1, 7, 1, 4]
def baseStart_963601 : Nat := 118140960795 + 963601 * 2 ^ 59
def prefixEnd_963601 : Nat := 4983230072969 + 3 ^ 40 * 963601 * 2
def baseEnd_963601 : Nat := 329860314768793093570657

theorem tailTrace_963601 : CollatzResearch.WordTrace tailWord_963601 prefixEnd_963601 329860314768793093570657 := by
  unfold tailWord_963601
  simp only [CollatzResearch.WordTrace]
  refine ⟨35145415782045621793826657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23430277188030414529217771 35145415782045621793826657)
  ·
    refine ⟨26359061836534216345369993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35145415782045621793826657 26359061836534216345369993)
    ·
      refine ⟨19769296377400662259027495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26359061836534216345369993 19769296377400662259027495)
      ·
        refine ⟨29653944566100993388541243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19769296377400662259027495 29653944566100993388541243)
        ·
          refine ⟨44480916849151490082811865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29653944566100993388541243 44480916849151490082811865)
          ·
            refine ⟨33360687636863617562108899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44480916849151490082811865 33360687636863617562108899)
            ·
              refine ⟨50041031455295426343163349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33360687636863617562108899 50041031455295426343163349)
              ·
                refine ⟨1172836674733486554917891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 50041031455295426343163349 1172836674733486554917891)
                ·
                  refine ⟨1759255012100229832376837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1172836674733486554917891 1759255012100229832376837)
                  ·
                    refine ⟨329860314768793093570657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1759255012100229832376837 329860314768793093570657)
                    ·
                      rfl

theorem cell22_963601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_963601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963601 prefixEnd_963601 := by exact prefixLift 963601
  have htrace : WordTrace (prefixWord ++ tailWord_963601) baseStart_963601 baseEnd_963601 := by
    simpa [prefixWord, tailWord_963601, baseEnd_963601] using wordTrace_append hprefix tailTrace_963601
  have hstable : (prefixWord ++ tailWord_963601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963601).length < 2 ^ (prefixWord ++ tailWord_963601).sum := by decide
  have hdescent : baseEnd_963601 < baseStart_963601 := by decide
  rcases family_descends (prefixWord ++ tailWord_963601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963740 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 5]
def baseStart_963740 : Nat := 118140960795 + 963740 * 2 ^ 59
def prefixEnd_963740 : Nat := 4983230072969 + 3 ^ 40 * 963740 * 2
def baseEnd_963740 : Nat := 109969299103147688115077

theorem tailTrace_963740 : CollatzResearch.WordTrace tailWord_963740 prefixEnd_963740 109969299103147688115077 := by
  unfold tailWord_963740
  simp only [CollatzResearch.WordTrace]
  refine ⟨17575242764271024266568337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23433657019028032355424449 17575242764271024266568337)
  ·
    refine ⟨13181432073203268199926253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17575242764271024266568337 13181432073203268199926253)
    ·
      refine ⟨4943037027451225574972345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13181432073203268199926253 4943037027451225574972345)
      ·
        refine ⟨3707277770588419181229259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4943037027451225574972345 3707277770588419181229259)
        ·
          refine ⟨5560916655882628771843889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3707277770588419181229259 5560916655882628771843889)
          ·
            refine ⟨4170687491911971578882917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5560916655882628771843889 4170687491911971578882917)
            ·
              refine ⟨782003904733494671040547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4170687491911971578882917 782003904733494671040547)
              ·
                refine ⟨1173005857100242006560821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 782003904733494671040547 1173005857100242006560821)
                ·
                  refine ⟨109969299103147688115077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1173005857100242006560821 109969299103147688115077)
                  ·
                    rfl

theorem cell22_963740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_963740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963740 prefixEnd_963740 := by exact prefixLift 963740
  have htrace : WordTrace (prefixWord ++ tailWord_963740) baseStart_963740 baseEnd_963740 := by
    simpa [prefixWord, tailWord_963740, baseEnd_963740] using wordTrace_append hprefix tailTrace_963740
  have hstable : (prefixWord ++ tailWord_963740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963740).length < 2 ^ (prefixWord ++ tailWord_963740).sum := by decide
  have hdescent : baseEnd_963740 < baseStart_963740 := by decide
  rcases family_descends (prefixWord ++ tailWord_963740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963781 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_963781 : Nat := 118140960795 + 963781 * 2 ^ 59
def prefixEnd_963781 : Nat := 4983230072969 + 3 ^ 40 * 963781 * 2
def baseEnd_963781 : Nat := 329921932447332624070105

theorem tailTrace_963781 : CollatzResearch.WordTrace tailWord_963781 prefixEnd_963781 329921932447332624070105 := by
  unfold tailWord_963781
  simp only [CollatzResearch.WordTrace]
  refine ⟨35151980921393512535379197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23434653947595675023586131 35151980921393512535379197)
  ·
    refine ⟨13181992845522567200767199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35151980921393512535379197 13181992845522567200767199)
    ·
      refine ⟨19772989268283850801150799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13181992845522567200767199 19772989268283850801150799)
      ·
        refine ⟨29659483902425776201726199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19772989268283850801150799 29659483902425776201726199)
        ·
          refine ⟨44489225853638664302589299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29659483902425776201726199 44489225853638664302589299)
          ·
            refine ⟨66733838780457996453883949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44489225853638664302589299 66733838780457996453883949)
            ·
              refine ⟨25025189542671748670206481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66733838780457996453883949 25025189542671748670206481)
              ·
                refine ⟨18768892157003811502654861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25025189542671748670206481 18768892157003811502654861)
                ·
                  refine ⟨7038334558876429313495573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18768892157003811502654861 7038334558876429313495573)
                  ·
                    refine ⟨329921932447332624070105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7038334558876429313495573 329921932447332624070105)
                    ·
                      rfl

theorem cell22_963781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_963781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963781 prefixEnd_963781 := by exact prefixLift 963781
  have htrace : WordTrace (prefixWord ++ tailWord_963781) baseStart_963781 baseEnd_963781 := by
    simpa [prefixWord, tailWord_963781, baseEnd_963781] using wordTrace_append hprefix tailTrace_963781
  have hstable : (prefixWord ++ tailWord_963781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963781).length < 2 ^ (prefixWord ++ tailWord_963781).sum := by decide
  have hdescent : baseEnd_963781 < baseStart_963781 := by decide
  rcases family_descends (prefixWord ++ tailWord_963781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963783 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 4, 3]
def baseStart_963783 : Nat := 118140960795 + 963783 * 2 ^ 59
def prefixEnd_963783 : Nat := 4983230072969 + 3 ^ 40 * 963783 * 2
def baseEnd_963783 : Nat := 329922617088205285520099

theorem tailTrace_963783 : CollatzResearch.WordTrace tailWord_963783 prefixEnd_963783 329922617088205285520099 := by
  unfold tailWord_963783
  simp only [CollatzResearch.WordTrace]
  refine ⟨35152053867386266876952003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23434702578257511251301335 35152053867386266876952003)
  ·
    refine ⟨52728080801079400315428005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35152053867386266876952003 52728080801079400315428005)
    ·
      refine ⟨9886515150202387559142751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52728080801079400315428005 9886515150202387559142751)
      ·
        refine ⟨14829772725303581338714127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9886515150202387559142751 14829772725303581338714127)
        ·
          refine ⟨22244659087955372008071191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14829772725303581338714127 22244659087955372008071191)
          ·
            refine ⟨33366988631933058012106787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22244659087955372008071191 33366988631933058012106787)
            ·
              refine ⟨50050482947899587018160181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33366988631933058012106787 50050482947899587018160181)
              ·
                refine ⟨4692232776365586282952517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50050482947899587018160181 4692232776365586282952517)
                ·
                  refine ⟨879793645568547428053597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4692232776365586282952517 879793645568547428053597)
                  ·
                    refine ⟨329922617088205285520099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 879793645568547428053597 329922617088205285520099)
                    ·
                      rfl

theorem cell22_963783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_963783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963783 prefixEnd_963783 := by exact prefixLift 963783
  have htrace : WordTrace (prefixWord ++ tailWord_963783) baseStart_963783 baseEnd_963783 := by
    simpa [prefixWord, tailWord_963783, baseEnd_963783] using wordTrace_append hprefix tailTrace_963783
  have hstable : (prefixWord ++ tailWord_963783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963783).length < 2 ^ (prefixWord ++ tailWord_963783).sum := by decide
  have hdescent : baseEnd_963783 < baseStart_963783 := by decide
  rcases family_descends (prefixWord ++ tailWord_963783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963800 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 1, 5]
def baseStart_963800 : Nat := 118140960795 + 963800 * 2 ^ 59
def prefixEnd_963800 : Nat := 4983230072969 + 3 ^ 40 * 963800 * 2
def baseEnd_963800 : Nat := 329928436535622907845047

theorem tailTrace_963800 : CollatzResearch.WordTrace tailWord_963800 prefixEnd_963800 329928436535622907845047 := by
  unfold tailWord_963800
  simp only [CollatzResearch.WordTrace]
  refine ⟨17576336954162339390160427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23435115938883119186880569 17576336954162339390160427)
  ·
    refine ⟨26364505431243509085240641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17576336954162339390160427 26364505431243509085240641)
    ·
      refine ⟨19773379073432631813930481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26364505431243509085240641 19773379073432631813930481)
      ·
        refine ⟨14830034305074473860447861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19773379073432631813930481 14830034305074473860447861)
        ·
          refine ⟨1390315716100731924416987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14830034305074473860447861 1390315716100731924416987)
          ·
            refine ⟨2085473574151097886625481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390315716100731924416987 2085473574151097886625481)
            ·
              refine ⟨1564105180613323414969111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2085473574151097886625481 1564105180613323414969111)
              ·
                refine ⟨2346157770919985122453667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564105180613323414969111 2346157770919985122453667)
                ·
                  refine ⟨3519236656379977683680501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2346157770919985122453667 3519236656379977683680501)
                  ·
                    refine ⟨329928436535622907845047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3519236656379977683680501 329928436535622907845047)
                    ·
                      rfl

theorem cell22_963800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_963800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963800 prefixEnd_963800 := by exact prefixLift 963800
  have htrace : WordTrace (prefixWord ++ tailWord_963800) baseStart_963800 baseEnd_963800 := by
    simpa [prefixWord, tailWord_963800, baseEnd_963800] using wordTrace_append hprefix tailTrace_963800
  have hstable : (prefixWord ++ tailWord_963800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963800).length < 2 ^ (prefixWord ++ tailWord_963800).sum := by decide
  have hdescent : baseEnd_963800 < baseStart_963800 := by decide
  rcases family_descends (prefixWord ++ tailWord_963800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963815 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 1, 6]
def baseStart_963815 : Nat := 118140960795 + 963815 * 2 ^ 59
def prefixEnd_963815 : Nat := 4983230072969 + 3 ^ 40 * 963815 * 2
def baseEnd_963815 : Nat := 329933571342167868720001

theorem tailTrace_963815 : CollatzResearch.WordTrace tailWord_963815 prefixEnd_963815 329933571342167868720001 := by
  unfold tailWord_963815
  simp only [CollatzResearch.WordTrace]
  refine ⟨35153221003270336342116899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23435480668846890894744599 35153221003270336342116899)
  ·
    refine ⟨52729831504905504513175349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35153221003270336342116899 52729831504905504513175349)
    ·
      refine ⟨4943421703584891048110189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52729831504905504513175349 4943421703584891048110189)
      ·
        refine ⟨1853783138844334143041321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4943421703584891048110189 1853783138844334143041321)
        ·
          refine ⟨1390337354133250607280991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1853783138844334143041321 1390337354133250607280991)
          ·
            refine ⟨2085506031199875910921487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1390337354133250607280991 2085506031199875910921487)
            ·
              refine ⟨3128259046799813866382231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2085506031199875910921487 3128259046799813866382231)
              ·
                refine ⟨4692388570199720799573347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3128259046799813866382231 4692388570199720799573347)
                ·
                  refine ⟨7038582855299581199360021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4692388570199720799573347 7038582855299581199360021)
                  ·
                    refine ⟨329933571342167868720001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7038582855299581199360021 329933571342167868720001)
                    ·
                      rfl

theorem cell22_963815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_963815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963815 prefixEnd_963815 := by exact prefixLift 963815
  have htrace : WordTrace (prefixWord ++ tailWord_963815) baseStart_963815 baseEnd_963815 := by
    simpa [prefixWord, tailWord_963815, baseEnd_963815] using wordTrace_append hprefix tailTrace_963815
  have hstable : (prefixWord ++ tailWord_963815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963815).length < 2 ^ (prefixWord ++ tailWord_963815).sum := by decide
  have hdescent : baseEnd_963815 < baseStart_963815 := by decide
  rcases family_descends (prefixWord ++ tailWord_963815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963845 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 3, 3]
def baseStart_963845 : Nat := 118140960795 + 963845 * 2 ^ 59
def prefixEnd_963845 : Nat := 4983230072969 + 3 ^ 40 * 963845 * 2
def baseEnd_963845 : Nat := 329943840955257790469909

theorem tailTrace_963845 : CollatzResearch.WordTrace tailWord_963845 prefixEnd_963845 329943840955257790469909 := by
  unfold tailWord_963845
  simp only [CollatzResearch.WordTrace]
  refine ⟨35154315193161651465708989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23436210128774434310472659 35154315193161651465708989)
  ·
    refine ⟨13182868197435619299640871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35154315193161651465708989 13182868197435619299640871)
    ·
      refine ⟨19774302296153428949461307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13182868197435619299640871 19774302296153428949461307)
      ·
        refine ⟨29661453444230143424191961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19774302296153428949461307 29661453444230143424191961)
        ·
          refine ⟨22246090083172607568143971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29661453444230143424191961 22246090083172607568143971)
          ·
            refine ⟨33369135124758911352215957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22246090083172607568143971 33369135124758911352215957)
            ·
              refine ⟨1564178208973073969635123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33369135124758911352215957 1564178208973073969635123)
              ·
                refine ⟨2346267313459610954452685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1564178208973073969635123 2346267313459610954452685)
                ·
                  refine ⟨879850242547354107919757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2346267313459610954452685 879850242547354107919757)
                  ·
                    refine ⟨329943840955257790469909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 879850242547354107919757 329943840955257790469909)
                    ·
                      rfl

theorem cell22_963845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_963845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963845 prefixEnd_963845 := by exact prefixLift 963845
  have htrace : WordTrace (prefixWord ++ tailWord_963845) baseStart_963845 baseEnd_963845 := by
    simpa [prefixWord, tailWord_963845, baseEnd_963845] using wordTrace_append hprefix tailTrace_963845
  have hstable : (prefixWord ++ tailWord_963845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963845).length < 2 ^ (prefixWord ++ tailWord_963845).sum := by decide
  have hdescent : baseEnd_963845 < baseStart_963845 := by decide
  rcases family_descends (prefixWord ++ tailWord_963845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963948 : List Nat := [2, 2, 1, 1, 5, 11]
def baseStart_963948 : Nat := 118140960795 + 963948 * 2 ^ 59
def prefixEnd_963948 : Nat := 4983230072969 + 3 ^ 40 * 963948 * 2
def baseEnd_963948 : Nat := 4073816048891356236353

theorem tailTrace_963948 : CollatzResearch.WordTrace tailWord_963948 prefixEnd_963948 4073816048891356236353 := by
  unfold tailWord_963948
  simp only [CollatzResearch.WordTrace]
  refine ⟨17579035955894250028354249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23438714607859000037805665 17579035955894250028354249)
  ·
    refine ⟨13184276966920687521265687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17579035955894250028354249 13184276966920687521265687)
    ·
      refine ⟨19776415450381031281898531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13184276966920687521265687 19776415450381031281898531)
      ·
        refine ⟨29664623175571546922847797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19776415450381031281898531 29664623175571546922847797)
        ·
          refine ⟨2781058422709832524016981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29664623175571546922847797 2781058422709832524016981)
          ·
            refine ⟨4073816048891356236353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2781058422709832524016981 4073816048891356236353)
            ·
              rfl

theorem cell22_963948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 11].length) (baseStart_963948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963948 prefixEnd_963948 := by exact prefixLift 963948
  have htrace : WordTrace (prefixWord ++ tailWord_963948) baseStart_963948 baseEnd_963948 := by
    simpa [prefixWord, tailWord_963948, baseEnd_963948] using wordTrace_append hprefix tailTrace_963948
  have hstable : (prefixWord ++ tailWord_963948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963948).length < 2 ^ (prefixWord ++ tailWord_963948).sum := by decide
  have hdescent : baseEnd_963948 < baseStart_963948 := by decide
  rcases family_descends (prefixWord ++ tailWord_963948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_963952 : List Nat := [2, 1, 1, 1, 4, 2, 4, 2, 2, 3]
def baseStart_963952 : Nat := 118140960795 + 963952 * 2 ^ 59
def prefixEnd_963952 : Nat := 4983230072969 + 3 ^ 40 * 963952 * 2
def baseEnd_963952 : Nat := 329980469241945178044581

theorem tailTrace_963952 : CollatzResearch.WordTrace tailWord_963952 prefixEnd_963952 329980469241945178044581 := by
  unfold tailWord_963952
  simp only [CollatzResearch.WordTrace]
  refine ⟨17579108901887004369927055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23438811869182672493236073 17579108901887004369927055)
  ·
    refine ⟨26368663352830506554890583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17579108901887004369927055 26368663352830506554890583)
    ·
      refine ⟨39552995029245759832335875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26368663352830506554890583 39552995029245759832335875)
      ·
        refine ⟨59329492543868639748503813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39552995029245759832335875 59329492543868639748503813)
        ·
          refine ⟨11124279851975369952844465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59329492543868639748503813 11124279851975369952844465)
          ·
            refine ⟨8343209888981527464633349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11124279851975369952844465 8343209888981527464633349)
            ·
              refine ⟨1564351854184036399618753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8343209888981527464633349 1564351854184036399618753)
              ·
                refine ⟨1173263890638027299714065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564351854184036399618753 1173263890638027299714065)
                ·
                  refine ⟨879947917978520474785549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1173263890638027299714065 879947917978520474785549)
                  ·
                    refine ⟨329980469241945178044581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 879947917978520474785549 329980469241945178044581)
                    ·
                      rfl

theorem cell22_963952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 2, 3].length) (baseStart_963952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_963952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_963952 prefixEnd_963952 := by exact prefixLift 963952
  have htrace : WordTrace (prefixWord ++ tailWord_963952) baseStart_963952 baseEnd_963952 := by
    simpa [prefixWord, tailWord_963952, baseEnd_963952] using wordTrace_append hprefix tailTrace_963952
  have hstable : (prefixWord ++ tailWord_963952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_963952).length < 2 ^ (prefixWord ++ tailWord_963952).sum := by decide
  have hdescent : baseEnd_963952 < baseStart_963952 := by decide
  rcases family_descends (prefixWord ++ tailWord_963952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964057 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 1, 4]
def baseStart_964057 : Nat := 118140960795 + 964057 * 2 ^ 59
def prefixEnd_964057 : Nat := 4983230072969 + 3 ^ 40 * 964057 * 2
def baseEnd_964057 : Nat := 330016412887759904169259

theorem tailTrace_964057 : CollatzResearch.WordTrace tailWord_964057 prefixEnd_964057 330016412887759904169259 := by
  unfold tailWord_964057
  simp only [CollatzResearch.WordTrace]
  refine ⟨35162047468393611672426425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23441364978929074448284283 35162047468393611672426425)
  ·
    refine ⟨26371535601295208754319819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35162047468393611672426425 26371535601295208754319819)
    ·
      refine ⟨39557303401942813131479729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26371535601295208754319819 39557303401942813131479729)
      ·
        refine ⟨29667977551457109848609797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39557303401942813131479729 29667977551457109848609797)
        ·
          refine ⟨5562745790898208096614337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29667977551457109848609797 5562745790898208096614337)
          ·
            refine ⟨4172059343173656072460753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5562745790898208096614337 4172059343173656072460753)
            ·
              refine ⟨3129044507380242054345565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4172059343173656072460753 3129044507380242054345565)
              ·
                refine ⟨1173391690267590770379587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3129044507380242054345565 1173391690267590770379587)
                ·
                  refine ⟨1760087535401386155569381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173391690267590770379587 1760087535401386155569381)
                  ·
                    refine ⟨330016412887759904169259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1760087535401386155569381 330016412887759904169259)
                    ·
                      rfl

theorem cell22_964057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_964057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964057 prefixEnd_964057 := by exact prefixLift 964057
  have htrace : WordTrace (prefixWord ++ tailWord_964057) baseStart_964057 baseEnd_964057 := by
    simpa [prefixWord, tailWord_964057, baseEnd_964057] using wordTrace_append hprefix tailTrace_964057
  have hstable : (prefixWord ++ tailWord_964057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964057).length < 2 ^ (prefixWord ++ tailWord_964057).sum := by decide
  have hdescent : baseEnd_964057 < baseStart_964057 := by decide
  rcases family_descends (prefixWord ++ tailWord_964057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964145 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 9]
def baseStart_964145 : Nat := 118140960795 + 964145 * 2 ^ 59
def prefixEnd_964145 : Nat := 4983230072969 + 3 ^ 40 * 964145 * 2
def baseEnd_964145 : Nat := 110015512362052335989663

theorem tailTrace_964145 : CollatzResearch.WordTrace tailWord_964145 prefixEnd_964145 110015512362052335989663 := by
  unfold tailWord_964145
  simp only [CollatzResearch.WordTrace]
  refine ⟨35165257092074802701629889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23443504728049868467753259 35165257092074802701629889)
  ·
    refine ⟨26373942819056102026222417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35165257092074802701629889 26373942819056102026222417)
    ·
      refine ⟨19780457114292076519666813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26373942819056102026222417 19780457114292076519666813)
      ·
        refine ⟨7417671417859528694875055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19780457114292076519666813 7417671417859528694875055)
        ·
          refine ⟨11126507126789293042312583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7417671417859528694875055 11126507126789293042312583)
          ·
            refine ⟨16689760690183939563468875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11126507126789293042312583 16689760690183939563468875)
            ·
              refine ⟨25034641035275909345203313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16689760690183939563468875 25034641035275909345203313)
              ·
                refine ⟨18775980776456932008902485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25034641035275909345203313 18775980776456932008902485)
                ·
                  refine ⟨110015512362052335989663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18775980776456932008902485 110015512362052335989663)
                  ·
                    rfl

theorem cell22_964145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_964145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964145 prefixEnd_964145 := by exact prefixLift 964145
  have htrace : WordTrace (prefixWord ++ tailWord_964145) baseStart_964145 baseEnd_964145 := by
    simpa [prefixWord, tailWord_964145, baseEnd_964145] using wordTrace_append hprefix tailTrace_964145
  have hstable : (prefixWord ++ tailWord_964145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964145).length < 2 ^ (prefixWord ++ tailWord_964145).sum := by decide
  have hdescent : baseEnd_964145 < baseStart_964145 := by decide
  rcases family_descends (prefixWord ++ tailWord_964145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964149 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 3, 3]
def baseStart_964149 : Nat := 118140960795 + 964149 * 2 ^ 59
def prefixEnd_964149 : Nat := 4983230072969 + 3 ^ 40 * 964149 * 2
def baseEnd_964149 : Nat := 330047906367902330868977

theorem tailTrace_964149 : CollatzResearch.WordTrace tailWord_964149 prefixEnd_964149 330047906367902330868977 := by
  unfold tailWord_964149
  simp only [CollatzResearch.WordTrace]
  refine ⟨35165402984060311384775501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23443601989373540923183667 35165402984060311384775501)
  ·
    refine ⟨13187026119022616769290813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35165402984060311384775501 13187026119022616769290813)
    ·
      refine ⟨4945134794633481288484055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13187026119022616769290813 4945134794633481288484055)
      ·
        refine ⟨7417702191950221932726083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4945134794633481288484055 7417702191950221932726083)
        ·
          refine ⟨11126553287925332899089125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7417702191950221932726083 11126553287925332899089125)
          ·
            refine ⟨2086228741485999918579211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11126553287925332899089125 2086228741485999918579211)
            ·
              refine ⟨3129343112228999877868817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086228741485999918579211 3129343112228999877868817)
              ·
                refine ⟨2347007334171749908401613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3129343112228999877868817 2347007334171749908401613)
                ·
                  refine ⟨880127750314406215650605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2347007334171749908401613 880127750314406215650605)
                  ·
                    refine ⟨330047906367902330868977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 880127750314406215650605 330047906367902330868977)
                    ·
                      rfl

theorem cell22_964149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_964149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964149 prefixEnd_964149 := by exact prefixLift 964149
  have htrace : WordTrace (prefixWord ++ tailWord_964149) baseStart_964149 baseEnd_964149 := by
    simpa [prefixWord, tailWord_964149, baseEnd_964149] using wordTrace_append hprefix tailTrace_964149
  have hstable : (prefixWord ++ tailWord_964149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964149).length < 2 ^ (prefixWord ++ tailWord_964149).sum := by decide
  have hdescent : baseEnd_964149 < baseStart_964149 := by decide
  rcases family_descends (prefixWord ++ tailWord_964149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964160 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_964160 : Nat := 118140960795 + 964160 * 2 ^ 59
def prefixEnd_964160 : Nat := 4983230072969 + 3 ^ 40 * 964160 * 2
def baseEnd_964160 : Nat := 330051671892701968843943

theorem tailTrace_964160 : CollatzResearch.WordTrace tailWord_964160 prefixEnd_964160 330051671892701968843943 := by
  unfold tailWord_964160
  simp only [CollatzResearch.WordTrace]
  refine ⟨17582902093510230131712967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23443869458013640175617289 17582902093510230131712967)
  ·
    refine ⟨26374353140265345197569451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17582902093510230131712967 26374353140265345197569451)
    ·
      refine ⟨39561529710398017796354177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26374353140265345197569451 39561529710398017796354177)
      ·
        refine ⟨29671147282798513347265633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39561529710398017796354177 29671147282798513347265633)
        ·
          refine ⟨22253360462098885010449225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29671147282798513347265633 22253360462098885010449225)
          ·
            refine ⟨16690020346574163757836919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22253360462098885010449225 16690020346574163757836919)
            ·
              refine ⟨25035030519861245636755379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16690020346574163757836919 25035030519861245636755379)
              ·
                refine ⟨37552545779791868455133069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25035030519861245636755379 37552545779791868455133069)
                ·
                  refine ⟨14082204667421950670674901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37552545779791868455133069 14082204667421950670674901)
                  ·
                    refine ⟨330051671892701968843943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14082204667421950670674901 330051671892701968843943)
                    ·
                      rfl

theorem cell22_964160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_964160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964160 prefixEnd_964160 := by exact prefixLift 964160
  have htrace : WordTrace (prefixWord ++ tailWord_964160) baseStart_964160 baseEnd_964160 := by
    simpa [prefixWord, tailWord_964160, baseEnd_964160] using wordTrace_append hprefix tailTrace_964160
  have hstable : (prefixWord ++ tailWord_964160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964160).length < 2 ^ (prefixWord ++ tailWord_964160).sum := by decide
  have hdescent : baseEnd_964160 < baseStart_964160 := by decide
  rcases family_descends (prefixWord ++ tailWord_964160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964256 : List Nat := [2, 1, 1, 4, 3, 2, 1, 3, 2, 3]
def baseStart_964256 : Nat := 118140960795 + 964256 * 2 ^ 59
def prefixEnd_964256 : Nat := 4983230072969 + 3 ^ 40 * 964256 * 2
def baseEnd_964256 : Nat := 330084534654589718443649

theorem tailTrace_964256 : CollatzResearch.WordTrace tailWord_964256 prefixEnd_964256 330084534654589718443649 := by
  unfold tailWord_964256
  simp only [CollatzResearch.WordTrace]
  refine ⟨17584652797336334329460311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23446203729781779105947081 17584652797336334329460311)
  ·
    refine ⟨26376979196004501494190467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17584652797336334329460311 26376979196004501494190467)
    ·
      refine ⟨39565468794006752241285701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26376979196004501494190467 39565468794006752241285701)
      ·
        refine ⟨7418525398876266045241069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39565468794006752241285701 7418525398876266045241069)
        ·
          refine ⟨2781947024578599766965401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7418525398876266045241069 2781947024578599766965401)
          ·
            refine ⟨2086460268433949825224051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2781947024578599766965401 2086460268433949825224051)
            ·
              refine ⟨3129690402650924737836077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2086460268433949825224051 3129690402650924737836077)
              ·
                refine ⟨1173633900994096776688529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3129690402650924737836077 1173633900994096776688529)
                ·
                  refine ⟨880225425745572582516397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1173633900994096776688529 880225425745572582516397)
                  ·
                    refine ⟨330084534654589718443649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 880225425745572582516397 330084534654589718443649)
                    ·
                      rfl

theorem cell22_964256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 3, 2, 3].length) (baseStart_964256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964256 prefixEnd_964256 := by exact prefixLift 964256
  have htrace : WordTrace (prefixWord ++ tailWord_964256) baseStart_964256 baseEnd_964256 := by
    simpa [prefixWord, tailWord_964256, baseEnd_964256] using wordTrace_append hprefix tailTrace_964256
  have hstable : (prefixWord ++ tailWord_964256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964256).length < 2 ^ (prefixWord ++ tailWord_964256).sum := by decide
  have hdescent : baseEnd_964256 < baseStart_964256 := by decide
  rcases family_descends (prefixWord ++ tailWord_964256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964314 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_964314 : Nat := 118140960795 + 964314 * 2 ^ 59
def prefixEnd_964314 : Nat := 4983230072969 + 3 ^ 40 * 964314 * 2
def baseEnd_964314 : Nat := 110034796413298966831157

theorem tailTrace_964314 : CollatzResearch.WordTrace tailWord_964314 prefixEnd_964314 110034796413298966831157 := by
  unfold tailWord_964314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8792855257115636141132999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23447614018975029709687997 8792855257115636141132999)
  ·
    refine ⟨13189282885673454211699499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8792855257115636141132999 13189282885673454211699499)
    ·
      refine ⟨19783924328510181317549249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13189282885673454211699499 19783924328510181317549249)
      ·
        refine ⟨14837943246382635988161937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19783924328510181317549249 14837943246382635988161937)
        ·
          refine ⟨11128457434786976991121453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14837943246382635988161937 11128457434786976991121453)
          ·
            refine ⟨4173171538045116371670545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11128457434786976991121453 4173171538045116371670545)
            ·
              refine ⟨3129878653533837278752909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4173171538045116371670545 3129878653533837278752909)
              ·
                refine ⟨1173704495075188979532341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3129878653533837278752909 1173704495075188979532341)
                ·
                  refine ⟨110034796413298966831157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1173704495075188979532341 110034796413298966831157)
                  ·
                    rfl

theorem cell22_964314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_964314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964314 prefixEnd_964314 := by exact prefixLift 964314
  have htrace : WordTrace (prefixWord ++ tailWord_964314) baseStart_964314 baseEnd_964314 := by
    simpa [prefixWord, tailWord_964314, baseEnd_964314] using wordTrace_append hprefix tailTrace_964314
  have hstable : (prefixWord ++ tailWord_964314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964314).length < 2 ^ (prefixWord ++ tailWord_964314).sum := by decide
  have hdescent : baseEnd_964314 < baseStart_964314 := by decide
  rcases family_descends (prefixWord ++ tailWord_964314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964357 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_964357 : Nat := 118140960795 + 964357 * 2 ^ 59
def prefixEnd_964357 : Nat := 4983230072969 + 3 ^ 40 * 964357 * 2
def baseEnd_964357 : Nat := 330119109018659121668339

theorem tailTrace_964357 : CollatzResearch.WordTrace tailWord_964357 prefixEnd_964357 330119109018659121668339 := by
  unfold tailWord_964357
  simp only [CollatzResearch.WordTrace]
  refine ⟨35172989367306762908347325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23448659578204508605564883 35172989367306762908347325)
  ·
    refine ⟨13189871012740036090630247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35172989367306762908347325 13189871012740036090630247)
    ·
      refine ⟨19784806519110054135945371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13189871012740036090630247 19784806519110054135945371)
      ·
        refine ⟨29677209778665081203918057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19784806519110054135945371 29677209778665081203918057)
        ·
          refine ⟨22257907333998810902938543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29677209778665081203918057 22257907333998810902938543)
          ·
            refine ⟨33386861000998216354407815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22257907333998810902938543 33386861000998216354407815)
            ·
              refine ⟨50080291501497324531611723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33386861000998216354407815 50080291501497324531611723)
              ·
                refine ⟨75120437252245986797417585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50080291501497324531611723 75120437252245986797417585)
                ·
                  refine ⟨56340327939184490098063189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75120437252245986797417585 56340327939184490098063189)
                  ·
                    refine ⟨330119109018659121668339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 56340327939184490098063189 330119109018659121668339)
                    ·
                      rfl

theorem cell22_964357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_964357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964357 prefixEnd_964357 := by exact prefixLift 964357
  have htrace : WordTrace (prefixWord ++ tailWord_964357) baseStart_964357 baseEnd_964357 := by
    simpa [prefixWord, tailWord_964357, baseEnd_964357] using wordTrace_append hprefix tailTrace_964357
  have hstable : (prefixWord ++ tailWord_964357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964357).length < 2 ^ (prefixWord ++ tailWord_964357).sum := by decide
  have hdescent : baseEnd_964357 < baseStart_964357 := by decide
  rcases family_descends (prefixWord ++ tailWord_964357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964389 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_964389 : Nat := 118140960795 + 964389 * 2 ^ 59
def prefixEnd_964389 : Nat := 4983230072969 + 3 ^ 40 * 964389 * 2
def baseEnd_964389 : Nat := 330130063272621704868241

theorem tailTrace_964389 : CollatzResearch.WordTrace tailWord_964389 prefixEnd_964389 330130063272621704868241 := by
  unfold tailWord_964389
  simp only [CollatzResearch.WordTrace]
  refine ⟨35174156503190832373512221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23449437668793888249008147 35174156503190832373512221)
  ·
    refine ⟨13190308688696562140067083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35174156503190832373512221 13190308688696562140067083)
    ·
      refine ⟨19785463033044843210100625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13190308688696562140067083 19785463033044843210100625)
      ·
        refine ⟨14839097274783632407575469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19785463033044843210100625 14839097274783632407575469)
        ·
          refine ⟨5564661478043862152840801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14839097274783632407575469 5564661478043862152840801)
          ·
            refine ⟨4173496108532896614630601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5564661478043862152840801 4173496108532896614630601)
            ·
              refine ⟨3130122081399672460972951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4173496108532896614630601 3130122081399672460972951)
              ·
                refine ⟨4695183122099508691459427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3130122081399672460972951 4695183122099508691459427)
                ·
                  refine ⟨7042774683149263037189141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695183122099508691459427 7042774683149263037189141)
                  ·
                    refine ⟨330130063272621704868241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7042774683149263037189141 330130063272621704868241)
                    ·
                      rfl

theorem cell22_964389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_964389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964389 prefixEnd_964389 := by exact prefixLift 964389
  have htrace : WordTrace (prefixWord ++ tailWord_964389) baseStart_964389 baseEnd_964389 := by
    simpa [prefixWord, tailWord_964389, baseEnd_964389] using wordTrace_append hprefix tailTrace_964389
  have hstable : (prefixWord ++ tailWord_964389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964389).length < 2 ^ (prefixWord ++ tailWord_964389).sum := by decide
  have hdescent : baseEnd_964389 < baseStart_964389 := by decide
  rcases family_descends (prefixWord ++ tailWord_964389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964453 : List Nat := [1, 3, 1, 3, 1, 1, 1, 7, 1, 3]
def baseStart_964453 : Nat := 118140960795 + 964453 * 2 ^ 59
def prefixEnd_964453 : Nat := 4983230072969 + 3 ^ 40 * 964453 * 2
def baseEnd_964453 : Nat := 330151971780546871268045

theorem tailTrace_964453 : CollatzResearch.WordTrace tailWord_964453 prefixEnd_964453 330151971780546871268045 := by
  unfold tailWord_964453
  simp only [CollatzResearch.WordTrace]
  refine ⟨35176490774958971303842013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23450993849972647535894675 35176490774958971303842013)
  ·
    refine ⟨13191184040609614238940755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35176490774958971303842013 13191184040609614238940755)
    ·
      refine ⟨19786776060914421358411133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13191184040609614238940755 19786776060914421358411133)
      ·
        refine ⟨7420041022842908009404175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19786776060914421358411133 7420041022842908009404175)
        ·
          refine ⟨11130061534264362014106263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7420041022842908009404175 11130061534264362014106263)
          ·
            refine ⟨16695092301396543021159395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11130061534264362014106263 16695092301396543021159395)
            ·
              refine ⟨25042638452094814531739093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16695092301396543021159395 25042638452094814531739093)
              ·
                refine ⟨586936838720972215587635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25042638452094814531739093 586936838720972215587635)
                ·
                  refine ⟨880405258081458323381453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586936838720972215587635 880405258081458323381453)
                  ·
                    refine ⟨330151971780546871268045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 880405258081458323381453 330151971780546871268045)
                    ·
                      rfl

theorem cell22_964453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_964453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964453 prefixEnd_964453 := by exact prefixLift 964453
  have htrace : WordTrace (prefixWord ++ tailWord_964453) baseStart_964453 baseEnd_964453 := by
    simpa [prefixWord, tailWord_964453, baseEnd_964453] using wordTrace_append hprefix tailTrace_964453
  have hstable : (prefixWord ++ tailWord_964453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964453).length < 2 ^ (prefixWord ++ tailWord_964453).sum := by decide
  have hdescent : baseEnd_964453 < baseStart_964453 := by decide
  rcases family_descends (prefixWord ++ tailWord_964453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964464 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_964464 : Nat := 118140960795 + 964464 * 2 ^ 59
def prefixEnd_964464 : Nat := 4983230072969 + 3 ^ 40 * 964464 * 2
def baseEnd_964464 : Nat := 330155737305346509243011

theorem tailTrace_964464 : CollatzResearch.WordTrace tailWord_964464 prefixEnd_964464 330155737305346509243011 := by
  unfold tailWord_964464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17588445988959560091246223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23451261318612746788328297 17588445988959560091246223)
  ·
    refine ⟨26382668983439340136869335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17588445988959560091246223 26382668983439340136869335)
    ·
      refine ⟨39574003475159010205304003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26382668983439340136869335 39574003475159010205304003)
      ·
        refine ⟨59361005212738515307956005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39574003475159010205304003 59361005212738515307956005)
        ·
          refine ⟨11130188477388471620241751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59361005212738515307956005 11130188477388471620241751)
          ·
            refine ⟨16695282716082707430362627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11130188477388471620241751 16695282716082707430362627)
            ·
              refine ⟨25042924074124061145543941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16695282716082707430362627 25042924074124061145543941)
              ·
                refine ⟨4695548263898261464789489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25042924074124061145543941 4695548263898261464789489)
                ·
                  refine ⟨3521661197923696098592117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4695548263898261464789489 3521661197923696098592117)
                  ·
                    refine ⟨330155737305346509243011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3521661197923696098592117 330155737305346509243011)
                    ·
                      rfl

theorem cell22_964464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_964464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964464 prefixEnd_964464 := by exact prefixLift 964464
  have htrace : WordTrace (prefixWord ++ tailWord_964464) baseStart_964464 baseEnd_964464 := by
    simpa [prefixWord, tailWord_964464, baseEnd_964464] using wordTrace_append hprefix tailTrace_964464
  have hstable : (prefixWord ++ tailWord_964464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964464).length < 2 ^ (prefixWord ++ tailWord_964464).sum := by decide
  have hdescent : baseEnd_964464 < baseStart_964464 := by decide
  rcases family_descends (prefixWord ++ tailWord_964464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964524 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_964524 : Nat := 118140960795 + 964524 * 2 ^ 59
def prefixEnd_964524 : Nat := 4983230072969 + 3 ^ 40 * 964524 * 2
def baseEnd_964524 : Nat := 330176276531526352742827

theorem tailTrace_964524 : CollatzResearch.WordTrace tailWord_964524 prefixEnd_964524 330176276531526352742827 := by
  unfold tailWord_964524
  simp only [CollatzResearch.WordTrace]
  refine ⟨17589540178850875214838313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23452720238467833619784417 17589540178850875214838313)
  ·
    refine ⟨13192155134138156411128735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17589540178850875214838313 13192155134138156411128735)
    ·
      refine ⟨19788232701207234616693103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13192155134138156411128735 19788232701207234616693103)
      ·
        refine ⟨29682349051810851925039655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19788232701207234616693103 29682349051810851925039655)
        ·
          refine ⟨44523523577716277887559483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29682349051810851925039655 44523523577716277887559483)
          ·
            refine ⟨66785285366574416831339225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44523523577716277887559483 66785285366574416831339225)
            ·
              refine ⟨50088964024930812623504419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66785285366574416831339225 50088964024930812623504419)
              ·
                refine ⟨75133446037396218935256629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50088964024930812623504419 75133446037396218935256629)
                ·
                  refine ⟨7043760566005895525180309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75133446037396218935256629 7043760566005895525180309)
                  ·
                    refine ⟨330176276531526352742827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7043760566005895525180309 330176276531526352742827)
                    ·
                      rfl

theorem cell22_964524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_964524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964524 prefixEnd_964524 := by exact prefixLift 964524
  have htrace : WordTrace (prefixWord ++ tailWord_964524) baseStart_964524 baseEnd_964524 := by
    simpa [prefixWord, tailWord_964524, baseEnd_964524] using wordTrace_append hprefix tailTrace_964524
  have hstable : (prefixWord ++ tailWord_964524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964524).length < 2 ^ (prefixWord ++ tailWord_964524).sum := by decide
  have hdescent : baseEnd_964524 < baseStart_964524 := by decide
  rcases family_descends (prefixWord ++ tailWord_964524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964541 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_964541 : Nat := 118140960795 + 964541 * 2 ^ 59
def prefixEnd_964541 : Nat := 4983230072969 + 3 ^ 40 * 964541 * 2
def baseEnd_964541 : Nat := 330182095978943975067775

theorem tailTrace_964541 : CollatzResearch.WordTrace tailWord_964541 prefixEnd_964541 330182095978943975067775 := by
  unfold tailWord_964541
  simp only [CollatzResearch.WordTrace]
  refine ⟨35179700398640162333045477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23453133599093441555363651 35179700398640162333045477)
  ·
    refine ⟨6596193824745030437446027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35179700398640162333045477 6596193824745030437446027)
    ·
      refine ⟨9894290737117545656169041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6596193824745030437446027 9894290737117545656169041)
      ·
        refine ⟨7420718052838159242126781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9894290737117545656169041 7420718052838159242126781)
        ·
          refine ⟨2782769269814309715797543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7420718052838159242126781 2782769269814309715797543)
          ·
            refine ⟨4174153904721464573696315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2782769269814309715797543 4174153904721464573696315)
            ·
              refine ⟨6261230857082196860544473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4174153904721464573696315 6261230857082196860544473)
              ·
                refine ⟨4695923142811647645408355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6261230857082196860544473 4695923142811647645408355)
                ·
                  refine ⟨7043884714217471468112533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4695923142811647645408355 7043884714217471468112533)
                  ·
                    refine ⟨330182095978943975067775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7043884714217471468112533 330182095978943975067775)
                    ·
                      rfl

theorem cell22_964541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_964541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964541 prefixEnd_964541 := by exact prefixLift 964541
  have htrace : WordTrace (prefixWord ++ tailWord_964541) baseStart_964541 baseEnd_964541 := by
    simpa [prefixWord, tailWord_964541, baseEnd_964541] using wordTrace_append hprefix tailTrace_964541
  have hstable : (prefixWord ++ tailWord_964541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964541).length < 2 ^ (prefixWord ++ tailWord_964541).sum := by decide
  have hdescent : baseEnd_964541 < baseStart_964541 := by decide
  rcases family_descends (prefixWord ++ tailWord_964541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964556 : List Nat := [2, 2, 1, 4, 1, 3, 1, 8]
def baseStart_964556 : Nat := 118140960795 + 964556 * 2 ^ 59
def prefixEnd_964556 : Nat := 4983230072969 + 3 ^ 40 * 964556 * 2
def baseEnd_964556 : Nat := 36687470087276548438081

theorem tailTrace_964556 : CollatzResearch.WordTrace tailWord_964556 prefixEnd_964556 36687470087276548438081 := by
  unfold tailWord_964556
  simp only [CollatzResearch.WordTrace]
  refine ⟨17590123746792909947420761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23453498329057213263227681 17590123746792909947420761)
  ·
    refine ⟨13192592810094682460565571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17590123746792909947420761 13192592810094682460565571)
    ·
      refine ⟨19788889215142023690848357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13192592810094682460565571 19788889215142023690848357)
      ·
        refine ⟨3710416727839129442034067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19788889215142023690848357 3710416727839129442034067)
        ·
          refine ⟨5565625091758694163051101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3710416727839129442034067 5565625091758694163051101)
          ·
            refine ⟨2087109409409510311144163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5565625091758694163051101 2087109409409510311144163)
            ·
              refine ⟨3130664114114265466716245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2087109409409510311144163 3130664114114265466716245)
              ·
                refine ⟨36687470087276548438081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3130664114114265466716245 36687470087276548438081)
                ·
                  rfl

theorem cell22_964556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 8].length) (baseStart_964556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964556 prefixEnd_964556 := by exact prefixLift 964556
  have htrace : WordTrace (prefixWord ++ tailWord_964556) baseStart_964556 baseEnd_964556 := by
    simpa [prefixWord, tailWord_964556, baseEnd_964556] using wordTrace_append hprefix tailTrace_964556
  have hstable : (prefixWord ++ tailWord_964556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964556).length < 2 ^ (prefixWord ++ tailWord_964556).sum := by decide
  have hdescent : baseEnd_964556 < baseStart_964556 := by decide
  rcases family_descends (prefixWord ++ tailWord_964556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964562 : List Nat := [3, 2, 2, 3, 2, 2, 1, 3, 4]
def baseStart_964562 : Nat := 118140960795 + 964562 * 2 ^ 59
def prefixEnd_964562 : Nat := 4983230072969 + 3 ^ 40 * 964562 * 2
def baseEnd_964562 : Nat := 110063094902702306764237

theorem tailTrace_964562 : CollatzResearch.WordTrace tailWord_964562 prefixEnd_964562 110063094902702306764237 := by
  unfold tailWord_964562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795116582891020729889985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23453644221042721946373293 8795116582891020729889985)
  ·
    refine ⟨6596337437168265547417489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8795116582891020729889985 6596337437168265547417489)
    ·
      refine ⟨4947253077876199160563117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6596337437168265547417489 4947253077876199160563117)
      ·
        refine ⟨1855219904203574685211169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4947253077876199160563117 1855219904203574685211169)
        ·
          refine ⟨1391414928152681013908377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1855219904203574685211169 1391414928152681013908377)
          ·
            refine ⟨1043561196114510760431283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1391414928152681013908377 1043561196114510760431283)
            ·
              refine ⟨1565341794171766140646925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1043561196114510760431283 1565341794171766140646925)
              ·
                refine ⟨587003172814412302742597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1565341794171766140646925 587003172814412302742597)
                ·
                  refine ⟨110063094902702306764237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587003172814412302742597 110063094902702306764237)
                  ·
                    rfl

theorem cell22_964562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_964562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964562 prefixEnd_964562 := by exact prefixLift 964562
  have htrace : WordTrace (prefixWord ++ tailWord_964562) baseStart_964562 baseEnd_964562 := by
    simpa [prefixWord, tailWord_964562, baseEnd_964562] using wordTrace_append hprefix tailTrace_964562
  have hstable : (prefixWord ++ tailWord_964562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964562).length < 2 ^ (prefixWord ++ tailWord_964562).sum := by decide
  have hdescent : baseEnd_964562 < baseStart_964562 := by decide
  rcases family_descends (prefixWord ++ tailWord_964562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964573 : List Nat := [1, 4, 3, 1, 3, 2, 8]
def baseStart_964573 : Nat := 118140960795 + 964573 * 2 ^ 59
def prefixEnd_964573 : Nat := 4983230072969 + 3 ^ 40 * 964573 * 2
def baseEnd_964573 : Nat := 12229372230848391046951

theorem tailTrace_964573 : CollatzResearch.WordTrace tailWord_964573 prefixEnd_964573 12229372230848391046951 := by
  unfold tailWord_964573
  simp only [CollatzResearch.WordTrace]
  refine ⟨35180867534524231798210373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23453911689682821198806915 35180867534524231798210373)
  ·
    refine ⟨6596412662723293462164445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35180867534524231798210373 6596412662723293462164445)
    ·
      refine ⟨2473654748521235048311667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6596412662723293462164445 2473654748521235048311667)
      ·
        refine ⟨3710482122781852572467501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2473654748521235048311667 3710482122781852572467501)
        ·
          refine ⟨1391430796043194714675313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3710482122781852572467501 1391430796043194714675313)
          ·
            refine ⟨1043573097032396036006485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1391430796043194714675313 1043573097032396036006485)
            ·
              refine ⟨12229372230848391046951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1043573097032396036006485 12229372230848391046951)
              ·
                rfl

theorem cell22_964573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 8].length) (baseStart_964573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964573 prefixEnd_964573 := by exact prefixLift 964573
  have htrace : WordTrace (prefixWord ++ tailWord_964573) baseStart_964573 baseEnd_964573 := by
    simpa [prefixWord, tailWord_964573, baseEnd_964573] using wordTrace_append hprefix tailTrace_964573
  have hstable : (prefixWord ++ tailWord_964573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964573).length < 2 ^ (prefixWord ++ tailWord_964573).sum := by decide
  have hdescent : baseEnd_964573 < baseStart_964573 := by decide
  rcases family_descends (prefixWord ++ tailWord_964573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964586 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_964586 : Nat := 118140960795 + 964586 * 2 ^ 59
def prefixEnd_964586 : Nat := 4983230072969 + 3 ^ 40 * 964586 * 2
def baseEnd_964586 : Nat := 330197500398578857692637

theorem tailTrace_964586 : CollatzResearch.WordTrace tailWord_964586 prefixEnd_964586 330197500398578857692637 := by
  unfold tailWord_964586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8795335420869283754608403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23454227788984756678955741 8795335420869283754608403)
  ·
    refine ⟨13193003131303925631912605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8795335420869283754608403 13193003131303925631912605)
    ·
      refine ⟨4947376174238972111967227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13193003131303925631912605 4947376174238972111967227)
      ·
        refine ⟨7421064261358458167950841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4947376174238972111967227 7421064261358458167950841)
        ·
          refine ⟨5565798196018843625963131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7421064261358458167950841 5565798196018843625963131)
          ·
            refine ⟨8348697294028265438944697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5565798196018843625963131 8348697294028265438944697)
            ·
              refine ⟨6261522970521199079208523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8348697294028265438944697 6261522970521199079208523)
              ·
                refine ⟨9392284455781798618812785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6261522970521199079208523 9392284455781798618812785)
                ·
                  refine ⟨7044213341836348964109589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9392284455781798618812785 7044213341836348964109589)
                  ·
                    refine ⟨330197500398578857692637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7044213341836348964109589 330197500398578857692637)
                    ·
                      rfl

theorem cell22_964586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_964586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964586 prefixEnd_964586 := by exact prefixLift 964586
  have htrace : WordTrace (prefixWord ++ tailWord_964586) baseStart_964586 baseEnd_964586 := by
    simpa [prefixWord, tailWord_964586, baseEnd_964586] using wordTrace_append hprefix tailTrace_964586
  have hstable : (prefixWord ++ tailWord_964586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964586).length < 2 ^ (prefixWord ++ tailWord_964586).sum := by decide
  have hdescent : baseEnd_964586 < baseStart_964586 := by decide
  rcases family_descends (prefixWord ++ tailWord_964586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964695 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 2, 3]
def baseStart_964695 : Nat := 118140960795 + 964695 * 2 ^ 59
def prefixEnd_964695 : Nat := 4983230072969 + 3 ^ 40 * 964695 * 2
def baseEnd_964695 : Nat := 330234813326138906717303

theorem tailTrace_964695 : CollatzResearch.WordTrace tailWord_964695 prefixEnd_964695 330234813326138906717303 := by
  unfold tailWord_964695
  simp only [CollatzResearch.WordTrace]
  refine ⟨35185317240082246634151539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23456878160054831089434359 35185317240082246634151539)
  ·
    refine ⟨52777975860123369951227309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35185317240082246634151539 52777975860123369951227309)
    ·
      refine ⟨19791740947546263731710241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52777975860123369951227309 19791740947546263731710241)
      ·
        refine ⟨14843805710659697798782681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19791740947546263731710241 14843805710659697798782681)
        ·
          refine ⟨11132854282994773349087011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14843805710659697798782681 11132854282994773349087011)
          ·
            refine ⟨16699281424492160023630517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11132854282994773349087011 16699281424492160023630517)
            ·
              refine ⟨1565557633546140002215361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16699281424492160023630517 1565557633546140002215361)
              ·
                refine ⟨1174168225159605001661521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1565557633546140002215361 1174168225159605001661521)
                ·
                  refine ⟨880626168869703751246141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1174168225159605001661521 880626168869703751246141)
                  ·
                    refine ⟨330234813326138906717303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 880626168869703751246141 330234813326138906717303)
                    ·
                      rfl

theorem cell22_964695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_964695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964695 prefixEnd_964695 := by exact prefixLift 964695
  have htrace : WordTrace (prefixWord ++ tailWord_964695) baseStart_964695 baseEnd_964695 := by
    simpa [prefixWord, tailWord_964695, baseEnd_964695] using wordTrace_append hprefix tailTrace_964695
  have hstable : (prefixWord ++ tailWord_964695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964695).length < 2 ^ (prefixWord ++ tailWord_964695).sum := by decide
  have hdescent : baseEnd_964695 < baseStart_964695 := by decide
  rcases family_descends (prefixWord ++ tailWord_964695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964815 : List Nat := [1, 1, 2, 1, 1, 3, 5, 4, 4]
def baseStart_964815 : Nat := 118140960795 + 964815 * 2 ^ 59
def prefixEnd_964815 : Nat := 4983230072969 + 3 ^ 40 * 964815 * 2
def baseEnd_964815 : Nat := 110091963926166197905645

theorem tailTrace_964815 : CollatzResearch.WordTrace tailWord_964815 prefixEnd_964815 110091963926166197905645 := by
  unfold tailWord_964815
  simp only [CollatzResearch.WordTrace]
  refine ⟨35189693999647507128519899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23459795999765004752346599 35189693999647507128519899)
  ·
    refine ⟨52784540999471260692779849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35189693999647507128519899 52784540999471260692779849)
    ·
      refine ⟨39588405749603445519584887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52784540999471260692779849 39588405749603445519584887)
      ·
        refine ⟨59382608624405168279377331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39588405749603445519584887 59382608624405168279377331)
        ·
          refine ⟨89073912936607752419065997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59382608624405168279377331 89073912936607752419065997)
          ·
            refine ⟨33402717351227907157149749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89073912936607752419065997 33402717351227907157149749)
            ·
              refine ⟨3131504751677616295982789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33402717351227907157149749 3131504751677616295982789)
              ·
                refine ⟨587157140939553055496773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3131504751677616295982789 587157140939553055496773)
                ·
                  refine ⟨110091963926166197905645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 587157140939553055496773 110091963926166197905645)
                  ·
                    rfl

theorem cell22_964815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 4, 4].length) (baseStart_964815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964815 prefixEnd_964815 := by exact prefixLift 964815
  have htrace : WordTrace (prefixWord ++ tailWord_964815) baseStart_964815 baseEnd_964815 := by
    simpa [prefixWord, tailWord_964815, baseEnd_964815] using wordTrace_append hprefix tailTrace_964815
  have hstable : (prefixWord ++ tailWord_964815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964815).length < 2 ^ (prefixWord ++ tailWord_964815).sum := by decide
  have hdescent : baseEnd_964815 < baseStart_964815 := by decide
  rcases family_descends (prefixWord ++ tailWord_964815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964894 : List Nat := [4, 3, 2, 1, 1, 1, 4, 6]
def baseStart_964894 : Nat := 118140960795 + 964894 * 2 ^ 59
def prefixEnd_964894 : Nat := 4983230072969 + 3 ^ 40 * 964894 * 2
def baseEnd_964894 : Nat := 36700326121440968999077

theorem tailTrace_964894 : CollatzResearch.WordTrace tailWord_964894 prefixEnd_964894 36700326121440968999077 := by
  unfold tailWord_964894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4399071920795162952580717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23461716910907535747097157 4399071920795162952580717)
  ·
    refine ⟨1649651970298186107217769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4399071920795162952580717 1649651970298186107217769)
    ·
      refine ⟨1237238977723639580413327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1649651970298186107217769 1237238977723639580413327)
      ·
        refine ⟨1855858466585459370619991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1237238977723639580413327 1855858466585459370619991)
        ·
          refine ⟨2783787699878189055929987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1855858466585459370619991 2783787699878189055929987)
          ·
            refine ⟨4175681549817283583894981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2783787699878189055929987 4175681549817283583894981)
            ·
              refine ⟨782940290590740671980309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4175681549817283583894981 782940290590740671980309)
              ·
                refine ⟨36700326121440968999077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 782940290590740671980309 36700326121440968999077)
                ·
                  rfl

theorem cell22_964894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_964894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964894 prefixEnd_964894 := by exact prefixLift 964894
  have htrace : WordTrace (prefixWord ++ tailWord_964894) baseStart_964894 baseEnd_964894 := by
    simpa [prefixWord, tailWord_964894, baseEnd_964894] using wordTrace_append hprefix tailTrace_964894
  have hstable : (prefixWord ++ tailWord_964894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964894).length < 2 ^ (prefixWord ++ tailWord_964894).sum := by decide
  have hdescent : baseEnd_964894 < baseStart_964894 := by decide
  rcases family_descends (prefixWord ++ tailWord_964894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964935 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 3, 4]
def baseStart_964935 : Nat := 118140960795 + 964935 * 2 ^ 59
def prefixEnd_964935 : Nat := 4983230072969 + 3 ^ 40 * 964935 * 2
def baseEnd_964935 : Nat := 330316970230858280716567

theorem tailTrace_964935 : CollatzResearch.WordTrace tailWord_964935 prefixEnd_964935 330316970230858280716567 := by
  unfold tailWord_964935
  simp only [CollatzResearch.WordTrace]
  refine ⟨35194070759212767622888259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23462713839475178415258839 35194070759212767622888259)
  ·
    refine ⟨52791106138819151434332389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35194070759212767622888259 52791106138819151434332389)
    ·
      refine ⟨9898332401028590893937323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52791106138819151434332389 9898332401028590893937323)
      ·
        refine ⟨14847498601542886340905985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9898332401028590893937323 14847498601542886340905985)
        ·
          refine ⟨11135623951157164755679489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14847498601542886340905985 11135623951157164755679489)
          ·
            refine ⟨8351717963367873566759617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11135623951157164755679489 8351717963367873566759617)
            ·
              refine ⟨6263788472525905175069713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8351717963367873566759617 6263788472525905175069713)
              ·
                refine ⟨4697841354394428881302285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6263788472525905175069713 4697841354394428881302285)
                ·
                  refine ⟨1761690507897910830488357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4697841354394428881302285 1761690507897910830488357)
                  ·
                    refine ⟨330316970230858280716567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1761690507897910830488357 330316970230858280716567)
                    ·
                      rfl

theorem cell22_964935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_964935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964935 prefixEnd_964935 := by exact prefixLift 964935
  have htrace : WordTrace (prefixWord ++ tailWord_964935) baseStart_964935 baseEnd_964935 := by
    simpa [prefixWord, tailWord_964935, baseEnd_964935] using wordTrace_append hprefix tailTrace_964935
  have hstable : (prefixWord ++ tailWord_964935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964935).length < 2 ^ (prefixWord ++ tailWord_964935).sum := by decide
  have hdescent : baseEnd_964935 < baseStart_964935 := by decide
  rcases family_descends (prefixWord ++ tailWord_964935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_964965 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_964965 : Nat := 118140960795 + 964965 * 2 ^ 59
def prefixEnd_964965 : Nat := 4983230072969 + 3 ^ 40 * 964965 * 2
def baseEnd_964965 : Nat := 330327239843948202466475

theorem tailTrace_964965 : CollatzResearch.WordTrace tailWord_964965 prefixEnd_964965 330327239843948202466475 := by
  unfold tailWord_964965
  simp only [CollatzResearch.WordTrace]
  refine ⟨35195164949104082746480349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23463443299402721830986899 35195164949104082746480349)
  ·
    refine ⟨13198186855914031029930131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35195164949104082746480349 13198186855914031029930131)
    ·
      refine ⟨19797280283871046544895197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13198186855914031029930131 19797280283871046544895197)
      ·
        refine ⟨7423980106451642454335699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19797280283871046544895197 7423980106451642454335699)
        ·
          refine ⟨11135970159677463681503549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7423980106451642454335699 11135970159677463681503549)
          ·
            refine ⟨4175988809879048880563831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11135970159677463681503549 4175988809879048880563831)
            ·
              refine ⟨6263983214818573320845747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4175988809879048880563831 6263983214818573320845747)
              ·
                refine ⟨9395974822227859981268621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6263983214818573320845747 9395974822227859981268621)
                ·
                  refine ⟨3523490558335447492975733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9395974822227859981268621 3523490558335447492975733)
                  ·
                    refine ⟨330327239843948202466475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3523490558335447492975733 330327239843948202466475)
                    ·
                      rfl

theorem cell22_964965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_964965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_964965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_964965 prefixEnd_964965 := by exact prefixLift 964965
  have htrace : WordTrace (prefixWord ++ tailWord_964965) baseStart_964965 baseEnd_964965 := by
    simpa [prefixWord, tailWord_964965, baseEnd_964965] using wordTrace_append hprefix tailTrace_964965
  have hstable : (prefixWord ++ tailWord_964965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_964965).length < 2 ^ (prefixWord ++ tailWord_964965).sum := by decide
  have hdescent : baseEnd_964965 < baseStart_964965 := by decide
  rcases family_descends (prefixWord ++ tailWord_964965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965117 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_965117 : Nat := 118140960795 + 965117 * 2 ^ 59
def prefixEnd_965117 : Nat := 4983230072969 + 3 ^ 40 * 965117 * 2
def baseEnd_965117 : Nat := 330379272550270472666009

theorem tailTrace_965117 : CollatzResearch.WordTrace tailWord_965117 prefixEnd_965117 330379272550270472666009 := by
  unfold tailWord_965117
  simp only [CollatzResearch.WordTrace]
  refine ⟨35200708844553412706013605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23467139229702275137342403 35200708844553412706013605)
  ·
    refine ⟨6600132908353764882377551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35200708844553412706013605 6600132908353764882377551)
    ·
      refine ⟨9900199362530647323566327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6600132908353764882377551 9900199362530647323566327)
      ·
        refine ⟨14850299043795970985349491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9900199362530647323566327 14850299043795970985349491)
        ·
          refine ⟨22275448565693956478024237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14850299043795970985349491 22275448565693956478024237)
          ·
            refine ⟨8353293212135233679259089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22275448565693956478024237 8353293212135233679259089)
            ·
              refine ⟨6264969909101425259444317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8353293212135233679259089 6264969909101425259444317)
              ·
                refine ⟨2349363715913034472291619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6264969909101425259444317 2349363715913034472291619)
                ·
                  refine ⟨3524045573869551708437429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349363715913034472291619 3524045573869551708437429)
                  ·
                    refine ⟨330379272550270472666009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3524045573869551708437429 330379272550270472666009)
                    ·
                      rfl

theorem cell22_965117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_965117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965117 prefixEnd_965117 := by exact prefixLift 965117
  have htrace : WordTrace (prefixWord ++ tailWord_965117) baseStart_965117 baseEnd_965117 := by
    simpa [prefixWord, tailWord_965117, baseEnd_965117] using wordTrace_append hprefix tailTrace_965117
  have hstable : (prefixWord ++ tailWord_965117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965117).length < 2 ^ (prefixWord ++ tailWord_965117).sum := by decide
  have hdescent : baseEnd_965117 < baseStart_965117 := by decide
  rcases family_descends (prefixWord ++ tailWord_965117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965121 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 1, 4]
def baseStart_965121 : Nat := 118140960795 + 965121 * 2 ^ 59
def prefixEnd_965121 : Nat := 4983230072969 + 3 ^ 40 * 965121 * 2
def baseEnd_965121 : Nat := 330380641832015795565997

theorem tailTrace_965121 : CollatzResearch.WordTrace tailWord_965121 prefixEnd_965121 330380641832015795565997 := by
  unfold tailWord_965121
  simp only [CollatzResearch.WordTrace]
  refine ⟨35200854736538921389159217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23467236491025947592772811 35200854736538921389159217)
  ·
    refine ⟨26400641052404191041869413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35200854736538921389159217 26400641052404191041869413)
    ·
      refine ⟨4950120197325785820350515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26400641052404191041869413 4950120197325785820350515)
      ·
        refine ⟨7425180295988678730525773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4950120197325785820350515 7425180295988678730525773)
        ·
          refine ⟨2784442610995754523947165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7425180295988678730525773 2784442610995754523947165)
          ·
            refine ⟨1044165979123407946480187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2784442610995754523947165 1044165979123407946480187)
            ·
              refine ⟨1566248968685111919720281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044165979123407946480187 1566248968685111919720281)
              ·
                refine ⟨1174686726513833939790211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1566248968685111919720281 1174686726513833939790211)
                ·
                  refine ⟨1762030089770750909685317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174686726513833939790211 1762030089770750909685317)
                  ·
                    refine ⟨330380641832015795565997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762030089770750909685317 330380641832015795565997)
                    ·
                      rfl

theorem cell22_965121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_965121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965121 prefixEnd_965121 := by exact prefixLift 965121
  have htrace : WordTrace (prefixWord ++ tailWord_965121) baseStart_965121 baseEnd_965121 := by
    simpa [prefixWord, tailWord_965121, baseEnd_965121] using wordTrace_append hprefix tailTrace_965121
  have hstable : (prefixWord ++ tailWord_965121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965121).length < 2 ^ (prefixWord ++ tailWord_965121).sum := by decide
  have hdescent : baseEnd_965121 < baseStart_965121 := by decide
  rcases family_descends (prefixWord ++ tailWord_965121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965134 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_965134 : Nat := 118140960795 + 965134 * 2 ^ 59
def prefixEnd_965134 : Nat := 4983230072969 + 3 ^ 40 * 965134 * 2
def baseEnd_965134 : Nat := 330385091997688094990957

theorem tailTrace_965134 : CollatzResearch.WordTrace tailWord_965134 prefixEnd_965134 330385091997688094990957 := by
  unfold tailWord_965134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4400166110686478076172807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23467552590327883072921637 4400166110686478076172807)
  ·
    refine ⟨6600249166029717114259211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4400166110686478076172807 6600249166029717114259211)
    ·
      refine ⟨9900373749044575671388817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6600249166029717114259211 9900373749044575671388817)
      ·
        refine ⟨7425280311783431753541613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9900373749044575671388817 7425280311783431753541613)
        ·
          refine ⟨2784480116918786907578105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7425280311783431753541613 2784480116918786907578105)
          ·
            refine ⟨2088360087689090180683579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2784480116918786907578105 2088360087689090180683579)
            ·
              refine ⟨3132540131533635271025369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2088360087689090180683579 3132540131533635271025369)
              ·
                refine ⟨2349405098650226453269027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132540131533635271025369 2349405098650226453269027)
                ·
                  refine ⟨3524107647975339679903541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2349405098650226453269027 3524107647975339679903541)
                  ·
                    refine ⟨330385091997688094990957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3524107647975339679903541 330385091997688094990957)
                    ·
                      rfl

theorem cell22_965134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_965134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965134 prefixEnd_965134 := by exact prefixLift 965134
  have htrace : WordTrace (prefixWord ++ tailWord_965134) baseStart_965134 baseEnd_965134 := by
    simpa [prefixWord, tailWord_965134, baseEnd_965134] using wordTrace_append hprefix tailTrace_965134
  have hstable : (prefixWord ++ tailWord_965134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965134).length < 2 ^ (prefixWord ++ tailWord_965134).sum := by decide
  have hdescent : baseEnd_965134 < baseStart_965134 := by decide
  rcases family_descends (prefixWord ++ tailWord_965134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965149 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_965149 : Nat := 118140960795 + 965149 * 2 ^ 59
def prefixEnd_965149 : Nat := 4983230072969 + 3 ^ 40 * 965149 * 2
def baseEnd_965149 : Nat := 330390226804233055865911

theorem tailTrace_965149 : CollatzResearch.WordTrace tailWord_965149 prefixEnd_965149 330390226804233055865911 := by
  unfold tailWord_965149
  simp only [CollatzResearch.WordTrace]
  refine ⟨35201875980437482171178501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23467917320291654780785667 35201875980437482171178501)
  ·
    refine ⟨6600351746332027907095969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35201875980437482171178501 6600351746332027907095969)
    ·
      refine ⟨4950263809749020930321977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6600351746332027907095969 4950263809749020930321977)
      ·
        refine ⟨3712697857311765697741483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4950263809749020930321977 3712697857311765697741483)
        ·
          refine ⟨5569046785967648546612225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712697857311765697741483 5569046785967648546612225)
          ·
            refine ⟨4176785089475736409959169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5569046785967648546612225 4176785089475736409959169)
            ·
              refine ⟨3132588817106802307469377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4176785089475736409959169 3132588817106802307469377)
              ·
                refine ⟨2349441612830101730602033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3132588817106802307469377 2349441612830101730602033)
                ·
                  refine ⟨1762081209622576297951525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349441612830101730602033 1762081209622576297951525)
                  ·
                    refine ⟨330390226804233055865911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762081209622576297951525 330390226804233055865911)
                    ·
                      rfl

theorem cell22_965149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_965149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965149 prefixEnd_965149 := by exact prefixLift 965149
  have htrace : WordTrace (prefixWord ++ tailWord_965149) baseStart_965149 baseEnd_965149 := by
    simpa [prefixWord, tailWord_965149, baseEnd_965149] using wordTrace_append hprefix tailTrace_965149
  have hstable : (prefixWord ++ tailWord_965149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965149).length < 2 ^ (prefixWord ++ tailWord_965149).sum := by decide
  have hdescent : baseEnd_965149 < baseStart_965149 := by decide
  rcases family_descends (prefixWord ++ tailWord_965149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965177 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_965177 : Nat := 118140960795 + 965177 * 2 ^ 59
def prefixEnd_965177 : Nat := 4983230072969 + 3 ^ 40 * 965177 * 2
def baseEnd_965177 : Nat := 330399811776450316165825

theorem tailTrace_965177 : CollatzResearch.WordTrace tailWord_965177 prefixEnd_965177 330399811776450316165825 := by
  unfold tailWord_965177
  simp only [CollatzResearch.WordTrace]
  refine ⟨35202897224336042953197785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23468598149557361968798523 35202897224336042953197785)
  ·
    refine ⟨26402172918252032214898339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35202897224336042953197785 26402172918252032214898339)
    ·
      refine ⟨39603259377378048322347509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26402172918252032214898339 39603259377378048322347509)
      ·
        refine ⟨3712805566629192030220079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39603259377378048322347509 3712805566629192030220079)
        ·
          refine ⟨5569208349943788045330119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712805566629192030220079 5569208349943788045330119)
          ·
            refine ⟨8353812524915682067995179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569208349943788045330119 8353812524915682067995179)
            ·
              refine ⟨12530718787373523101992769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8353812524915682067995179 12530718787373523101992769)
              ·
                refine ⟨9398039090530142326494577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12530718787373523101992769 9398039090530142326494577)
                ·
                  refine ⟨7048529317897606744870933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9398039090530142326494577 7048529317897606744870933)
                  ·
                    refine ⟨330399811776450316165825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7048529317897606744870933 330399811776450316165825)
                    ·
                      rfl

theorem cell22_965177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_965177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965177 prefixEnd_965177 := by exact prefixLift 965177
  have htrace : WordTrace (prefixWord ++ tailWord_965177) baseStart_965177 baseEnd_965177 := by
    simpa [prefixWord, tailWord_965177, baseEnd_965177] using wordTrace_append hprefix tailTrace_965177
  have hstable : (prefixWord ++ tailWord_965177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965177).length < 2 ^ (prefixWord ++ tailWord_965177).sum := by decide
  have hdescent : baseEnd_965177 < baseStart_965177 := by decide
  rcases family_descends (prefixWord ++ tailWord_965177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965207 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 4, 5]
def baseStart_965207 : Nat := 118140960795 + 965207 * 2 ^ 59
def prefixEnd_965207 : Nat := 4983230072969 + 3 ^ 40 * 965207 * 2
def baseEnd_965207 : Nat := 330410081389540237915733

theorem tailTrace_965207 : CollatzResearch.WordTrace tailWord_965207 prefixEnd_965207 330410081389540237915733 := by
  unfold tailWord_965207
  simp only [CollatzResearch.WordTrace]
  refine ⟨35203991414227358076789875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23469327609484905384526583 35203991414227358076789875)
  ·
    refine ⟨52805987121341037115184813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35203991414227358076789875 52805987121341037115184813)
    ·
      refine ⟨19802245170502888918194305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52805987121341037115184813 19802245170502888918194305)
      ·
        refine ⟨14851683877877166688645729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19802245170502888918194305 14851683877877166688645729)
        ·
          refine ⟨11138762908407875016484297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14851683877877166688645729 11138762908407875016484297)
          ·
            refine ⟨8354072181305906262363223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11138762908407875016484297 8354072181305906262363223)
            ·
              refine ⟨12531108271958859393544835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354072181305906262363223 12531108271958859393544835)
              ·
                refine ⟨18796662407938289090317253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12531108271958859393544835 18796662407938289090317253)
                ·
                  refine ⟨3524374201488429204434485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18796662407938289090317253 3524374201488429204434485)
                  ·
                    refine ⟨330410081389540237915733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3524374201488429204434485 330410081389540237915733)
                    ·
                      rfl

theorem cell22_965207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_965207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965207 prefixEnd_965207 := by exact prefixLift 965207
  have htrace : WordTrace (prefixWord ++ tailWord_965207) baseStart_965207 baseEnd_965207 := by
    simpa [prefixWord, tailWord_965207, baseEnd_965207] using wordTrace_append hprefix tailTrace_965207
  have hstable : (prefixWord ++ tailWord_965207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965207).length < 2 ^ (prefixWord ++ tailWord_965207).sum := by decide
  have hdescent : baseEnd_965207 < baseStart_965207 := by decide
  rcases family_descends (prefixWord ++ tailWord_965207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965226 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 5]
def baseStart_965226 : Nat := 118140960795 + 965226 * 2 ^ 59
def prefixEnd_965226 : Nat := 4983230072969 + 3 ^ 40 * 965226 * 2
def baseEnd_965226 : Nat := 110138861825943507230225

theorem tailTrace_965226 : CollatzResearch.WordTrace tailWord_965226 prefixEnd_965226 110138861825943507230225 := by
  unfold tailWord_965226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8801171100289631080432883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23469789600772349547821021 8801171100289631080432883)
  ·
    refine ⟨13201756650434446620649325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8801171100289631080432883 13201756650434446620649325)
    ·
      refine ⟨4950658743912917482743497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13201756650434446620649325 4950658743912917482743497)
      ·
        refine ⟨3712994057934688112057623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4950658743912917482743497 3712994057934688112057623)
        ·
          refine ⟨5569491086902032168086435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3712994057934688112057623 5569491086902032168086435)
          ·
            refine ⟨8354236630353048252129653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569491086902032168086435 8354236630353048252129653)
            ·
              refine ⟨783209684095598273637155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8354236630353048252129653 783209684095598273637155)
              ·
                refine ⟨1174814526143397410455733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783209684095598273637155 1174814526143397410455733)
                ·
                  refine ⟨110138861825943507230225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1174814526143397410455733 110138861825943507230225)
                  ·
                    rfl

theorem cell22_965226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_965226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965226 prefixEnd_965226 := by exact prefixLift 965226
  have htrace : WordTrace (prefixWord ++ tailWord_965226) baseStart_965226 baseEnd_965226 := by
    simpa [prefixWord, tailWord_965226, baseEnd_965226] using wordTrace_append hprefix tailTrace_965226
  have hstable : (prefixWord ++ tailWord_965226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965226).length < 2 ^ (prefixWord ++ tailWord_965226).sum := by decide
  have hdescent : baseEnd_965226 < baseStart_965226 := by decide
  rcases family_descends (prefixWord ++ tailWord_965226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965239 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 1, 4]
def baseStart_965239 : Nat := 118140960795 + 965239 * 2 ^ 59
def prefixEnd_965239 : Nat := 4983230072969 + 3 ^ 40 * 965239 * 2
def baseEnd_965239 : Nat := 330421035643502821115635

theorem tailTrace_965239 : CollatzResearch.WordTrace tailWord_965239 prefixEnd_965239 330421035643502821115635 := by
  unfold tailWord_965239
  simp only [CollatzResearch.WordTrace]
  refine ⟨35205158550111427541954771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23470105700074285027969847 35205158550111427541954771)
  ·
    refine ⟨52807737825167141312932157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35205158550111427541954771 52807737825167141312932157)
    ·
      refine ⟨19802901684437677992349559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52807737825167141312932157 19802901684437677992349559)
      ·
        refine ⟨29704352526656516988524339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19802901684437677992349559 29704352526656516988524339)
        ·
          refine ⟨44556528789984775482786509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29704352526656516988524339 44556528789984775482786509)
          ·
            refine ⟨16708698296244290806044941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44556528789984775482786509 16708698296244290806044941)
            ·
              refine ⟨6265761861091609052266853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16708698296244290806044941 6265761861091609052266853)
              ·
                refine ⟨1174830348954676697300035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6265761861091609052266853 1174830348954676697300035)
                ·
                  refine ⟨1762245523432015045950053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1174830348954676697300035 1762245523432015045950053)
                  ·
                    refine ⟨330421035643502821115635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762245523432015045950053 330421035643502821115635)
                    ·
                      rfl

theorem cell22_965239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_965239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965239 prefixEnd_965239 := by exact prefixLift 965239
  have htrace : WordTrace (prefixWord ++ tailWord_965239) baseStart_965239 baseEnd_965239 := by
    simpa [prefixWord, tailWord_965239, baseEnd_965239] using wordTrace_append hprefix tailTrace_965239
  have hstable : (prefixWord ++ tailWord_965239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965239).length < 2 ^ (prefixWord ++ tailWord_965239).sum := by decide
  have hdescent : baseEnd_965239 < baseStart_965239 := by decide
  rcases family_descends (prefixWord ++ tailWord_965239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965284 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_965284 : Nat := 118140960795 + 965284 * 2 ^ 59
def prefixEnd_965284 : Nat := 4983230072969 + 3 ^ 40 * 965284 * 2
def baseEnd_965284 : Nat := 330436440063137703740497

theorem tailTrace_965284 : CollatzResearch.WordTrace tailWord_965284 prefixEnd_965284 330436440063137703740497 := by
  unfold tailWord_965284
  simp only [CollatzResearch.WordTrace]
  refine ⟨17603399917474200113671453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23471199889965600151561937 17603399917474200113671453)
  ·
    refine ⟨6601274969052825042626795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17603399917474200113671453 6601274969052825042626795)
    ·
      refine ⟨9901912453579237563940193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6601274969052825042626795 9901912453579237563940193)
      ·
        refine ⟨7426434340184428172955145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9901912453579237563940193 7426434340184428172955145)
        ·
          refine ⟨5569825755138321129716359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7426434340184428172955145 5569825755138321129716359)
          ·
            refine ⟨8354738632707481694574539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5569825755138321129716359 8354738632707481694574539)
            ·
              refine ⟨12532107949061222541861809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8354738632707481694574539 12532107949061222541861809)
              ·
                refine ⟨9399080961795916906396357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12532107949061222541861809 9399080961795916906396357)
                ·
                  refine ⟨1762327680336734419949317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9399080961795916906396357 1762327680336734419949317)
                  ·
                    refine ⟨330436440063137703740497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762327680336734419949317 330436440063137703740497)
                    ·
                      rfl

theorem cell22_965284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_965284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965284 prefixEnd_965284 := by exact prefixLift 965284
  have htrace : WordTrace (prefixWord ++ tailWord_965284) baseStart_965284 baseEnd_965284 := by
    simpa [prefixWord, tailWord_965284, baseEnd_965284] using wordTrace_append hprefix tailTrace_965284
  have hstable : (prefixWord ++ tailWord_965284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965284).length < 2 ^ (prefixWord ++ tailWord_965284).sum := by decide
  have hdescent : baseEnd_965284 < baseStart_965284 := by decide
  rcases family_descends (prefixWord ++ tailWord_965284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965301 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_965301 : Nat := 118140960795 + 965301 * 2 ^ 59
def prefixEnd_965301 : Nat := 4983230072969 + 3 ^ 40 * 965301 * 2
def baseEnd_965301 : Nat := 330442259510555326065445

theorem tailTrace_965301 : CollatzResearch.WordTrace tailWord_965301 prefixEnd_965301 330442259510555326065445 := by
  unfold tailWord_965301
  simp only [CollatzResearch.WordTrace]
  refine ⟨35207419875886812130711757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23471613250591208087141171 35207419875886812130711757)
  ·
    refine ⟨13202782453457554549016909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35207419875886812130711757 13202782453457554549016909)
    ·
      refine ⟨4951043420046582955881341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13202782453457554549016909 4951043420046582955881341)
      ·
        refine ⟨1856641282517468608455503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4951043420046582955881341 1856641282517468608455503)
        ·
          refine ⟨2784961923776202912683255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1856641282517468608455503 2784961923776202912683255)
          ·
            refine ⟨4177442885664304369024883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2784961923776202912683255 4177442885664304369024883)
            ·
              refine ⟨6266164328496456553537325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4177442885664304369024883 6266164328496456553537325)
              ·
                refine ⟨2349811623186171207576497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6266164328496456553537325 2349811623186171207576497)
                ·
                  refine ⟨1762358717389628405682373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2349811623186171207576497 1762358717389628405682373)
                  ·
                    refine ⟨330442259510555326065445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762358717389628405682373 330442259510555326065445)
                    ·
                      rfl

theorem cell22_965301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_965301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965301 prefixEnd_965301 := by exact prefixLift 965301
  have htrace : WordTrace (prefixWord ++ tailWord_965301) baseStart_965301 baseEnd_965301 := by
    simpa [prefixWord, tailWord_965301, baseEnd_965301] using wordTrace_append hprefix tailTrace_965301
  have hstable : (prefixWord ++ tailWord_965301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965301).length < 2 ^ (prefixWord ++ tailWord_965301).sum := by decide
  have hdescent : baseEnd_965301 < baseStart_965301 := by decide
  rcases family_descends (prefixWord ++ tailWord_965301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965333 : List Nat := [1, 3, 2, 5, 1, 2, 1, 7]
def baseStart_965333 : Nat := 118140960795 + 965333 * 2 ^ 59
def prefixEnd_965333 : Nat := 4983230072969 + 3 ^ 40 * 965333 * 2
def baseEnd_965333 : Nat := 36717023751613101029483

theorem tailTrace_965333 : CollatzResearch.WordTrace tailWord_965333 prefixEnd_965333 36717023751613101029483 := by
  unfold tailWord_965333
  simp only [CollatzResearch.WordTrace]
  refine ⟨35208587011770881595876653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23472391341180587730584435 35208587011770881595876653)
  ·
    refine ⟨13203220129414080598453745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35208587011770881595876653 13203220129414080598453745)
    ·
      refine ⟨9902415097060560448840309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13203220129414080598453745 9902415097060560448840309)
      ·
        refine ⟨928351415349427542078779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9902415097060560448840309 928351415349427542078779)
        ·
          refine ⟨1392527123024141313118169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928351415349427542078779 1392527123024141313118169)
          ·
            refine ⟨1044395342268105984838627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1392527123024141313118169 1044395342268105984838627)
            ·
              refine ⟨1566593013402158977257941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044395342268105984838627 1566593013402158977257941)
              ·
                refine ⟨36717023751613101029483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1566593013402158977257941 36717023751613101029483)
                ·
                  rfl

theorem cell22_965333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 7].length) (baseStart_965333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965333 prefixEnd_965333 := by exact prefixLift 965333
  have htrace : WordTrace (prefixWord ++ tailWord_965333) baseStart_965333 baseEnd_965333 := by
    simpa [prefixWord, tailWord_965333, baseEnd_965333] using wordTrace_append hprefix tailTrace_965333
  have hstable : (prefixWord ++ tailWord_965333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965333).length < 2 ^ (prefixWord ++ tailWord_965333).sum := by decide
  have hdescent : baseEnd_965333 < baseStart_965333 := by decide
  rcases family_descends (prefixWord ++ tailWord_965333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965378 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_965378 : Nat := 118140960795 + 965378 * 2 ^ 59
def prefixEnd_965378 : Nat := 4983230072969 + 3 ^ 40 * 965378 * 2
def baseEnd_965378 : Nat := 110156206061384263963403

theorem tailTrace_965378 : CollatzResearch.WordTrace tailWord_965378 prefixEnd_965378 110156206061384263963403 := by
  unfold tailWord_965378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8802557074151963570316197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23473485531071902854176525 8802557074151963570316197)
  ·
    refine ⟨1650479451403493169434287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8802557074151963570316197 1650479451403493169434287)
    ·
      refine ⟨2475719177105239754151431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1650479451403493169434287 2475719177105239754151431)
      ·
        refine ⟨3713578765657859631227147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2475719177105239754151431 3713578765657859631227147)
        ·
          refine ⟨5570368148486789446840721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713578765657859631227147 5570368148486789446840721)
          ·
            refine ⟨4177776111365092085130541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5570368148486789446840721 4177776111365092085130541)
            ·
              refine ⟨1566666041761909531923953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4177776111365092085130541 1566666041761909531923953)
              ·
                refine ⟨1174999531321432148942965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1566666041761909531923953 1174999531321432148942965)
                ·
                  refine ⟨110156206061384263963403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1174999531321432148942965 110156206061384263963403)
                  ·
                    rfl

theorem cell22_965378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_965378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965378 prefixEnd_965378 := by exact prefixLift 965378
  have htrace : WordTrace (prefixWord ++ tailWord_965378) baseStart_965378 baseEnd_965378 := by
    simpa [prefixWord, tailWord_965378, baseEnd_965378] using wordTrace_append hprefix tailTrace_965378
  have hstable : (prefixWord ++ tailWord_965378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965378).length < 2 ^ (prefixWord ++ tailWord_965378).sum := by decide
  have hdescent : baseEnd_965378 < baseStart_965378 := by decide
  rcases family_descends (prefixWord ++ tailWord_965378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965408 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 1, 4]
def baseStart_965408 : Nat := 118140960795 + 965408 * 2 ^ 59
def prefixEnd_965408 : Nat := 4983230072969 + 3 ^ 40 * 965408 * 2
def baseEnd_965408 : Nat := 330478887797242713640117

theorem tailTrace_965408 : CollatzResearch.WordTrace tailWord_965408 prefixEnd_965408 330478887797242713640117 := by
  unfold tailWord_965408
  simp only [CollatzResearch.WordTrace]
  refine ⟨17605661243249584702428439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23474214990999446269904585 17605661243249584702428439)
  ·
    refine ⟨26408491864874377053642659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17605661243249584702428439 26408491864874377053642659)
    ·
      refine ⟨39612737797311565580463989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26408491864874377053642659 39612737797311565580463989)
      ·
        refine ⟨3713694168497959273168499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39612737797311565580463989 3713694168497959273168499)
        ·
          refine ⟨5570541252746938909752749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3713694168497959273168499 5570541252746938909752749)
          ·
            refine ⟨2088952969780102091157281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5570541252746938909752749 2088952969780102091157281)
            ·
              refine ⟨1566714727335076568367961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2088952969780102091157281 1566714727335076568367961)
              ·
                refine ⟨1175036045501307426275971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1566714727335076568367961 1175036045501307426275971)
                ·
                  refine ⟨1762554068251961139413957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175036045501307426275971 1762554068251961139413957)
                  ·
                    refine ⟨330478887797242713640117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762554068251961139413957 330478887797242713640117)
                    ·
                      rfl

theorem cell22_965408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_965408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965408 prefixEnd_965408 := by exact prefixLift 965408
  have htrace : WordTrace (prefixWord ++ tailWord_965408) baseStart_965408 baseEnd_965408 := by
    simpa [prefixWord, tailWord_965408, baseEnd_965408] using wordTrace_append hprefix tailTrace_965408
  have hstable : (prefixWord ++ tailWord_965408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965408).length < 2 ^ (prefixWord ++ tailWord_965408).sum := by decide
  have hdescent : baseEnd_965408 < baseStart_965408 := by decide
  rcases family_descends (prefixWord ++ tailWord_965408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965502 : List Nat := [4, 2, 3, 1, 3, 1, 1, 7]
def baseStart_965502 : Nat := 118140960795 + 965502 * 2 ^ 59
def prefixEnd_965502 : Nat := 4983230072969 + 3 ^ 40 * 965502 * 2
def baseEnd_965502 : Nat := 36723451768695311309981

theorem tailTrace_965502 : CollatzResearch.WordTrace tailWord_965502 prefixEnd_965502 36723451768695311309981 := by
  unfold tailWord_965502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4401843868519827932347345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23476500632105748972519173 4401843868519827932347345)
  ·
    refine ⟨3301382901389870949260509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4401843868519827932347345 3301382901389870949260509)
    ·
      refine ⟨1238018588021201605972691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3301382901389870949260509 1238018588021201605972691)
      ·
        refine ⟨1857027882031802408959037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238018588021201605972691 1857027882031802408959037)
        ·
          refine ⟨696385455761925903359639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1857027882031802408959037 696385455761925903359639)
          ·
            refine ⟨1044578183642888855039459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696385455761925903359639 1044578183642888855039459)
            ·
              refine ⟨1566867275464333282559189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044578183642888855039459 1566867275464333282559189)
              ·
                refine ⟨36723451768695311309981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1566867275464333282559189 36723451768695311309981)
                ·
                  rfl

theorem cell22_965502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_965502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965502 prefixEnd_965502 := by exact prefixLift 965502
  have htrace : WordTrace (prefixWord ++ tailWord_965502) baseStart_965502 baseEnd_965502 := by
    simpa [prefixWord, tailWord_965502, baseEnd_965502] using wordTrace_append hprefix tailTrace_965502
  have hstable : (prefixWord ++ tailWord_965502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965502).length < 2 ^ (prefixWord ++ tailWord_965502).sum := by decide
  have hdescent : baseEnd_965502 < baseStart_965502 := by decide
  rcases family_descends (prefixWord ++ tailWord_965502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965511 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 1, 7]
def baseStart_965511 : Nat := 118140960795 + 965511 * 2 ^ 59
def prefixEnd_965511 : Nat := 4983230072969 + 3 ^ 40 * 965511 * 2
def baseEnd_965511 : Nat := 330514146802184778314801

theorem tailTrace_965511 : CollatzResearch.WordTrace tailWord_965511 prefixEnd_965511 330514146802184778314801 := by
  unfold tailWord_965511
  simp only [CollatzResearch.WordTrace]
  refine ⟨35215079205126017995856387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23476719470084011997237591 35215079205126017995856387)
  ·
    refine ⟨52822618807689026993784581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35215079205126017995856387 52822618807689026993784581)
    ·
      refine ⟨9904241026441692561334609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52822618807689026993784581 9904241026441692561334609)
      ·
        refine ⟨7428180769831269421000957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9904241026441692561334609 7428180769831269421000957)
        ·
          refine ⟨2785567788686726032875359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7428180769831269421000957 2785567788686726032875359)
          ·
            refine ⟨4178351683030089049313039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2785567788686726032875359 4178351683030089049313039)
            ·
              refine ⟨6267527524545133573969559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4178351683030089049313039 6267527524545133573969559)
              ·
                refine ⟨9401291286817700360954339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6267527524545133573969559 9401291286817700360954339)
                ·
                  refine ⟨14101936930226550541431509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9401291286817700360954339 14101936930226550541431509)
                  ·
                    refine ⟨330514146802184778314801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14101936930226550541431509 330514146802184778314801)
                    ·
                      rfl

theorem cell22_965511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_965511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965511 prefixEnd_965511 := by exact prefixLift 965511
  have htrace : WordTrace (prefixWord ++ tailWord_965511) baseStart_965511 baseEnd_965511 := by
    simpa [prefixWord, tailWord_965511, baseEnd_965511] using wordTrace_append hprefix tailTrace_965511
  have hstable : (prefixWord ++ tailWord_965511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965511).length < 2 ^ (prefixWord ++ tailWord_965511).sum := by decide
  have hdescent : baseEnd_965511 < baseStart_965511 := by decide
  rcases family_descends (prefixWord ++ tailWord_965511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965571 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 4, 4]
def baseStart_965571 : Nat := 118140960795 + 965571 * 2 ^ 59
def prefixEnd_965571 : Nat := 4983230072969 + 3 ^ 40 * 965571 * 2
def baseEnd_965571 : Nat := 330534686028364621814617

theorem tailTrace_965571 : CollatzResearch.WordTrace tailWord_965571 prefixEnd_965571 330534686028364621814617 := by
  unfold tailWord_965571
  simp only [CollatzResearch.WordTrace]
  refine ⟨35217267584908648243040567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23478178389939098828693711 35217267584908648243040567)
  ·
    refine ⟨52825901377362972364560851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35217267584908648243040567 52825901377362972364560851)
    ·
      refine ⟨79238852066044458546841277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52825901377362972364560851 79238852066044458546841277)
      ·
        refine ⟨29714569524766671955065479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79238852066044458546841277 29714569524766671955065479)
        ·
          refine ⟨44571854287150007932598219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29714569524766671955065479 44571854287150007932598219)
          ·
            refine ⟨66857781430725011898897329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44571854287150007932598219 66857781430725011898897329)
            ·
              refine ⟨50143336073043758924172997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66857781430725011898897329 50143336073043758924172997)
              ·
                refine ⟨9401875513695704798282437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50143336073043758924172997 9401875513695704798282437)
                ·
                  refine ⟨1762851658817944649677957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9401875513695704798282437 1762851658817944649677957)
                  ·
                    refine ⟨330534686028364621814617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1762851658817944649677957 330534686028364621814617)
                    ·
                      rfl

theorem cell22_965571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 4].length) (baseStart_965571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965571 prefixEnd_965571 := by exact prefixLift 965571
  have htrace : WordTrace (prefixWord ++ tailWord_965571) baseStart_965571 baseEnd_965571 := by
    simpa [prefixWord, tailWord_965571, baseEnd_965571] using wordTrace_append hprefix tailTrace_965571
  have hstable : (prefixWord ++ tailWord_965571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965571).length < 2 ^ (prefixWord ++ tailWord_965571).sum := by decide
  have hdescent : baseEnd_965571 < baseStart_965571 := by decide
  rcases family_descends (prefixWord ++ tailWord_965571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965588 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_965588 : Nat := 118140960795 + 965588 * 2 ^ 59
def prefixEnd_965588 : Nat := 4983230072969 + 3 ^ 40 * 965588 * 2
def baseEnd_965588 : Nat := 330540505475782244139565

theorem tailTrace_965588 : CollatzResearch.WordTrace tailWord_965588 prefixEnd_965588 330540505475782244139565 := by
  unfold tailWord_965588
  simp only [CollatzResearch.WordTrace]
  refine ⟨17608943812923530073204709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23478591750564706764272945 17608943812923530073204709)
  ·
    refine ⟨3301676964923161888725883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17608943812923530073204709 3301676964923161888725883)
    ·
      refine ⟨4952515447384742833088825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3301676964923161888725883 4952515447384742833088825)
      ·
        refine ⟨3714386585538557124816619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4952515447384742833088825 3714386585538557124816619)
        ·
          refine ⟨5571579878307835687224929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714386585538557124816619 5571579878307835687224929)
          ·
            refine ⟨4178684908730876765418697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5571579878307835687224929 4178684908730876765418697)
            ·
              refine ⟨3134013681548157574064023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4178684908730876765418697 3134013681548157574064023)
              ·
                refine ⟨4701020522322236361096035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134013681548157574064023 4701020522322236361096035)
                ·
                  refine ⟨7051530783483354541644053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4701020522322236361096035 7051530783483354541644053)
                  ·
                    refine ⟨330540505475782244139565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7051530783483354541644053 330540505475782244139565)
                    ·
                      rfl

theorem cell22_965588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_965588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965588 prefixEnd_965588 := by exact prefixLift 965588
  have htrace : WordTrace (prefixWord ++ tailWord_965588) baseStart_965588 baseEnd_965588 := by
    simpa [prefixWord, tailWord_965588, baseEnd_965588] using wordTrace_append hprefix tailTrace_965588
  have hstable : (prefixWord ++ tailWord_965588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965588).length < 2 ^ (prefixWord ++ tailWord_965588).sum := by decide
  have hdescent : baseEnd_965588 < baseStart_965588 := by decide
  rcases family_descends (prefixWord ++ tailWord_965588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965616 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_965616 : Nat := 118140960795 + 965616 * 2 ^ 59
def prefixEnd_965616 : Nat := 4983230072969 + 3 ^ 40 * 965616 * 2
def baseEnd_965616 : Nat := 330550090447999504439479

theorem tailTrace_965616 : CollatzResearch.WordTrace tailWord_965616 prefixEnd_965616 330550090447999504439479 := by
  unfold tailWord_965616
  simp only [CollatzResearch.WordTrace]
  refine ⟨17609454434872810464214351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23479272579830413952285801 17609454434872810464214351)
  ·
    refine ⟨26414181652309215696321527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17609454434872810464214351 26414181652309215696321527)
    ·
      refine ⟨39621272478463823544482291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26414181652309215696321527 39621272478463823544482291)
      ·
        refine ⟨59431908717695735316723437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39621272478463823544482291 59431908717695735316723437)
        ·
          refine ⟨22286965769135900743771289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59431908717695735316723437 22286965769135900743771289)
          ·
            refine ⟨16715224326851925557828467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22286965769135900743771289 16715224326851925557828467)
            ·
              refine ⟨25072836490277888336742701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16715224326851925557828467 25072836490277888336742701)
              ·
                refine ⟨9402313683854208126278513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25072836490277888336742701 9402313683854208126278513)
                ·
                  refine ⟨7051735262890656094708885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9402313683854208126278513 7051735262890656094708885)
                  ·
                    refine ⟨330550090447999504439479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7051735262890656094708885 330550090447999504439479)
                    ·
                      rfl

theorem cell22_965616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_965616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965616 prefixEnd_965616 := by exact prefixLift 965616
  have htrace : WordTrace (prefixWord ++ tailWord_965616) baseStart_965616 baseEnd_965616 := by
    simpa [prefixWord, tailWord_965616, baseEnd_965616] using wordTrace_append hprefix tailTrace_965616
  have hstable : (prefixWord ++ tailWord_965616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965616).length < 2 ^ (prefixWord ++ tailWord_965616).sum := by decide
  have hdescent : baseEnd_965616 < baseStart_965616 := by decide
  rcases family_descends (prefixWord ++ tailWord_965616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965665 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 5]
def baseStart_965665 : Nat := 118140960795 + 965665 * 2 ^ 59
def prefixEnd_965665 : Nat := 4983230072969 + 3 ^ 40 * 965665 * 2
def baseEnd_965665 : Nat := 110188954716459903321443

theorem tailTrace_965665 : CollatzResearch.WordTrace tailWord_965665 prefixEnd_965665 110188954716459903321443 := by
  unfold tailWord_965665
  simp only [CollatzResearch.WordTrace]
  refine ⟨35220696046568102296962449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23480464031045401531308299 35220696046568102296962449)
  ·
    refine ⟨26415522034926076722721837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35220696046568102296962449 26415522034926076722721837)
    ·
      refine ⟨9905820763097278771020689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26415522034926076722721837 9905820763097278771020689)
      ·
        refine ⟨7429365572322959078265517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9905820763097278771020689 7429365572322959078265517)
        ·
          refine ⟨2786012089621109654349569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7429365572322959078265517 2786012089621109654349569)
          ·
            refine ⟨2089509067215832240762177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2786012089621109654349569 2089509067215832240762177)
            ·
              refine ⟨1567131800411874180571633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2089509067215832240762177 1567131800411874180571633)
              ·
                refine ⟨1175348850308905635428725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567131800411874180571633 1175348850308905635428725)
                ·
                  refine ⟨110188954716459903321443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1175348850308905635428725 110188954716459903321443)
                  ·
                    rfl

theorem cell22_965665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_965665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965665 prefixEnd_965665 := by exact prefixLift 965665
  have htrace : WordTrace (prefixWord ++ tailWord_965665) baseStart_965665 baseEnd_965665 := by
    simpa [prefixWord, tailWord_965665, baseEnd_965665] using wordTrace_append hprefix tailTrace_965665
  have hstable : (prefixWord ++ tailWord_965665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965665).length < 2 ^ (prefixWord ++ tailWord_965665).sum := by decide
  have hdescent : baseEnd_965665 < baseStart_965665 := by decide
  rcases family_descends (prefixWord ++ tailWord_965665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965693 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 8]
def baseStart_965693 : Nat := 118140960795 + 965693 * 2 ^ 59
def prefixEnd_965693 : Nat := 4983230072969 + 3 ^ 40 * 965693 * 2
def baseEnd_965693 : Nat := 110192149707198990088081

theorem tailTrace_965693 : CollatzResearch.WordTrace tailWord_965693 prefixEnd_965693 110192149707198990088081 := by
  unfold tailWord_965693
  simp only [CollatzResearch.WordTrace]
  refine ⟨35221717290466663078981733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23481144860311108719321155 35221717290466663078981733)
  ·
    refine ⟨6604071991962499327309075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35221717290466663078981733 6604071991962499327309075)
    ·
      refine ⟨9906107987943748990963613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6604071991962499327309075 9906107987943748990963613)
      ·
        refine ⟨3714790495478905871611355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9906107987943748990963613 3714790495478905871611355)
        ·
          refine ⟨5572185743218358807417033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714790495478905871611355 5572185743218358807417033)
          ·
            refine ⟨4179139307413769105562775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5572185743218358807417033 4179139307413769105562775)
            ·
              refine ⟨6268708961120653658344163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4179139307413769105562775 6268708961120653658344163)
              ·
                refine ⟨9403063441680980487516245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6268708961120653658344163 9403063441680980487516245)
                ·
                  refine ⟨110192149707198990088081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9403063441680980487516245 110192149707198990088081)
                  ·
                    rfl

theorem cell22_965693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_965693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965693 prefixEnd_965693 := by exact prefixLift 965693
  have htrace : WordTrace (prefixWord ++ tailWord_965693) baseStart_965693 baseEnd_965693 := by
    simpa [prefixWord, tailWord_965693, baseEnd_965693] using wordTrace_append hprefix tailTrace_965693
  have hstable : (prefixWord ++ tailWord_965693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965693).length < 2 ^ (prefixWord ++ tailWord_965693).sum := by decide
  have hdescent : baseEnd_965693 < baseStart_965693 := by decide
  rcases family_descends (prefixWord ++ tailWord_965693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965742 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_965742 : Nat := 118140960795 + 965742 * 2 ^ 59
def prefixEnd_965742 : Nat := 4983230072969 + 3 ^ 40 * 965742 * 2
def baseEnd_965742 : Nat := 330593222822977175789093

theorem tailTrace_965742 : CollatzResearch.WordTrace tailWord_965742 prefixEnd_965742 330593222822977175789093 := by
  unfold tailWord_965742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4402938058411143055939435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23482336311526096298343653 4402938058411143055939435)
  ·
    refine ⟨6604407087616714583909153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4402938058411143055939435 6604407087616714583909153)
    ·
      refine ⟨4953305315712535937931865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6604407087616714583909153 4953305315712535937931865)
      ·
        refine ⟨3714978986784401953448899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4953305315712535937931865 3714978986784401953448899)
        ·
          refine ⟨5572468480176602930173349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3714978986784401953448899 5572468480176602930173349)
          ·
            refine ⟨1044837840033113049407503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5572468480176602930173349 1044837840033113049407503)
            ·
              refine ⟨1567256760049669574111255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1044837840033113049407503 1567256760049669574111255)
              ·
                refine ⟨2350885140074504361166883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567256760049669574111255 2350885140074504361166883)
                ·
                  refine ⟨3526327710111756541750325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2350885140074504361166883 3526327710111756541750325)
                  ·
                    refine ⟨330593222822977175789093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3526327710111756541750325 330593222822977175789093)
                    ·
                      rfl

theorem cell22_965742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_965742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965742 prefixEnd_965742 := by exact prefixLift 965742
  have htrace : WordTrace (prefixWord ++ tailWord_965742) baseStart_965742 baseEnd_965742 := by
    simpa [prefixWord, tailWord_965742, baseEnd_965742] using wordTrace_append hprefix tailTrace_965742
  have hstable : (prefixWord ++ tailWord_965742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965742).length < 2 ^ (prefixWord ++ tailWord_965742).sum := by decide
  have hdescent : baseEnd_965742 < baseStart_965742 := by decide
  rcases family_descends (prefixWord ++ tailWord_965742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965838 : List Nat := [4, 1, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_965838 : Nat := 118140960795 + 965838 * 2 ^ 59
def prefixEnd_965838 : Nat := 4983230072969 + 3 ^ 40 * 965838 * 2
def baseEnd_965838 : Nat := 330626085584864925388799

theorem tailTrace_965838 : CollatzResearch.WordTrace tailWord_965838 prefixEnd_965838 330626085584864925388799 := by
  unfold tailWord_965838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4403375734367669105376271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23484670583294235228673445 4403375734367669105376271)
  ·
    refine ⟨6605063601551503658064407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4403375734367669105376271 6605063601551503658064407)
    ·
      refine ⟨9907595402327255487096611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6605063601551503658064407 9907595402327255487096611)
      ·
        refine ⟨14861393103490883230644917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9907595402327255487096611 14861393103490883230644917)
        ·
          refine ⟨1393255603452270302872961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14861393103490883230644917 1393255603452270302872961)
          ·
            refine ⟨1044941702589202727154721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1393255603452270302872961 1044941702589202727154721)
            ·
              refine ⟨783706276941902045366041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1044941702589202727154721 783706276941902045366041)
              ·
                refine ⟨587779707706426534024531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 783706276941902045366041 587779707706426534024531)
                ·
                  refine ⟨881669561559639801036797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 587779707706426534024531 881669561559639801036797)
                  ·
                    refine ⟨330626085584864925388799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 881669561559639801036797 330626085584864925388799)
                    ·
                      rfl

theorem cell22_965838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_965838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965838 prefixEnd_965838 := by exact prefixLift 965838
  have htrace : WordTrace (prefixWord ++ tailWord_965838) baseStart_965838 baseEnd_965838 := by
    simpa [prefixWord, tailWord_965838, baseEnd_965838] using wordTrace_append hprefix tailTrace_965838
  have hstable : (prefixWord ++ tailWord_965838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965838).length < 2 ^ (prefixWord ++ tailWord_965838).sum := by decide
  have hdescent : baseEnd_965838 < baseStart_965838 := by decide
  rcases family_descends (prefixWord ++ tailWord_965838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965860 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_965860 : Nat := 118140960795 + 965860 * 2 ^ 59
def prefixEnd_965860 : Nat := 4983230072969 + 3 ^ 40 * 965860 * 2
def baseEnd_965860 : Nat := 330633616634464201338731

theorem tailTrace_965860 : CollatzResearch.WordTrace tailWord_965860 prefixEnd_965860 330633616634464201338731 := by
  unfold tailWord_965860
  simp only [CollatzResearch.WordTrace]
  refine ⟨17613904140430825300155517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23485205520574433733540689 17613904140430825300155517)
  ·
    refine ⟨6605214052661559487558319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17613904140430825300155517 6605214052661559487558319)
    ·
      refine ⟨9907821078992339231337479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6605214052661559487558319 9907821078992339231337479)
      ·
        refine ⟨14861731618488508847006219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9907821078992339231337479 14861731618488508847006219)
        ·
          refine ⟨22292597427732763270509329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14861731618488508847006219 22292597427732763270509329)
          ·
            refine ⟨16719448070799572452881997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22292597427732763270509329 16719448070799572452881997)
            ·
              refine ⟨6269793026549839669830749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16719448070799572452881997 6269793026549839669830749)
              ·
                refine ⟨2351172384956189876186531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6269793026549839669830749 2351172384956189876186531)
                ·
                  refine ⟨3526758577434284814279797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351172384956189876186531 3526758577434284814279797)
                  ·
                    refine ⟨330633616634464201338731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3526758577434284814279797 330633616634464201338731)
                    ·
                      rfl

theorem cell22_965860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_965860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965860 prefixEnd_965860 := by exact prefixLift 965860
  have htrace : WordTrace (prefixWord ++ tailWord_965860) baseStart_965860 baseEnd_965860 := by
    simpa [prefixWord, tailWord_965860, baseEnd_965860] using wordTrace_append hprefix tailTrace_965860
  have hstable : (prefixWord ++ tailWord_965860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965860).length < 2 ^ (prefixWord ++ tailWord_965860).sum := by decide
  have hdescent : baseEnd_965860 < baseStart_965860 := by decide
  rcases family_descends (prefixWord ++ tailWord_965860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965875 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 1, 6]
def baseStart_965875 : Nat := 118140960795 + 965875 * 2 ^ 59
def prefixEnd_965875 : Nat := 4983230072969 + 3 ^ 40 * 965875 * 2
def baseEnd_965875 : Nat := 330638751441009162213685

theorem tailTrace_965875 : CollatzResearch.WordTrace tailWord_965875 prefixEnd_965875 330638751441009162213685 := by
  unfold tailWord_965875
  simp only [CollatzResearch.WordTrace]
  refine ⟨35228355375807308162107079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23485570250538205441404719 35228355375807308162107079)
  ·
    refine ⟨52842533063710962243160619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35228355375807308162107079 52842533063710962243160619)
    ·
      refine ⟨79263799595566443364740929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52842533063710962243160619 79263799595566443364740929)
      ·
        refine ⟨59447849696674832523555697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79263799595566443364740929 59447849696674832523555697)
        ·
          refine ⟨44585887272506124392666773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59447849696674832523555697 44585887272506124392666773)
          ·
            refine ⟨2089963465898724580906255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44585887272506124392666773 2089963465898724580906255)
            ·
              refine ⟨3134945198848086871359383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2089963465898724580906255 3134945198848086871359383)
              ·
                refine ⟨4702417798272130307039075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3134945198848086871359383 4702417798272130307039075)
                ·
                  refine ⟨7053626697408195460558613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4702417798272130307039075 7053626697408195460558613)
                  ·
                    refine ⟨330638751441009162213685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7053626697408195460558613 330638751441009162213685)
                    ·
                      rfl

theorem cell22_965875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 6].length) (baseStart_965875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965875 prefixEnd_965875 := by exact prefixLift 965875
  have htrace : WordTrace (prefixWord ++ tailWord_965875) baseStart_965875 baseEnd_965875 := by
    simpa [prefixWord, tailWord_965875, baseEnd_965875] using wordTrace_append hprefix tailTrace_965875
  have hstable : (prefixWord ++ tailWord_965875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965875).length < 2 ^ (prefixWord ++ tailWord_965875).sum := by decide
  have hdescent : baseEnd_965875 < baseStart_965875 := by decide
  rcases family_descends (prefixWord ++ tailWord_965875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965956 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_965956 : Nat := 118140960795 + 965956 * 2 ^ 59
def prefixEnd_965956 : Nat := 4983230072969 + 3 ^ 40 * 965956 * 2
def baseEnd_965956 : Nat := 330666479396351950938437

theorem tailTrace_965956 : CollatzResearch.WordTrace tailWord_965956 prefixEnd_965956 330666479396351950938437 := by
  unfold tailWord_965956
  simp only [CollatzResearch.WordTrace]
  refine ⟨17615654844256929497902861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23487539792342572663870481 17615654844256929497902861)
  ·
    refine ⟨6605870566596348561713573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17615654844256929497902861 6605870566596348561713573)
    ·
      refine ⟨1238600731236815355321295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6605870566596348561713573 1238600731236815355321295)
      ·
        refine ⟨1857901096855223032981943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1238600731236815355321295 1857901096855223032981943)
        ·
          refine ⟨2786851645282834549472915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1857901096855223032981943 2786851645282834549472915)
          ·
            refine ⟨4180277467924251824209373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2786851645282834549472915 4180277467924251824209373)
            ·
              refine ⟨1567604050471594434078515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4180277467924251824209373 1567604050471594434078515)
              ·
                refine ⟨2351406075707391651117773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567604050471594434078515 2351406075707391651117773)
                ·
                  refine ⟨881777278390271869169165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2351406075707391651117773 881777278390271869169165)
                  ·
                    refine ⟨330666479396351950938437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 881777278390271869169165 330666479396351950938437)
                    ·
                      rfl

theorem cell22_965956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_965956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965956 prefixEnd_965956 := by exact prefixLift 965956
  have htrace : WordTrace (prefixWord ++ tailWord_965956) baseStart_965956 baseEnd_965956 := by
    simpa [prefixWord, tailWord_965956, baseEnd_965956] using wordTrace_append hprefix tailTrace_965956
  have hstable : (prefixWord ++ tailWord_965956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965956).length < 2 ^ (prefixWord ++ tailWord_965956).sum := by decide
  have hdescent : baseEnd_965956 < baseStart_965956 := by decide
  rcases family_descends (prefixWord ++ tailWord_965956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_965999 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 1, 4]
def baseStart_965999 : Nat := 118140960795 + 965999 * 2 ^ 59
def prefixEnd_965999 : Nat := 4983230072969 + 3 ^ 40 * 965999 * 2
def baseEnd_965999 : Nat := 330681199175114172113305

theorem tailTrace_965999 : CollatzResearch.WordTrace tailWord_965999 prefixEnd_965999 330681199175114172113305 := by
  unfold tailWord_965999
  simp only [CollatzResearch.WordTrace]
  refine ⟨35232878027358077339621051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23488585351572051559747367 35232878027358077339621051)
  ·
    refine ⟨52849317041037116009431577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35232878027358077339621051 52849317041037116009431577)
    ·
      refine ⟨39636987780777837007073683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52849317041037116009431577 39636987780777837007073683)
      ·
        refine ⟨59455481671166755510610525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39636987780777837007073683 59455481671166755510610525)
        ·
          refine ⟨22295805626687533316478947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59455481671166755510610525 22295805626687533316478947)
          ·
            refine ⟨33443708440031299974718421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22295805626687533316478947 33443708440031299974718421)
            ·
              refine ⟨783836916563233593157463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 33443708440031299974718421 783836916563233593157463)
              ·
                refine ⟨1175755374844850389736195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783836916563233593157463 1175755374844850389736195)
                ·
                  refine ⟨1763633062267275584604293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175755374844850389736195 1763633062267275584604293)
                  ·
                    refine ⟨330681199175114172113305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1763633062267275584604293 330681199175114172113305)
                    ·
                      rfl

theorem cell22_965999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 1, 4].length) (baseStart_965999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_965999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_965999 prefixEnd_965999 := by exact prefixLift 965999
  have htrace : WordTrace (prefixWord ++ tailWord_965999) baseStart_965999 baseEnd_965999 := by
    simpa [prefixWord, tailWord_965999, baseEnd_965999] using wordTrace_append hprefix tailTrace_965999
  have hstable : (prefixWord ++ tailWord_965999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_965999).length < 2 ^ (prefixWord ++ tailWord_965999).sum := by decide
  have hdescent : baseEnd_965999 < baseStart_965999 := by decide
  rcases family_descends (prefixWord ++ tailWord_965999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966125 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_966125 : Nat := 118140960795 + 966125 * 2 ^ 59
def prefixEnd_966125 : Nat := 4983230072969 + 3 ^ 40 * 966125 * 2
def baseEnd_966125 : Nat := 330724331550091843462919

theorem tailTrace_966125 : CollatzResearch.WordTrace tailWord_966125 prefixEnd_966125 330724331550091843462919 := by
  unfold tailWord_966125
  simp only [CollatzResearch.WordTrace]
  refine ⟨35237473624901600858707829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23491649083267733905805219 35237473624901600858707829)
  ·
    refine ⟨3303513152334525080503859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35237473624901600858707829 3303513152334525080503859)
    ·
      refine ⟨4955269728501787620755789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3303513152334525080503859 4955269728501787620755789)
      ·
        refine ⟨1858226148188170357783421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4955269728501787620755789 1858226148188170357783421)
        ·
          refine ⟨696834805570563884168783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1858226148188170357783421 696834805570563884168783)
          ·
            refine ⟨1045252208355845826253175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 696834805570563884168783 1045252208355845826253175)
            ·
              refine ⟨1567878312533768739379763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045252208355845826253175 1567878312533768739379763)
              ·
                refine ⟨2351817468800653109069645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567878312533768739379763 2351817468800653109069645)
                ·
                  refine ⟨881931550800244915901117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2351817468800653109069645 881931550800244915901117)
                  ·
                    refine ⟨330724331550091843462919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 881931550800244915901117 330724331550091843462919)
                    ·
                      rfl

theorem cell22_966125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_966125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966125 prefixEnd_966125 := by exact prefixLift 966125
  have htrace : WordTrace (prefixWord ++ tailWord_966125) baseStart_966125 baseEnd_966125 := by
    simpa [prefixWord, tailWord_966125, baseEnd_966125] using wordTrace_append hprefix tailTrace_966125
  have hstable : (prefixWord ++ tailWord_966125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966125).length < 2 ^ (prefixWord ++ tailWord_966125).sum := by decide
  have hdescent : baseEnd_966125 < baseStart_966125 := by decide
  rcases family_descends (prefixWord ++ tailWord_966125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966151 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 1, 4]
def baseStart_966151 : Nat := 118140960795 + 966151 * 2 ^ 59
def prefixEnd_966151 : Nat := 4983230072969 + 3 ^ 40 * 966151 * 2
def baseEnd_966151 : Nat := 330733231881436442312839

theorem tailTrace_966151 : CollatzResearch.WordTrace tailWord_966151 prefixEnd_966151 330733231881436442312839 := by
  unfold tailWord_966151
  simp only [CollatzResearch.WordTrace]
  refine ⟨35238421922807407299154307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23492281281871604866102871 35238421922807407299154307)
  ·
    refine ⟨52857632884211110948731461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35238421922807407299154307 52857632884211110948731461)
    ·
      refine ⟨9910806165789583302887149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52857632884211110948731461 9910806165789583302887149)
      ·
        refine ⟨3716552312171093738582681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9910806165789583302887149 3716552312171093738582681)
        ·
          refine ⟨2787414234128320303937011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3716552312171093738582681 2787414234128320303937011)
          ·
            refine ⟨4181121351192480455905517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2787414234128320303937011 4181121351192480455905517)
            ·
              refine ⟨1567920506697180170964569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4181121351192480455905517 1567920506697180170964569)
              ·
                refine ⟨1175940380022885128223427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1567920506697180170964569 1175940380022885128223427)
                ·
                  refine ⟨1763910570034327692335141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175940380022885128223427 1763910570034327692335141)
                  ·
                    refine ⟨330733231881436442312839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1763910570034327692335141 330733231881436442312839)
                    ·
                      rfl

theorem cell22_966151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_966151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966151 prefixEnd_966151 := by exact prefixLift 966151
  have htrace : WordTrace (prefixWord ++ tailWord_966151) baseStart_966151 baseEnd_966151 := by
    simpa [prefixWord, tailWord_966151, baseEnd_966151] using wordTrace_append hprefix tailTrace_966151
  have hstable : (prefixWord ++ tailWord_966151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966151).length < 2 ^ (prefixWord ++ tailWord_966151).sum := by decide
  have hdescent : baseEnd_966151 < baseStart_966151 := by decide
  rcases family_descends (prefixWord ++ tailWord_966151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966168 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 1, 4]
def baseStart_966168 : Nat := 118140960795 + 966168 * 2 ^ 59
def prefixEnd_966168 : Nat := 4983230072969 + 3 ^ 40 * 966168 * 2
def baseEnd_966168 : Nat := 330739051328854064637787

theorem tailTrace_966168 : CollatzResearch.WordTrace tailWord_966168 prefixEnd_966168 330739051328854064637787 := by
  unfold tailWord_966168
  simp only [CollatzResearch.WordTrace]
  refine ⟨17619520981872909601261579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23492694642497212801682105 17619520981872909601261579)
  ·
    refine ⟨26429281472809364401892369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17619520981872909601261579 26429281472809364401892369)
    ·
      refine ⟨19821961104607023301419277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26429281472809364401892369 19821961104607023301419277)
      ·
        refine ⟨7433235414227633738032229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19821961104607023301419277 7433235414227633738032229)
        ·
          refine ⟨1393731640167681325881043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7433235414227633738032229 1393731640167681325881043)
          ·
            refine ⟨2090597460251521988821565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393731640167681325881043 2090597460251521988821565)
            ·
              refine ⟨783974047594320745808087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2090597460251521988821565 783974047594320745808087)
              ·
                refine ⟨1175961071391481118712131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 783974047594320745808087 1175961071391481118712131)
                ·
                  refine ⟨1763941607087221678068197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1175961071391481118712131 1763941607087221678068197)
                  ·
                    refine ⟨330739051328854064637787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1763941607087221678068197 330739051328854064637787)
                    ·
                      rfl

theorem cell22_966168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_966168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966168 prefixEnd_966168 := by exact prefixLift 966168
  have htrace : WordTrace (prefixWord ++ tailWord_966168) baseStart_966168 baseEnd_966168 := by
    simpa [prefixWord, tailWord_966168, baseEnd_966168] using wordTrace_append hprefix tailTrace_966168
  have hstable : (prefixWord ++ tailWord_966168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966168).length < 2 ^ (prefixWord ++ tailWord_966168).sum := by decide
  have hdescent : baseEnd_966168 < baseStart_966168 := by decide
  rcases family_descends (prefixWord ++ tailWord_966168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966177 : List Nat := [1, 2, 3, 2, 2, 12]
def baseStart_966177 : Nat := 118140960795 + 966177 * 2 ^ 59
def prefixEnd_966177 : Nat := 4983230072969 + 3 ^ 40 * 966177 * 2
def baseEnd_966177 : Nat := 4083236200157790631639

theorem tailTrace_966177 : CollatzResearch.WordTrace tailWord_966177 prefixEnd_966177 4083236200157790631639 := by
  unfold tailWord_966177
  simp only [CollatzResearch.WordTrace]
  refine ⟨35239370220713213739600785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23492913480475475826400523 35239370220713213739600785)
  ·
    refine ⟨26429527665534910304700589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35239370220713213739600785 26429527665534910304700589)
    ·
      refine ⟨9911072874575591364262721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26429527665534910304700589 9911072874575591364262721)
      ·
        refine ⟨7433304655931693523197041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9911072874575591364262721 7433304655931693523197041)
        ·
          refine ⟨5574978491948770142397781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7433304655931693523197041 5574978491948770142397781)
          ·
            refine ⟨4083236200157790631639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5574978491948770142397781 4083236200157790631639)
            ·
              rfl

theorem cell22_966177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 12].length) (baseStart_966177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966177 prefixEnd_966177 := by exact prefixLift 966177
  have htrace : WordTrace (prefixWord ++ tailWord_966177) baseStart_966177 baseEnd_966177 := by
    simpa [prefixWord, tailWord_966177, baseEnd_966177] using wordTrace_append hprefix tailTrace_966177
  have hstable : (prefixWord ++ tailWord_966177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966177).length < 2 ^ (prefixWord ++ tailWord_966177).sum := by decide
  have hdescent : baseEnd_966177 < baseStart_966177 := by decide
  rcases family_descends (prefixWord ++ tailWord_966177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966192 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_966192 : Nat := 118140960795 + 966192 * 2 ^ 59
def prefixEnd_966192 : Nat := 4983230072969 + 3 ^ 40 * 966192 * 2
def baseEnd_966192 : Nat := 330747267019326002037713

theorem tailTrace_966192 : CollatzResearch.WordTrace tailWord_966192 prefixEnd_966192 330747267019326002037713 := by
  unfold tailWord_966192
  simp only [CollatzResearch.WordTrace]
  refine ⟨17619958657829435650698415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23493278210439247534264553 17619958657829435650698415)
  ·
    refine ⟨26429937986744153476047623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17619958657829435650698415 26429937986744153476047623)
    ·
      refine ⟨39644906980116230214071435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26429937986744153476047623 39644906980116230214071435)
      ·
        refine ⟨59467360470174345321107153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39644906980116230214071435 59467360470174345321107153)
        ·
          refine ⟨44600520352630758990830365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59467360470174345321107153 44600520352630758990830365)
          ·
            refine ⟨16725195132236534621561387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44600520352630758990830365 16725195132236534621561387)
            ·
              refine ⟨25087792698354801932342081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16725195132236534621561387 25087792698354801932342081)
              ·
                refine ⟨18815844523766101449256561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25087792698354801932342081 18815844523766101449256561)
                ·
                  refine ⟨14111883392824576086942421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18815844523766101449256561 14111883392824576086942421)
                  ·
                    refine ⟨330747267019326002037713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14111883392824576086942421 330747267019326002037713)
                    ·
                      rfl

theorem cell22_966192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_966192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966192 prefixEnd_966192 := by exact prefixLift 966192
  have htrace : WordTrace (prefixWord ++ tailWord_966192) baseStart_966192 baseEnd_966192 := by
    simpa [prefixWord, tailWord_966192, baseEnd_966192] using wordTrace_append hprefix tailTrace_966192
  have hstable : (prefixWord ++ tailWord_966192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966192).length < 2 ^ (prefixWord ++ tailWord_966192).sum := by decide
  have hdescent : baseEnd_966192 < baseStart_966192 := by decide
  rcases family_descends (prefixWord ++ tailWord_966192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966198 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_966198 : Nat := 118140960795 + 966198 * 2 ^ 59
def prefixEnd_966198 : Nat := 4983230072969 + 3 ^ 40 * 966198 * 2
def baseEnd_966198 : Nat := 330749320941943986387695

theorem tailTrace_966198 : CollatzResearch.WordTrace tailWord_966198 prefixEnd_966198 330749320941943986387695 := by
  unfold tailWord_966198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2202508509602320895382203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23493424102424756217410165 2202508509602320895382203)
  ·
    refine ⟨3303762764403481343073305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2202508509602320895382203 3303762764403481343073305)
    ·
      refine ⟨2477822073302611007304979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3303762764403481343073305 2477822073302611007304979)
      ·
        refine ⟨3716733109953916510957469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2477822073302611007304979 3716733109953916510957469)
        ·
          refine ⟨1393774916232718691609051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3716733109953916510957469 1393774916232718691609051)
          ·
            refine ⟨2090662374349078037413577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1393774916232718691609051 2090662374349078037413577)
            ·
              refine ⟨1567996780761808528060183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2090662374349078037413577 1567996780761808528060183)
              ·
                refine ⟨2351995171142712792090275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1567996780761808528060183 2351995171142712792090275)
                ·
                  refine ⟨3527992756714069188135413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2351995171142712792090275 3527992756714069188135413)
                  ·
                    refine ⟨330749320941943986387695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3527992756714069188135413 330749320941943986387695)
                    ·
                      rfl

theorem cell22_966198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_966198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966198 prefixEnd_966198 := by exact prefixLift 966198
  have htrace : WordTrace (prefixWord ++ tailWord_966198) baseStart_966198 baseEnd_966198 := by
    simpa [prefixWord, tailWord_966198, baseEnd_966198] using wordTrace_append hprefix tailTrace_966198
  have hstable : (prefixWord ++ tailWord_966198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966198).length < 2 ^ (prefixWord ++ tailWord_966198).sum := by decide
  have hdescent : baseEnd_966198 < baseStart_966198 := by decide
  rcases family_descends (prefixWord ++ tailWord_966198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966243 : List Nat := [1, 1, 1, 5, 1, 3, 2, 4, 1, 3]
def baseStart_966243 : Nat := 118140960795 + 966243 * 2 ^ 59
def prefixEnd_966243 : Nat := 4983230072969 + 3 ^ 40 * 966243 * 2
def baseEnd_966243 : Nat := 330764725361578869012557

theorem tailTrace_966243 : CollatzResearch.WordTrace tailWord_966243 prefixEnd_966243 330764725361578869012557 := by
  unfold tailWord_966243
  simp only [CollatzResearch.WordTrace]
  refine ⟨35241777438474107011503383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23494518292316071341002255 35241777438474107011503383)
  ·
    refine ⟨52862666157711160517255075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35241777438474107011503383 52862666157711160517255075)
    ·
      refine ⟨79293999236566740775882613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52862666157711160517255075 79293999236566740775882613)
      ·
        refine ⟨7433812428428131947738995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79293999236566740775882613 7433812428428131947738995)
        ·
          refine ⟨11150718642642197921608493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7433812428428131947738995 11150718642642197921608493)
          ·
            refine ⟨4181519490990824220603185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11150718642642197921608493 4181519490990824220603185)
            ·
              refine ⟨3136139618243118165452389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4181519490990824220603185 3136139618243118165452389)
              ·
                refine ⟨588026178420584656022323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3136139618243118165452389 588026178420584656022323)
                ·
                  refine ⟨882039267630876984033485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588026178420584656022323 882039267630876984033485)
                  ·
                    refine ⟨330764725361578869012557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 882039267630876984033485 330764725361578869012557)
                    ·
                      rfl

theorem cell22_966243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 4, 1, 3].length) (baseStart_966243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966243 prefixEnd_966243 := by exact prefixLift 966243
  have htrace : WordTrace (prefixWord ++ tailWord_966243) baseStart_966243 baseEnd_966243 := by
    simpa [prefixWord, tailWord_966243, baseEnd_966243] using wordTrace_append hprefix tailTrace_966243
  have hstable : (prefixWord ++ tailWord_966243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966243).length < 2 ^ (prefixWord ++ tailWord_966243).sum := by decide
  have hdescent : baseEnd_966243 < baseStart_966243 := by decide
  rcases family_descends (prefixWord ++ tailWord_966243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966329 : List Nat := [1, 2, 1, 4, 1, 1, 4, 8]
def baseStart_966329 : Nat := 118140960795 + 966329 * 2 ^ 59
def prefixEnd_966329 : Nat := 4983230072969 + 3 ^ 40 * 966329 * 2
def baseEnd_966329 : Nat := 36754907213233701262477

theorem tailTrace_966329 : CollatzResearch.WordTrace tailWord_966329 prefixEnd_966329 36754907213233701262477 := by
  unfold tailWord_966329
  simp only [CollatzResearch.WordTrace]
  refine ⟨35244914116162543699134041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23496609410775029132756027 35244914116162543699134041)
  ·
    refine ⟨26433685587121907774350531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35244914116162543699134041 26433685587121907774350531)
    ·
      refine ⟨39650528380682861661525797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26433685587121907774350531 39650528380682861661525797)
      ·
        refine ⟨7434474071378036561536087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39650528380682861661525797 7434474071378036561536087)
        ·
          refine ⟨11151711107067054842304131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7434474071378036561536087 11151711107067054842304131)
          ·
            refine ⟨16727566660600582263456197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11151711107067054842304131 16727566660600582263456197)
            ·
              refine ⟨3136418748862609174398037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16727566660600582263456197 3136418748862609174398037)
              ·
                refine ⟨36754907213233701262477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3136418748862609174398037 36754907213233701262477)
                ·
                  rfl

theorem cell22_966329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 8].length) (baseStart_966329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966329 prefixEnd_966329 := by exact prefixLift 966329
  have htrace : WordTrace (prefixWord ++ tailWord_966329) baseStart_966329 baseEnd_966329 := by
    simpa [prefixWord, tailWord_966329, baseEnd_966329] using wordTrace_append hprefix tailTrace_966329
  have hstable : (prefixWord ++ tailWord_966329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966329).length < 2 ^ (prefixWord ++ tailWord_966329).sum := by decide
  have hdescent : baseEnd_966329 < baseStart_966329 := by decide
  rcases family_descends (prefixWord ++ tailWord_966329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966346 : List Nat := [3, 1, 2, 1, 6, 9]
def baseStart_966346 : Nat := 118140960795 + 966346 * 2 ^ 59
def prefixEnd_966346 : Nat := 4983230072969 + 3 ^ 40 * 966346 * 2
def baseEnd_966346 : Nat := 4083950424278036218361

theorem tailTrace_966346 : CollatzResearch.WordTrace tailWord_966346 prefixEnd_966346 4083950424278036218361 := by
  unfold tailWord_966346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8811383539275238900625723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23497022771400637068335261 8811383539275238900625723)
  ·
    refine ⟨13217075308912858350938585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8811383539275238900625723 13217075308912858350938585)
    ·
      refine ⟨9912806481684643763203939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13217075308912858350938585 9912806481684643763203939)
      ·
        refine ⟨14869209722526965644805909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9912806481684643763203939 14869209722526965644805909)
        ·
          refine ⟨696994205743451514600277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14869209722526965644805909 696994205743451514600277)
          ·
            refine ⟨4083950424278036218361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 696994205743451514600277 4083950424278036218361)
            ·
              rfl

theorem cell22_966346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 9].length) (baseStart_966346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966346 prefixEnd_966346 := by exact prefixLift 966346
  have htrace : WordTrace (prefixWord ++ tailWord_966346) baseStart_966346 baseEnd_966346 := by
    simpa [prefixWord, tailWord_966346, baseEnd_966346] using wordTrace_append hprefix tailTrace_966346
  have hstable : (prefixWord ++ tailWord_966346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966346).length < 2 ^ (prefixWord ++ tailWord_966346).sum := by decide
  have hdescent : baseEnd_966346 < baseStart_966346 := by decide
  rcases family_descends (prefixWord ++ tailWord_966346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966359 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 1, 8]
def baseStart_966359 : Nat := 118140960795 + 966359 * 2 ^ 59
def prefixEnd_966359 : Nat := 4983230072969 + 3 ^ 40 * 966359 * 2
def baseEnd_966359 : Nat := 330804434532193233112201

theorem tailTrace_966359 : CollatzResearch.WordTrace tailWord_966359 prefixEnd_966359 330804434532193233112201 := by
  unfold tailWord_966359
  simp only [CollatzResearch.WordTrace]
  refine ⟨35246008306053858822726131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23497338870702572548484087 35246008306053858822726131)
  ·
    refine ⟨52869012459080788234089197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35246008306053858822726131 52869012459080788234089197)
    ·
      refine ⟨19825879672155295587783449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52869012459080788234089197 19825879672155295587783449)
      ·
        refine ⟨14869409754116471690837587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19825879672155295587783449 14869409754116471690837587)
        ·
          refine ⟨22304114631174707536256381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14869409754116471690837587 22304114631174707536256381)
          ·
            refine ⟨8364042986690515326096143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22304114631174707536256381 8364042986690515326096143)
            ·
              refine ⟨12546064480035772989144215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8364042986690515326096143 12546064480035772989144215)
              ·
                refine ⟨18819096720053659483716323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12546064480035772989144215 18819096720053659483716323)
                ·
                  refine ⟨28228645080080489225574485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18819096720053659483716323 28228645080080489225574485)
                  ·
                    refine ⟨330804434532193233112201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28228645080080489225574485 330804434532193233112201)
                    ·
                      rfl

theorem cell22_966359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_966359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966359 prefixEnd_966359 := by exact prefixLift 966359
  have htrace : WordTrace (prefixWord ++ tailWord_966359) baseStart_966359 baseEnd_966359 := by
    simpa [prefixWord, tailWord_966359, baseEnd_966359] using wordTrace_append hprefix tailTrace_966359
  have hstable : (prefixWord ++ tailWord_966359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966359).length < 2 ^ (prefixWord ++ tailWord_966359).sum := by decide
  have hdescent : baseEnd_966359 < baseStart_966359 := by decide
  rcases family_descends (prefixWord ++ tailWord_966359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966446 : List Nat := [4, 1, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_966446 : Nat := 118140960795 + 966446 * 2 ^ 59
def prefixEnd_966446 : Nat := 4983230072969 + 3 ^ 40 * 966446 * 2
def baseEnd_966446 : Nat := 330834216410154006186935

theorem tailTrace_966446 : CollatzResearch.WordTrace tailWord_966446 prefixEnd_966446 330834216410154006186935 := by
  unfold tailWord_966446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4406147682092334085142899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23499454304492448454095461 4406147682092334085142899)
  ·
    refine ⟨6609221523138501127714349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4406147682092334085142899 6609221523138501127714349)
    ·
      refine ⟨2478458071176937922892881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6609221523138501127714349 2478458071176937922892881)
      ·
        refine ⟨1858843553382703442169661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2478458071176937922892881 1858843553382703442169661)
        ·
          refine ⟨697066332518513790813623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1858843553382703442169661 697066332518513790813623)
          ·
            refine ⟨1045599498777770686220435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697066332518513790813623 1045599498777770686220435)
            ·
              refine ⟨1568399248166656029330653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1045599498777770686220435 1568399248166656029330653)
              ·
                refine ⟨588149718062496010998995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1568399248166656029330653 588149718062496010998995)
                ·
                  refine ⟨882224577093744016498493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588149718062496010998995 882224577093744016498493)
                  ·
                    refine ⟨330834216410154006186935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 882224577093744016498493 330834216410154006186935)
                    ·
                      rfl

theorem cell22_966446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_966446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966446 prefixEnd_966446 := by exact prefixLift 966446
  have htrace : WordTrace (prefixWord ++ tailWord_966446) baseStart_966446 baseEnd_966446 := by
    simpa [prefixWord, tailWord_966446, baseEnd_966446] using wordTrace_append hprefix tailTrace_966446
  have hstable : (prefixWord ++ tailWord_966446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966446).length < 2 ^ (prefixWord ++ tailWord_966446).sum := by decide
  have hdescent : baseEnd_966446 < baseStart_966446 := by decide
  rcases family_descends (prefixWord ++ tailWord_966446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966481 : List Nat := [1, 2, 2, 1, 5, 1, 1, 9]
def baseStart_966481 : Nat := 118140960795 + 966481 * 2 ^ 59
def prefixEnd_966481 : Nat := 4983230072969 + 3 ^ 40 * 966481 * 2
def baseEnd_966481 : Nat := 36760688625047286840203

theorem tailTrace_966481 : CollatzResearch.WordTrace tailWord_966481 prefixEnd_966481 36760688625047286840203 := by
  unfold tailWord_966481
  simp only [CollatzResearch.WordTrace]
  refine ⟨35250458011611873658667297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23500305341074582439111531 35250458011611873658667297)
  ·
    refine ⟨26437843508708905244000473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35250458011611873658667297 26437843508708905244000473)
    ·
      refine ⟨19828382631531678933000355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26437843508708905244000473 19828382631531678933000355)
      ·
        refine ⟨29742573947297518399500533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19828382631531678933000355 29742573947297518399500533)
        ·
          refine ⟨2788366307559142349953175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29742573947297518399500533 2788366307559142349953175)
          ·
            refine ⟨4182549461338713524929763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788366307559142349953175 4182549461338713524929763)
            ·
              refine ⟨6273824192008070287394645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182549461338713524929763 6273824192008070287394645)
              ·
                refine ⟨36760688625047286840203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6273824192008070287394645 36760688625047286840203)
                ·
                  rfl

theorem cell22_966481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 9].length) (baseStart_966481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966481 prefixEnd_966481 := by exact prefixLift 966481
  have htrace : WordTrace (prefixWord ++ tailWord_966481) baseStart_966481 baseEnd_966481 := by
    simpa [prefixWord, tailWord_966481, baseEnd_966481] using wordTrace_append hprefix tailTrace_966481
  have hstable : (prefixWord ++ tailWord_966481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966481).length < 2 ^ (prefixWord ++ tailWord_966481).sum := by decide
  have hdescent : baseEnd_966481 < baseStart_966481 := by decide
  rcases family_descends (prefixWord ++ tailWord_966481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966485 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 2, 3]
def baseStart_966485 : Nat := 118140960795 + 966485 * 2 ^ 59
def prefixEnd_966485 : Nat := 4983230072969 + 3 ^ 40 * 966485 * 2
def baseEnd_966485 : Nat := 330847566907170904461815

theorem tailTrace_966485 : CollatzResearch.WordTrace tailWord_966485 prefixEnd_966485 330847566907170904461815 := by
  unfold tailWord_966485
  simp only [CollatzResearch.WordTrace]
  refine ⟨35250603903597382341812909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23500402602398254894541939 35250603903597382341812909)
  ·
    refine ⟨13218976463849018378179841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35250603903597382341812909 13218976463849018378179841)
    ·
      refine ⟨9914232347886763783634881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13218976463849018378179841 9914232347886763783634881)
      ·
        refine ⟨7435674260915072837726161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9914232347886763783634881 7435674260915072837726161)
        ·
          refine ⟨5576755695686304628294621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7435674260915072837726161 5576755695686304628294621)
          ·
            refine ⟨2091283385882364235610483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5576755695686304628294621 2091283385882364235610483)
            ·
              refine ⟨3136925078823546353415725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091283385882364235610483 3136925078823546353415725)
              ·
                refine ⟨1176346904558829882530897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3136925078823546353415725 1176346904558829882530897)
                ·
                  refine ⟨882260178419122411898173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1176346904558829882530897 882260178419122411898173)
                  ·
                    refine ⟨330847566907170904461815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 882260178419122411898173 330847566907170904461815)
                    ·
                      rfl

theorem cell22_966485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_966485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966485 prefixEnd_966485 := by exact prefixLift 966485
  have htrace : WordTrace (prefixWord ++ tailWord_966485) baseStart_966485 baseEnd_966485 := by
    simpa [prefixWord, tailWord_966485, baseEnd_966485] using wordTrace_append hprefix tailTrace_966485
  have hstable : (prefixWord ++ tailWord_966485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966485).length < 2 ^ (prefixWord ++ tailWord_966485).sum := by decide
  have hdescent : baseEnd_966485 < baseStart_966485 := by decide
  rcases family_descends (prefixWord ++ tailWord_966485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966498 : List Nat := [3, 3, 2, 1, 2, 1, 2, 8]
def baseStart_966498 : Nat := 118140960795 + 966498 * 2 ^ 59
def prefixEnd_966498 : Nat := 4983230072969 + 3 ^ 40 * 966498 * 2
def baseEnd_966498 : Nat := 36761335230315911542975

theorem tailTrace_966498 : CollatzResearch.WordTrace tailWord_966498 prefixEnd_966498 36761335230315911542975 := by
  unfold tailWord_966498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8812769513137571390509037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23500718701700190374690765 8812769513137571390509037)
  ·
    refine ⟨3304788567426589271440889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8812769513137571390509037 3304788567426589271440889)
    ·
      refine ⟨2478591425569941953580667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3304788567426589271440889 2478591425569941953580667)
      ·
        refine ⟨3717887138354912930371001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2478591425569941953580667 3717887138354912930371001)
        ·
          refine ⟨2788415353766184697778251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3717887138354912930371001 2788415353766184697778251)
          ·
            refine ⟨4182623030649277046667377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2788415353766184697778251 4182623030649277046667377)
            ·
              refine ⟨3136967272986957785000533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4182623030649277046667377 3136967272986957785000533)
              ·
                refine ⟨36761335230315911542975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3136967272986957785000533 36761335230315911542975)
                ·
                  rfl

theorem cell22_966498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_966498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966498 prefixEnd_966498 := by exact prefixLift 966498
  have htrace : WordTrace (prefixWord ++ tailWord_966498) baseStart_966498 baseEnd_966498 := by
    simpa [prefixWord, tailWord_966498, baseEnd_966498] using wordTrace_append hprefix tailTrace_966498
  have hstable : (prefixWord ++ tailWord_966498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966498).length < 2 ^ (prefixWord ++ tailWord_966498).sum := by decide
  have hdescent : baseEnd_966498 < baseStart_966498 := by decide
  rcases family_descends (prefixWord ++ tailWord_966498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966500 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_966500 : Nat := 118140960795 + 966500 * 2 ^ 59
def prefixEnd_966500 : Nat := 4983230072969 + 3 ^ 40 * 966500 * 2
def baseEnd_966500 : Nat := 330852701713715865336769

theorem tailTrace_966500 : CollatzResearch.WordTrace tailWord_966500 prefixEnd_966500 330852701713715865336769 := by
  unfold tailWord_966500
  simp only [CollatzResearch.WordTrace]
  refine ⟨17625575499271519951804477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23500767332362026602405969 17625575499271519951804477)
  ·
    refine ⟨6609590812226819981926679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17625575499271519951804477 6609590812226819981926679)
    ·
      refine ⟨9914386218340229972890019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6609590812226819981926679 9914386218340229972890019)
      ·
        refine ⟨14871579327510344959335029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914386218340229972890019 14871579327510344959335029)
        ·
          refine ⟨1394210561954094839937659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14871579327510344959335029 1394210561954094839937659)
          ·
            refine ⟨2091315842931142259906489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394210561954094839937659 2091315842931142259906489)
            ·
              refine ⟨1568486882198356694929867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091315842931142259906489 1568486882198356694929867)
              ·
                refine ⟨2352730323297535042394801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568486882198356694929867 2352730323297535042394801)
                ·
                  refine ⟨1764547742473151281796101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2352730323297535042394801 1764547742473151281796101)
                  ·
                    refine ⟨330852701713715865336769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1764547742473151281796101 330852701713715865336769)
                    ·
                      rfl

theorem cell22_966500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_966500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966500 prefixEnd_966500 := by exact prefixLift 966500
  have htrace : WordTrace (prefixWord ++ tailWord_966500) baseStart_966500 baseEnd_966500 := by
    simpa [prefixWord, tailWord_966500, baseEnd_966500] using wordTrace_append hprefix tailTrace_966500
  have hstable : (prefixWord ++ tailWord_966500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966500).length < 2 ^ (prefixWord ++ tailWord_966500).sum := by decide
  have hdescent : baseEnd_966500 < baseStart_966500 := by decide
  rcases family_descends (prefixWord ++ tailWord_966500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966654 : List Nat := [4, 2, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_966654 : Nat := 118140960795 + 966654 * 2 ^ 59
def prefixEnd_966654 : Nat := 4983230072969 + 3 ^ 40 * 966654 * 2
def baseEnd_966654 : Nat := 330905419060910796986297

theorem tailTrace_966654 : CollatzResearch.WordTrace tailWord_966654 prefixEnd_966654 330905419060910796986297 := by
  unfold tailWord_966654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4407095979998140525589377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23504511893323416136476677 4407095979998140525589377)
  ·
    refine ⟨3305321984998605394192033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4407095979998140525589377 3305321984998605394192033)
    ·
      refine ⟨2478991488748954045644025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3305321984998605394192033 2478991488748954045644025)
      ·
        refine ⟨1859243616561715534233019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2478991488748954045644025 1859243616561715534233019)
        ·
          refine ⟨2788865424842573301349529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859243616561715534233019 2788865424842573301349529)
          ·
            refine ⟨2091649068631929976012147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2788865424842573301349529 2091649068631929976012147)
            ·
              refine ⟨3137473602947894964018221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091649068631929976012147 3137473602947894964018221)
              ·
                refine ⟨1176552601105460611506833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3137473602947894964018221 1176552601105460611506833)
                ·
                  refine ⟨882414450829095458630125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1176552601105460611506833 882414450829095458630125)
                  ·
                    refine ⟨330905419060910796986297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 882414450829095458630125 330905419060910796986297)
                    ·
                      rfl

theorem cell22_966654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_966654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966654 prefixEnd_966654 := by exact prefixLift 966654
  have htrace : WordTrace (prefixWord ++ tailWord_966654) baseStart_966654 baseEnd_966654 := by
    simpa [prefixWord, tailWord_966654, baseEnd_966654] using wordTrace_append hprefix tailTrace_966654
  have hstable : (prefixWord ++ tailWord_966654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966654).length < 2 ^ (prefixWord ++ tailWord_966654).sum := by decide
  have hdescent : baseEnd_966654 < baseStart_966654 := by decide
  rcases family_descends (prefixWord ++ tailWord_966654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966725 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_966725 : Nat := 118140960795 + 966725 * 2 ^ 59
def prefixEnd_966725 : Nat := 4983230072969 + 3 ^ 40 * 966725 * 2
def baseEnd_966725 : Nat := 330929723811890278461079

theorem tailTrace_966725 : CollatzResearch.WordTrace tailWord_966725 prefixEnd_966725 330929723811890278461079 := by
  unfold tailWord_966725
  simp only [CollatzResearch.WordTrace]
  refine ⟨35259357422727903330549629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23506238281818602220366419 35259357422727903330549629)
  ·
    refine ⟨13222259033522963748956111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35259357422727903330549629 13222259033522963748956111)
    ·
      refine ⟨19833388550284445623434167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13222259033522963748956111 19833388550284445623434167)
      ·
        refine ⟨29750082825426668435151251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19833388550284445623434167 29750082825426668435151251)
        ·
          refine ⟨44625124238140002652726877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29750082825426668435151251 44625124238140002652726877)
          ·
            refine ⟨16734421589302500994772579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44625124238140002652726877 16734421589302500994772579)
            ·
              refine ⟨25101632383953751492158869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16734421589302500994772579 25101632383953751492158869)
              ·
                refine ⟨1176639017997832101194947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25101632383953751492158869 1176639017997832101194947)
                ·
                  refine ⟨1764958526996748151792421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176639017997832101194947 1764958526996748151792421)
                  ·
                    refine ⟨330929723811890278461079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1764958526996748151792421 330929723811890278461079)
                    ·
                      rfl

theorem cell22_966725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_966725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966725 prefixEnd_966725 := by exact prefixLift 966725
  have htrace : WordTrace (prefixWord ++ tailWord_966725) baseStart_966725 baseEnd_966725 := by
    simpa [prefixWord, tailWord_966725, baseEnd_966725] using wordTrace_append hprefix tailTrace_966725
  have hstable : (prefixWord ++ tailWord_966725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966725).length < 2 ^ (prefixWord ++ tailWord_966725).sum := by decide
  have hdescent : baseEnd_966725 < baseStart_966725 := by decide
  rcases family_descends (prefixWord ++ tailWord_966725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966757 : List Nat := [1, 3, 1, 3, 2, 2, 2, 4, 4]
def baseStart_966757 : Nat := 118140960795 + 966757 * 2 ^ 59
def prefixEnd_966757 : Nat := 4983230072969 + 3 ^ 40 * 966757 * 2
def baseEnd_966757 : Nat := 110313559355284287220327

theorem tailTrace_966757 : CollatzResearch.WordTrace tailWord_966757 prefixEnd_966757 110313559355284287220327 := by
  unfold tailWord_966757
  simp only [CollatzResearch.WordTrace]
  refine ⟨35260524558611972795714525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23507016372407981863809683 35260524558611972795714525)
  ·
    refine ⟨13222696709479489798392947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35260524558611972795714525 13222696709479489798392947)
    ·
      refine ⟨19834045064219234697589421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13222696709479489798392947 19834045064219234697589421)
      ·
        refine ⟨7437766899082213011596033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19834045064219234697589421 7437766899082213011596033)
        ·
          refine ⟨5578325174311659758697025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7437766899082213011596033 5578325174311659758697025)
          ·
            refine ⟨4183743880733744819022769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5578325174311659758697025 4183743880733744819022769)
            ·
              refine ⟨3137807910550308614267077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4183743880733744819022769 3137807910550308614267077)
              ·
                refine ⟨588338983228182865175077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3137807910550308614267077 588338983228182865175077)
                ·
                  refine ⟨110313559355284287220327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 588338983228182865175077 110313559355284287220327)
                  ·
                    rfl

theorem cell22_966757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_966757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966757 prefixEnd_966757 := by exact prefixLift 966757
  have htrace : WordTrace (prefixWord ++ tailWord_966757) baseStart_966757 baseEnd_966757 := by
    simpa [prefixWord, tailWord_966757, baseEnd_966757] using wordTrace_append hprefix tailTrace_966757
  have hstable : (prefixWord ++ tailWord_966757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966757).length < 2 ^ (prefixWord ++ tailWord_966757).sum := by decide
  have hdescent : baseEnd_966757 < baseStart_966757 := by decide
  rcases family_descends (prefixWord ++ tailWord_966757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966770 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_966770 : Nat := 118140960795 + 966770 * 2 ^ 59
def prefixEnd_966770 : Nat := 4983230072969 + 3 ^ 40 * 966770 * 2
def baseEnd_966770 : Nat := 330945128231525161085941

theorem tailTrace_966770 : CollatzResearch.WordTrace tailWord_966770 prefixEnd_966770 330945128231525161085941 := by
  unfold tailWord_966770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8815249676891219003984441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23507332471709917343958509 8815249676891219003984441)
  ·
    refine ⟨6611437257668414252988331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8815249676891219003984441 6611437257668414252988331)
    ·
      refine ⟨9917155886502621379482497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6611437257668414252988331 9917155886502621379482497)
      ·
        refine ⟨7437866914876966034611873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9917155886502621379482497 7437866914876966034611873)
        ·
          refine ⟨5578400186157724525958905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7437866914876966034611873 5578400186157724525958905)
          ·
            refine ⟨4183800139618293394469179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5578400186157724525958905 4183800139618293394469179)
            ·
              refine ⟨6275700209427440091703769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4183800139618293394469179 6275700209427440091703769)
              ·
                refine ⟨4706775157070580068777827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275700209427440091703769 4706775157070580068777827)
                ·
                  refine ⟨7060162735605870103166741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706775157070580068777827 7060162735605870103166741)
                  ·
                    refine ⟨330945128231525161085941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7060162735605870103166741 330945128231525161085941)
                    ·
                      rfl

theorem cell22_966770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_966770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966770 prefixEnd_966770 := by exact prefixLift 966770
  have htrace : WordTrace (prefixWord ++ tailWord_966770) baseStart_966770 baseEnd_966770 := by
    simpa [prefixWord, tailWord_966770, baseEnd_966770] using wordTrace_append hprefix tailTrace_966770
  have hstable : (prefixWord ++ tailWord_966770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966770).length < 2 ^ (prefixWord ++ tailWord_966770).sum := by decide
  have hdescent : baseEnd_966770 < baseStart_966770 := by decide
  rcases family_descends (prefixWord ++ tailWord_966770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966823 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 2, 3]
def baseStart_966823 : Nat := 118140960795 + 966823 * 2 ^ 59
def prefixEnd_966823 : Nat := 4983230072969 + 3 ^ 40 * 966823 * 2
def baseEnd_966823 : Nat := 330963271214650689510779

theorem tailTrace_966823 : CollatzResearch.WordTrace tailWord_966823 prefixEnd_966823 330963271214650689510779 := by
  unfold tailWord_966823
  simp only [CollatzResearch.WordTrace]
  refine ⟨35262931776372866067617123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23508621184248577378411415 35262931776372866067617123)
  ·
    refine ⟨52894397664559299101425685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35262931776372866067617123 52894397664559299101425685)
    ·
      refine ⟨2479424890526217145379329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52894397664559299101425685 2479424890526217145379329)
      ·
        refine ⟨1859568667894662859034497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2479424890526217145379329 1859568667894662859034497)
        ·
          refine ⟨1394676500920997144275873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859568667894662859034497 1394676500920997144275873)
          ·
            refine ⟨1046007375690747858206905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1394676500920997144275873 1046007375690747858206905)
            ·
              refine ⟨784505531768060893655179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046007375690747858206905 784505531768060893655179)
              ·
                refine ⟨1176758297652091340482769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784505531768060893655179 1176758297652091340482769)
                ·
                  refine ⟨882568723239068505362077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1176758297652091340482769 882568723239068505362077)
                  ·
                    refine ⟨330963271214650689510779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 882568723239068505362077 330963271214650689510779)
                    ·
                      rfl

theorem cell22_966823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_966823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966823 prefixEnd_966823 := by exact prefixLift 966823
  have htrace : WordTrace (prefixWord ++ tailWord_966823) baseStart_966823 baseEnd_966823 := by
    simpa [prefixWord, tailWord_966823, baseEnd_966823] using wordTrace_append hprefix tailTrace_966823
  have hstable : (prefixWord ++ tailWord_966823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966823).length < 2 ^ (prefixWord ++ tailWord_966823).sum := by decide
  have hdescent : baseEnd_966823 < baseStart_966823 := by decide
  rcases family_descends (prefixWord ++ tailWord_966823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966845 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_966845 : Nat := 118140960795 + 966845 * 2 ^ 59
def prefixEnd_966845 : Nat := 4983230072969 + 3 ^ 40 * 966845 * 2
def baseEnd_966845 : Nat := 330970802264249965460711

theorem tailTrace_966845 : CollatzResearch.WordTrace tailWord_966845 prefixEnd_966845 330970802264249965460711 := by
  unfold tailWord_966845
  simp only [CollatzResearch.WordTrace]
  refine ⟨35263734182293163824917989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23509156121528775883278659 35263734182293163824917989)
  ·
    refine ⟨6611950159179968217172123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35263734182293163824917989 6611950159179968217172123)
    ·
      refine ⟨9917925238769952325758185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6611950159179968217172123 9917925238769952325758185)
      ·
        refine ⟨7438443929077464244318639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9917925238769952325758185 7438443929077464244318639)
        ·
          refine ⟨11157665893616196366477959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7438443929077464244318639 11157665893616196366477959)
          ·
            refine ⟨16736498840424294549716939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11157665893616196366477959 16736498840424294549716939)
            ·
              refine ⟨25104748260636441824575409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16736498840424294549716939 25104748260636441824575409)
              ·
                refine ⟨18828561195477331368431557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25104748260636441824575409 18828561195477331368431557)
                ·
                  refine ⟨3530355224151999631580917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18828561195477331368431557 3530355224151999631580917)
                  ·
                    refine ⟨330970802264249965460711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3530355224151999631580917 330970802264249965460711)
                    ·
                      rfl

theorem cell22_966845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_966845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966845 prefixEnd_966845 := by exact prefixLift 966845
  have htrace : WordTrace (prefixWord ++ tailWord_966845) baseStart_966845 baseEnd_966845 := by
    simpa [prefixWord, tailWord_966845, baseEnd_966845] using wordTrace_append hprefix tailTrace_966845
  have hstable : (prefixWord ++ tailWord_966845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966845).length < 2 ^ (prefixWord ++ tailWord_966845).sum := by decide
  have hdescent : baseEnd_966845 < baseStart_966845 := by decide
  rcases family_descends (prefixWord ++ tailWord_966845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966922 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_966922 : Nat := 118140960795 + 966922 * 2 ^ 59
def prefixEnd_966922 : Nat := 4983230072969 + 3 ^ 40 * 966922 * 2
def baseEnd_966922 : Nat := 330997160937847431285475

theorem tailTrace_966922 : CollatzResearch.WordTrace tailWord_966922 prefixEnd_966922 330997160937847431285475 := by
  unfold tailWord_966922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8816635650753551493867755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23511028402009470650314013 8816635650753551493867755)
  ·
    refine ⟨13224953476130327240801633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8816635650753551493867755 13224953476130327240801633)
    ·
      refine ⟨9918715107097745430601225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13224953476130327240801633 9918715107097745430601225)
      ·
        refine ⟨7439036330323309072950919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9918715107097745430601225 7439036330323309072950919)
        ·
          refine ⟨11158554495484963609426379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7439036330323309072950919 11158554495484963609426379)
          ·
            refine ⟨16737831743227445414139569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11158554495484963609426379 16737831743227445414139569)
            ·
              refine ⟨12553373807420584060604677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16737831743227445414139569 12553373807420584060604677)
              ·
                refine ⟨2353757588891359511363377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12553373807420584060604677 2353757588891359511363377)
                ·
                  refine ⟨1765318191668519633522533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2353757588891359511363377 1765318191668519633522533)
                  ·
                    refine ⟨330997160937847431285475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1765318191668519633522533 330997160937847431285475)
                    ·
                      rfl

theorem cell22_966922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_966922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966922 prefixEnd_966922 := by exact prefixLift 966922
  have htrace : WordTrace (prefixWord ++ tailWord_966922) baseStart_966922 baseEnd_966922 := by
    simpa [prefixWord, tailWord_966922, baseEnd_966922] using wordTrace_append hprefix tailTrace_966922
  have hstable : (prefixWord ++ tailWord_966922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966922).length < 2 ^ (prefixWord ++ tailWord_966922).sum := by decide
  have hdescent : baseEnd_966922 < baseStart_966922 := by decide
  rcases family_descends (prefixWord ++ tailWord_966922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966941 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_966941 : Nat := 118140960795 + 966941 * 2 ^ 59
def prefixEnd_966941 : Nat := 4983230072969 + 3 ^ 40 * 966941 * 2
def baseEnd_966941 : Nat := 331003665026137715060417

theorem tailTrace_966941 : CollatzResearch.WordTrace tailWord_966941 prefixEnd_966941 331003665026137715060417 := by
  unfold tailWord_966941
  simp only [CollatzResearch.WordTrace]
  refine ⟨35267235589945372220412677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23511490393296914813608451 35267235589945372220412677)
  ·
    refine ⟨6612606673114757291327377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35267235589945372220412677 6612606673114757291327377)
    ·
      refine ⟨4959455004836067968495533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6612606673114757291327377 4959455004836067968495533)
      ·
        refine ⟨1859795626813525488185825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4959455004836067968495533 1859795626813525488185825)
        ·
          refine ⟨1394846720110144116139369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859795626813525488185825 1394846720110144116139369)
          ·
            refine ⟨1046135040082608087104527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1394846720110144116139369 1046135040082608087104527)
            ·
              refine ⟨1569202560123912130656791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046135040082608087104527 1569202560123912130656791)
              ·
                refine ⟨2353803840185868195985187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569202560123912130656791 2353803840185868195985187)
                ·
                  refine ⟨3530705760278802293977781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353803840185868195985187 3530705760278802293977781)
                  ·
                    refine ⟨331003665026137715060417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3530705760278802293977781 331003665026137715060417)
                    ·
                      rfl

theorem cell22_966941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_966941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966941 prefixEnd_966941 := by exact prefixLift 966941
  have htrace : WordTrace (prefixWord ++ tailWord_966941) baseStart_966941 baseEnd_966941 := by
    simpa [prefixWord, tailWord_966941, baseEnd_966941] using wordTrace_append hprefix tailTrace_966941
  have hstable : (prefixWord ++ tailWord_966941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966941).length < 2 ^ (prefixWord ++ tailWord_966941).sum := by decide
  have hdescent : baseEnd_966941 < baseStart_966941 := by decide
  rcases family_descends (prefixWord ++ tailWord_966941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_966954 : List Nat := [3, 1, 4, 2, 2, 1, 1, 8]
def baseStart_966954 : Nat := 118140960795 + 966954 * 2 ^ 59
def prefixEnd_966954 : Nat := 4983230072969 + 3 ^ 40 * 966954 * 2
def baseEnd_966954 : Nat := 36778679465756668276153

theorem tailTrace_966954 : CollatzResearch.WordTrace tailWord_966954 prefixEnd_966954 36778679465756668276153 := by
  unfold tailWord_966954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8816927434724568860158979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23511806492598850293757277 8816927434724568860158979)
  ·
    refine ⟨13225391152086853290238469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8816927434724568860158979 13225391152086853290238469)
    ·
      refine ⟨2479760841016284991919713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13225391152086853290238469 2479760841016284991919713)
      ·
        refine ⟨1859820630762213743939785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2479760841016284991919713 1859820630762213743939785)
        ·
          refine ⟨1394865473071660307954839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859820630762213743939785 1394865473071660307954839)
          ·
            refine ⟨2092298209607490461932259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394865473071660307954839 2092298209607490461932259)
            ·
              refine ⟨3138447314411235692898389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2092298209607490461932259 3138447314411235692898389)
              ·
                refine ⟨36778679465756668276153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3138447314411235692898389 36778679465756668276153)
                ·
                  rfl

theorem cell22_966954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_966954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_966954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_966954 prefixEnd_966954 := by exact prefixLift 966954
  have htrace : WordTrace (prefixWord ++ tailWord_966954) baseStart_966954 baseEnd_966954 := by
    simpa [prefixWord, tailWord_966954, baseEnd_966954] using wordTrace_append hprefix tailTrace_966954
  have hstable : (prefixWord ++ tailWord_966954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_966954).length < 2 ^ (prefixWord ++ tailWord_966954).sum := by decide
  have hdescent : baseEnd_966954 < baseStart_966954 := by decide
  rcases family_descends (prefixWord ++ tailWord_966954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967074 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_967074 : Nat := 118140960795 + 967074 * 2 ^ 59
def prefixEnd_967074 : Nat := 4983230072969 + 3 ^ 40 * 967074 * 2
def baseEnd_967074 : Nat := 331049193644169701485009

theorem tailTrace_967074 : CollatzResearch.WordTrace tailWord_967074 prefixEnd_967074 331049193644169701485009 := by
  unfold tailWord_967074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818021624615883983751069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23514724332309023956669517 8818021624615883983751069)
  ·
    refine ⟨3306758109230956493906651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8818021624615883983751069 3306758109230956493906651)
    ·
      refine ⟨4960137163846434740859977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3306758109230956493906651 4960137163846434740859977)
      ·
        refine ⟨3720102872884826055644983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4960137163846434740859977 3720102872884826055644983)
        ·
          refine ⟨5580154309327239083467475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720102872884826055644983 5580154309327239083467475)
          ·
            refine ⟨8370231463990858625201213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580154309327239083467475 8370231463990858625201213)
            ·
              refine ⟨3138836798996571984450455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8370231463990858625201213 3138836798996571984450455)
              ·
                refine ⟨4708255198494857976675683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3138836798996571984450455 4708255198494857976675683)
                ·
                  refine ⟨7062382797742286965013525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4708255198494857976675683 7062382797742286965013525)
                  ·
                    refine ⟨331049193644169701485009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7062382797742286965013525 331049193644169701485009)
                    ·
                      rfl

theorem cell22_967074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_967074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967074 prefixEnd_967074 := by exact prefixLift 967074
  have htrace : WordTrace (prefixWord ++ tailWord_967074) baseStart_967074 baseEnd_967074 := by
    simpa [prefixWord, tailWord_967074, baseEnd_967074] using wordTrace_append hprefix tailTrace_967074
  have hstable : (prefixWord ++ tailWord_967074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967074).length < 2 ^ (prefixWord ++ tailWord_967074).sum := by decide
  have hdescent : baseEnd_967074 < baseStart_967074 := by decide
  rcases family_descends (prefixWord ++ tailWord_967074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967080 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 1, 4]
def baseStart_967080 : Nat := 118140960795 + 967080 * 2 ^ 59
def prefixEnd_967080 : Nat := 4983230072969 + 3 ^ 40 * 967080 * 2
def baseEnd_967080 : Nat := 331051247566787685834991

theorem tailTrace_967080 : CollatzResearch.WordTrace tailWord_967080 prefixEnd_967080 331051247566787685834991 := by
  unfold tailWord_967080
  simp only [CollatzResearch.WordTrace]
  refine ⟨17636152668220899479861347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23514870224294532639815129 17636152668220899479861347)
  ·
    refine ⟨26454229002331349219792021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17636152668220899479861347 26454229002331349219792021)
    ·
      refine ⟨1240041984484281994677751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26454229002331349219792021 1240041984484281994677751)
      ·
        refine ⟨1860062976726422992016627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240041984484281994677751 1860062976726422992016627)
        ·
          refine ⟨2790094465089634488024941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1860062976726422992016627 2790094465089634488024941)
          ·
            refine ⟨1046285424408612933009353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2790094465089634488024941 1046285424408612933009353)
            ·
              refine ⟨784714068306459699757015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1046285424408612933009353 784714068306459699757015)
              ·
                refine ⟨1177071102459689549635523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 784714068306459699757015 1177071102459689549635523)
                ·
                  refine ⟨1765606653689534324453285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177071102459689549635523 1765606653689534324453285)
                  ·
                    refine ⟨331051247566787685834991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1765606653689534324453285 331051247566787685834991)
                    ·
                      rfl

theorem cell22_967080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_967080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967080 prefixEnd_967080 := by exact prefixLift 967080
  have htrace : WordTrace (prefixWord ++ tailWord_967080) baseStart_967080 baseEnd_967080 := by
    simpa [prefixWord, tailWord_967080, baseEnd_967080] using wordTrace_append hprefix tailTrace_967080
  have hstable : (prefixWord ++ tailWord_967080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967080).length < 2 ^ (prefixWord ++ tailWord_967080).sum := by decide
  have hdescent : baseEnd_967080 < baseStart_967080 := by decide
  rcases family_descends (prefixWord ++ tailWord_967080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967164 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_967164 : Nat := 118140960795 + 967164 * 2 ^ 59
def prefixEnd_967164 : Nat := 4983230072969 + 3 ^ 40 * 967164 * 2
def baseEnd_967164 : Nat := 331080002483439466734733

theorem tailTrace_967164 : CollatzResearch.WordTrace tailWord_967164 prefixEnd_967164 331080002483439466734733 := by
  unfold tailWord_967164
  simp only [CollatzResearch.WordTrace]
  refine ⟨17637684534068740652890273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23516912712091654203853697 17637684534068740652890273)
  ·
    refine ⟨13228263400551555489667705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17637684534068740652890273 13228263400551555489667705)
    ·
      refine ⟨9921197550413666617250779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13228263400551555489667705 9921197550413666617250779)
      ·
        refine ⟨14881796325620499925876169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9921197550413666617250779 14881796325620499925876169)
        ·
          refine ⟨11161347244215374944407127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14881796325620499925876169 11161347244215374944407127)
          ·
            refine ⟨16742020866323062416610691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11161347244215374944407127 16742020866323062416610691)
            ·
              refine ⟨25113031299484593624916037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16742020866323062416610691 25113031299484593624916037)
              ·
                refine ⟨4708693368653361304671757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25113031299484593624916037 4708693368653361304671757)
                ·
                  refine ⟨1765760013245010489251909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4708693368653361304671757 1765760013245010489251909)
                  ·
                    refine ⟨331080002483439466734733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1765760013245010489251909 331080002483439466734733)
                    ·
                      rfl

theorem cell22_967164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_967164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967164 prefixEnd_967164 := by exact prefixLift 967164
  have htrace : WordTrace (prefixWord ++ tailWord_967164) baseStart_967164 baseEnd_967164 := by
    simpa [prefixWord, tailWord_967164, baseEnd_967164] using wordTrace_append hprefix tailTrace_967164
  have hstable : (prefixWord ++ tailWord_967164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967164).length < 2 ^ (prefixWord ++ tailWord_967164).sum := by decide
  have hdescent : baseEnd_967164 < baseStart_967164 := by decide
  rcases family_descends (prefixWord ++ tailWord_967164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967194 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_967194 : Nat := 118140960795 + 967194 * 2 ^ 59
def prefixEnd_967194 : Nat := 4983230072969 + 3 ^ 40 * 967194 * 2
def baseEnd_967194 : Nat := 331090272096529388484641

theorem tailTrace_967194 : CollatzResearch.WordTrace tailWord_967194 prefixEnd_967194 331090272096529388484641 := by
  unfold tailWord_967194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8819115814507199107343159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23517642172019197619581757 8819115814507199107343159)
  ·
    refine ⟨13228673721760798661014739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8819115814507199107343159 13228673721760798661014739)
    ·
      refine ⟨19843010582641197991522109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13228673721760798661014739 19843010582641197991522109)
      ·
        refine ⟨7441128968490449246820791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19843010582641197991522109 7441128968490449246820791)
        ·
          refine ⟨11161693452735673870231187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7441128968490449246820791 11161693452735673870231187)
          ·
            refine ⟨16742540179103510805346781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11161693452735673870231187 16742540179103510805346781)
            ·
              refine ⟨6278452567163816552005043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16742540179103510805346781 6278452567163816552005043)
              ·
                refine ⟨9417678850745724828007565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6278452567163816552005043 9417678850745724828007565)
                ·
                  refine ⟨3531629569029646810502837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9417678850745724828007565 3531629569029646810502837)
                  ·
                    refine ⟨331090272096529388484641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3531629569029646810502837 331090272096529388484641)
                    ·
                      rfl

theorem cell22_967194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_967194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967194 prefixEnd_967194 := by exact prefixLift 967194
  have htrace : WordTrace (prefixWord ++ tailWord_967194) baseStart_967194 baseEnd_967194 := by
    simpa [prefixWord, tailWord_967194, baseEnd_967194] using wordTrace_append hprefix tailTrace_967194
  have hstable : (prefixWord ++ tailWord_967194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967194).length < 2 ^ (prefixWord ++ tailWord_967194).sum := by decide
  have hdescent : baseEnd_967194 < baseStart_967194 := by decide
  rcases family_descends (prefixWord ++ tailWord_967194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967228 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 2, 3]
def baseStart_967228 : Nat := 118140960795 + 967228 * 2 ^ 59
def prefixEnd_967228 : Nat := 4983230072969 + 3 ^ 40 * 967228 * 2
def baseEnd_967228 : Nat := 331101910991364633134537

theorem tailTrace_967228 : CollatzResearch.WordTrace tailWord_967228 prefixEnd_967228 331101910991364633134537 := by
  unfold tailWord_967228
  simp only [CollatzResearch.WordTrace]
  refine ⟨17638851669952810118055169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23518468893270413490740225 17638851669952810118055169)
  ·
    refine ⟨13229138752464607588541377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17638851669952810118055169 13229138752464607588541377)
    ·
      refine ⟨9921854064348455691406033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13229138752464607588541377 9921854064348455691406033)
      ·
        refine ⟨7441390548261341768554525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9921854064348455691406033 7441390548261341768554525)
        ·
          refine ⟨2790521455598003163207947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7441390548261341768554525 2790521455598003163207947)
          ·
            refine ⟨4185782183397004744811921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2790521455598003163207947 4185782183397004744811921)
            ·
              refine ⟨3139336637547753558608941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4185782183397004744811921 3139336637547753558608941)
              ·
                refine ⟨1177251239080407584478353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3139336637547753558608941 1177251239080407584478353)
                ·
                  refine ⟨882938429310305688358765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1177251239080407584478353 882938429310305688358765)
                  ·
                    refine ⟨331101910991364633134537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 882938429310305688358765 331101910991364633134537)
                    ·
                      rfl

theorem cell22_967228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_967228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967228 prefixEnd_967228 := by exact prefixLift 967228
  have htrace : WordTrace (prefixWord ++ tailWord_967228) baseStart_967228 baseEnd_967228 := by
    simpa [prefixWord, tailWord_967228, baseEnd_967228] using wordTrace_append hprefix tailTrace_967228
  have hstable : (prefixWord ++ tailWord_967228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967228).length < 2 ^ (prefixWord ++ tailWord_967228).sum := by decide
  have hdescent : baseEnd_967228 < baseStart_967228 := by decide
  rcases family_descends (prefixWord ++ tailWord_967228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967346 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_967346 : Nat := 118140960795 + 967346 * 2 ^ 59
def prefixEnd_967346 : Nat := 4983230072969 + 3 ^ 40 * 967346 * 2
def baseEnd_967346 : Nat := 331142304802851658684175

theorem tailTrace_967346 : CollatzResearch.WordTrace tailWord_967346 prefixEnd_967346 331142304802851658684175 := by
  unfold tailWord_967346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8820501788369531597226473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23521338102318750925937261 8820501788369531597226473)
  ·
    refine ⟨6615376341277148697919855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8820501788369531597226473 6615376341277148697919855)
    ·
      refine ⟨9923064511915723046879783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6615376341277148697919855 9923064511915723046879783)
      ·
        refine ⟨14884596767873584570319675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9923064511915723046879783 14884596767873584570319675)
        ·
          refine ⟨22326895151810376855479513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14884596767873584570319675 22326895151810376855479513)
          ·
            refine ⟨16745171363857782641609635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22326895151810376855479513 16745171363857782641609635)
            ·
              refine ⟨25117757045786673962414453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16745171363857782641609635 25117757045786673962414453)
              ·
                refine ⟨2354789723042500683976355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25117757045786673962414453 2354789723042500683976355)
                ·
                  refine ⟨3532184584563751025964533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354789723042500683976355 3532184584563751025964533)
                  ·
                    refine ⟨331142304802851658684175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3532184584563751025964533 331142304802851658684175)
                    ·
                      rfl

theorem cell22_967346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_967346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967346 prefixEnd_967346 := by exact prefixLift 967346
  have htrace : WordTrace (prefixWord ++ tailWord_967346) baseStart_967346 baseEnd_967346 := by
    simpa [prefixWord, tailWord_967346, baseEnd_967346] using wordTrace_append hprefix tailTrace_967346
  have hstable : (prefixWord ++ tailWord_967346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967346).length < 2 ^ (prefixWord ++ tailWord_967346).sum := by decide
  have hdescent : baseEnd_967346 < baseStart_967346 := by decide
  rcases family_descends (prefixWord ++ tailWord_967346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967393 : List Nat := [1, 2, 3, 1, 4, 3, 1, 7]
def baseStart_967393 : Nat := 118140960795 + 967393 * 2 ^ 59
def prefixEnd_967393 : Nat := 4983230072969 + 3 ^ 40 * 967393 * 2
def baseEnd_967393 : Nat := 36795377095928800306559

theorem tailTrace_967393 : CollatzResearch.WordTrace tailWord_967393 prefixEnd_967393 36795377095928800306559 := by
  unfold tailWord_967393
  simp only [CollatzResearch.WordTrace]
  refine ⟨35283721384307853415866833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23522480922871902277244555 35283721384307853415866833)
  ·
    refine ⟨26462791038230890061900125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35283721384307853415866833 26462791038230890061900125)
    ·
      refine ⟨9923546639336583773212547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26462791038230890061900125 9923546639336583773212547)
      ·
        refine ⟨14885319959004875659818821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9923546639336583773212547 14885319959004875659818821)
        ·
          refine ⟨2790997492313414186216029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14885319959004875659818821 2790997492313414186216029)
          ·
            refine ⟨1046624059617530319831011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2790997492313414186216029 1046624059617530319831011)
            ·
              refine ⟨1569936089426295479746517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046624059617530319831011 1569936089426295479746517)
              ·
                refine ⟨36795377095928800306559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1569936089426295479746517 36795377095928800306559)
                ·
                  rfl

theorem cell22_967393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 7].length) (baseStart_967393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967393 prefixEnd_967393 := by exact prefixLift 967393
  have htrace : WordTrace (prefixWord ++ tailWord_967393) baseStart_967393 baseEnd_967393 := by
    simpa [prefixWord, tailWord_967393, baseEnd_967393] using wordTrace_append hprefix tailTrace_967393
  have hstable : (prefixWord ++ tailWord_967393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967393).length < 2 ^ (prefixWord ++ tailWord_967393).sum := by decide
  have hdescent : baseEnd_967393 < baseStart_967393 := by decide
  rcases family_descends (prefixWord ++ tailWord_967393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967408 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 3, 3]
def baseStart_967408 : Nat := 118140960795 + 967408 * 2 ^ 59
def prefixEnd_967408 : Nat := 4983230072969 + 3 ^ 40 * 967408 * 2
def baseEnd_967408 : Nat := 331163528669904163633985

theorem tailTrace_967408 : CollatzResearch.WordTrace tailWord_967408 prefixEnd_967408 331163528669904163633985 := by
  unfold tailWord_967408
  simp only [CollatzResearch.WordTrace]
  refine ⟨17642134239626755488831439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23522845652835673985108585 17642134239626755488831439)
  ·
    refine ⟨26463201359440133233247159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17642134239626755488831439 26463201359440133233247159)
    ·
      refine ⟨39694802039160199849870739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26463201359440133233247159 39694802039160199849870739)
      ·
        refine ⟨59542203058740299774806109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39694802039160199849870739 59542203058740299774806109)
        ·
          refine ⟨22328326147027612415552291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59542203058740299774806109 22328326147027612415552291)
          ·
            refine ⟨33492489220541418623328437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22328326147027612415552291 33492489220541418623328437)
            ·
              refine ⟨3139920864425757995937041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33492489220541418623328437 3139920864425757995937041)
              ·
                refine ⟨2354940648319318496952781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3139920864425757995937041 2354940648319318496952781)
                ·
                  refine ⟨883102743119744436357293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2354940648319318496952781 883102743119744436357293)
                  ·
                    refine ⟨331163528669904163633985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 883102743119744436357293 331163528669904163633985)
                    ·
                      rfl

theorem cell22_967408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3, 3].length) (baseStart_967408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967408 prefixEnd_967408 := by exact prefixLift 967408
  have htrace : WordTrace (prefixWord ++ tailWord_967408) baseStart_967408 baseEnd_967408 := by
    simpa [prefixWord, tailWord_967408, baseEnd_967408] using wordTrace_append hprefix tailTrace_967408
  have hstable : (prefixWord ++ tailWord_967408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967408).length < 2 ^ (prefixWord ++ tailWord_967408).sum := by decide
  have hdescent : baseEnd_967408 < baseStart_967408 := by decide
  rcases family_descends (prefixWord ++ tailWord_967408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967412 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_967412 : Nat := 118140960795 + 967412 * 2 ^ 59
def prefixEnd_967412 : Nat := 4983230072969 + 3 ^ 40 * 967412 * 2
def baseEnd_967412 : Nat := 331164897951649486533973

theorem tailTrace_967412 : CollatzResearch.WordTrace tailWord_967412 prefixEnd_967412 331164897951649486533973 := by
  unfold tailWord_967412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17642207185619509830404245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23522942914159346440538993 17642207185619509830404245)
  ·
    refine ⟨826978461825914523300199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17642207185619509830404245 826978461825914523300199)
    ·
      refine ⟨1240467692738871784950299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826978461825914523300199 1240467692738871784950299)
      ·
        refine ⟨1860701539108307677425449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240467692738871784950299 1860701539108307677425449)
        ·
          refine ⟨1395526154331230758069087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1860701539108307677425449 1395526154331230758069087)
          ·
            refine ⟨2093289231496846137103631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395526154331230758069087 2093289231496846137103631)
            ·
              refine ⟨3139933847245269205655447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093289231496846137103631 3139933847245269205655447)
              ·
                refine ⟨4709900770867903808483171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139933847245269205655447 4709900770867903808483171)
                ·
                  refine ⟨7064851156301855712724757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709900770867903808483171 7064851156301855712724757)
                  ·
                    refine ⟨331164897951649486533973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7064851156301855712724757 331164897951649486533973)
                    ·
                      rfl

theorem cell22_967412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_967412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967412 prefixEnd_967412 := by exact prefixLift 967412
  have htrace : WordTrace (prefixWord ++ tailWord_967412) baseStart_967412 baseEnd_967412 := by
    simpa [prefixWord, tailWord_967412, baseEnd_967412] using wordTrace_append hprefix tailTrace_967412
  have hstable : (prefixWord ++ tailWord_967412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967412).length < 2 ^ (prefixWord ++ tailWord_967412).sum := by decide
  have hdescent : baseEnd_967412 < baseStart_967412 := by decide
  rcases family_descends (prefixWord ++ tailWord_967412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967421 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 7]
def baseStart_967421 : Nat := 118140960795 + 967421 * 2 ^ 59
def prefixEnd_967421 : Nat := 4983230072969 + 3 ^ 40 * 967421 * 2
def baseEnd_967421 : Nat := 110389326278525487686315

theorem tailTrace_967421 : CollatzResearch.WordTrace tailWord_967421 prefixEnd_967421 110389326278525487686315 := by
  unfold tailWord_967421
  simp only [CollatzResearch.WordTrace]
  refine ⟨35284742628206414197886117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23523161752137609465257411 35284742628206414197886117)
  ·
    refine ⟨6615889242788702662103647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35284742628206414197886117 6615889242788702662103647)
    ·
      refine ⟨9923833864183053993155471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6615889242788702662103647 9923833864183053993155471)
      ·
        refine ⟨14885750796274580989733207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9923833864183053993155471 14885750796274580989733207)
        ·
          refine ⟨22328626194411871484599811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14885750796274580989733207 22328626194411871484599811)
          ·
            refine ⟨33492939291617807226899717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22328626194411871484599811 33492939291617807226899717)
            ·
              refine ⟨6279926117178338855043697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33492939291617807226899717 6279926117178338855043697)
              ·
                refine ⟨4709944587883754141282773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6279926117178338855043697 4709944587883754141282773)
                ·
                  refine ⟨110389326278525487686315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4709944587883754141282773 110389326278525487686315)
                  ·
                    rfl

theorem cell22_967421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_967421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967421 prefixEnd_967421 := by exact prefixLift 967421
  have htrace : WordTrace (prefixWord ++ tailWord_967421) baseStart_967421 baseEnd_967421 := by
    simpa [prefixWord, tailWord_967421, baseEnd_967421] using wordTrace_append hprefix tailTrace_967421
  have hstable : (prefixWord ++ tailWord_967421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967421).length < 2 ^ (prefixWord ++ tailWord_967421).sum := by decide
  have hdescent : baseEnd_967421 < baseStart_967421 := by decide
  rcases family_descends (prefixWord ++ tailWord_967421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967455 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 5]
def baseStart_967455 : Nat := 118140960795 + 967455 * 2 ^ 59
def prefixEnd_967455 : Nat := 4983230072969 + 3 ^ 40 * 967455 * 2
def baseEnd_967455 : Nat := 110393205910137235902947

theorem tailTrace_967455 : CollatzResearch.WordTrace tailWord_967455 prefixEnd_967455 110393205910137235902947 := by
  unfold tailWord_967455
  simp only [CollatzResearch.WordTrace]
  refine ⟨35285982710083238004623819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23523988473388825336415879 35285982710083238004623819)
  ·
    refine ⟨52928974065124857006935729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35285982710083238004623819 52928974065124857006935729)
    ·
      refine ⟨39696730548843642755201797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52928974065124857006935729 39696730548843642755201797)
      ·
        refine ⟨7443136977908183016600337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39696730548843642755201797 7443136977908183016600337)
        ·
          refine ⟨5582352733431137262450253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7443136977908183016600337 5582352733431137262450253)
          ·
            refine ⟨2093382275036676473418845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5582352733431137262450253 2093382275036676473418845)
            ·
              refine ⟨785018353138753677532067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2093382275036676473418845 785018353138753677532067)
              ·
                refine ⟨1177527529708130516298101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785018353138753677532067 1177527529708130516298101)
                ·
                  refine ⟨110393205910137235902947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1177527529708130516298101 110393205910137235902947)
                  ·
                    rfl

theorem cell22_967455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 5].length) (baseStart_967455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967455 prefixEnd_967455 := by exact prefixLift 967455
  have htrace : WordTrace (prefixWord ++ tailWord_967455) baseStart_967455 baseEnd_967455 := by
    simpa [prefixWord, tailWord_967455, baseEnd_967455] using wordTrace_append hprefix tailTrace_967455
  have hstable : (prefixWord ++ tailWord_967455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967455).length < 2 ^ (prefixWord ++ tailWord_967455).sum := by decide
  have hdescent : baseEnd_967455 < baseStart_967455 := by decide
  rcases family_descends (prefixWord ++ tailWord_967455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967476 : List Nat := [2, 5, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_967476 : Nat := 118140960795 + 967476 * 2 ^ 59
def prefixEnd_967476 : Nat := 4983230072969 + 3 ^ 40 * 967476 * 2
def baseEnd_967476 : Nat := 331186806459574652933777

theorem tailTrace_967476 : CollatzResearch.WordTrace tailWord_967476 prefixEnd_967476 331186806459574652933777 := by
  unfold tailWord_967476
  simp only [CollatzResearch.WordTrace]
  refine ⟨17643374321503579295569141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23524499095338105727425521 17643374321503579295569141)
  ·
    refine ⟨1654066342640960558959607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17643374321503579295569141 1654066342640960558959607)
    ·
      refine ⟨2481099513961440838439411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654066342640960558959607 2481099513961440838439411)
      ·
        refine ⟨3721649270942161257659117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2481099513961440838439411 3721649270942161257659117)
        ·
          refine ⟨1395618476603310471622169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3721649270942161257659117 1395618476603310471622169)
          ·
            refine ⟨1046713857452482853716627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1395618476603310471622169 1046713857452482853716627)
            ·
              refine ⟨1570070786178724280574941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046713857452482853716627 1570070786178724280574941)
              ·
                refine ⟨588776544817021605215603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1570070786178724280574941 588776544817021605215603)
                ·
                  refine ⟨883164817225532407823405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588776544817021605215603 883164817225532407823405)
                  ·
                    refine ⟨331186806459574652933777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 883164817225532407823405 331186806459574652933777)
                    ·
                      rfl

theorem cell22_967476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_967476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967476 prefixEnd_967476 := by exact prefixLift 967476
  have htrace : WordTrace (prefixWord ++ tailWord_967476) baseStart_967476 baseEnd_967476 := by
    simpa [prefixWord, tailWord_967476, baseEnd_967476] using wordTrace_append hprefix tailTrace_967476
  have hstable : (prefixWord ++ tailWord_967476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967476).length < 2 ^ (prefixWord ++ tailWord_967476).sum := by decide
  have hdescent : baseEnd_967476 < baseStart_967476 := by decide
  rcases family_descends (prefixWord ++ tailWord_967476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967500 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 6]
def baseStart_967500 : Nat := 118140960795 + 967500 * 2 ^ 59
def prefixEnd_967500 : Nat := 4983230072969 + 3 ^ 40 * 967500 * 2
def baseEnd_967500 : Nat := 110398340716682196777901

theorem tailTrace_967500 : CollatzResearch.WordTrace tailWord_967500 prefixEnd_967500 110398340716682196777901 := by
  unfold tailWord_967500
  simp only [CollatzResearch.WordTrace]
  refine ⟨17643811997460105345005977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23525082663280140460007969 17643811997460105345005977)
  ·
    refine ⟨13232858998095079008754483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17643811997460105345005977 13232858998095079008754483)
    ·
      refine ⟨19849288497142618513131725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13232858998095079008754483 19849288497142618513131725)
      ·
        refine ⟨7443483186428481942424397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19849288497142618513131725 7443483186428481942424397)
        ·
          refine ⟨2791306194910680728409149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7443483186428481942424397 2791306194910680728409149)
          ·
            refine ⟨1046739823091505273153431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2791306194910680728409149 1046739823091505273153431)
            ·
              refine ⟨1570109734637257909730147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1046739823091505273153431 1570109734637257909730147)
              ·
                refine ⟨2355164601955886864595221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570109734637257909730147 2355164601955886864595221)
                ·
                  refine ⟨110398340716682196777901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2355164601955886864595221 110398340716682196777901)
                  ·
                    rfl

theorem cell22_967500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_967500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967500 prefixEnd_967500 := by exact prefixLift 967500
  have htrace : WordTrace (prefixWord ++ tailWord_967500) baseStart_967500 baseEnd_967500 := by
    simpa [prefixWord, tailWord_967500, baseEnd_967500] using wordTrace_append hprefix tailTrace_967500
  have hstable : (prefixWord ++ tailWord_967500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967500).length < 2 ^ (prefixWord ++ tailWord_967500).sum := by decide
  have hdescent : baseEnd_967500 < baseStart_967500 := by decide
  rcases family_descends (prefixWord ++ tailWord_967500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967528 : List Nat := [2, 1, 4, 2, 1, 2, 2, 8]
def baseStart_967528 : Nat := 118140960795 + 967528 * 2 ^ 59
def prefixEnd_967528 : Nat := 4983230072969 + 3 ^ 40 * 967528 * 2
def baseEnd_967528 : Nat := 36800511902473761181513

theorem tailTrace_967528 : CollatzResearch.WordTrace tailWord_967528 prefixEnd_967528 36800511902473761181513 := by
  unfold tailWord_967528
  simp only [CollatzResearch.WordTrace]
  refine ⟨17644322619409385736015619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23525763492545847648020825 17644322619409385736015619)
  ·
    refine ⟨26466483929114078604023429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17644322619409385736015619 26466483929114078604023429)
    ·
      refine ⟨4962465736708889738254393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26466483929114078604023429 4962465736708889738254393)
      ·
        refine ⟨3721849302531667303690795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4962465736708889738254393 3721849302531667303690795)
        ·
          refine ⟨5582773953797500955536193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721849302531667303690795 5582773953797500955536193)
          ·
            refine ⟨4187080465348125716652145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5582773953797500955536193 4187080465348125716652145)
            ·
              refine ⟨3140310349011094287489109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4187080465348125716652145 3140310349011094287489109)
              ·
                refine ⟨36800511902473761181513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3140310349011094287489109 36800511902473761181513)
                ·
                  rfl

theorem cell22_967528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 8].length) (baseStart_967528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967528 prefixEnd_967528 := by exact prefixLift 967528
  have htrace : WordTrace (prefixWord ++ tailWord_967528) baseStart_967528 baseEnd_967528 := by
    simpa [prefixWord, tailWord_967528, baseEnd_967528] using wordTrace_append hprefix tailTrace_967528
  have hstable : (prefixWord ++ tailWord_967528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967528).length < 2 ^ (prefixWord ++ tailWord_967528).sum := by decide
  have hdescent : baseEnd_967528 < baseStart_967528 := by decide
  rcases family_descends (prefixWord ++ tailWord_967528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967588 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_967588 : Nat := 118140960795 + 967588 * 2 ^ 59
def prefixEnd_967588 : Nat := 4983230072969 + 3 ^ 40 * 967588 * 2
def baseEnd_967588 : Nat := 331225146348443694133433

theorem tailTrace_967588 : CollatzResearch.WordTrace tailWord_967588 prefixEnd_967588 331225146348443694133433 := by
  unfold tailWord_967588
  simp only [CollatzResearch.WordTrace]
  refine ⟨17645416809300700859607709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23527222412400934479476945 17645416809300700859607709)
  ·
    refine ⟨6617031303487762822352891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17645416809300700859607709 6617031303487762822352891)
    ·
      refine ⟨9925546955231644233529337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6617031303487762822352891 9925546955231644233529337)
      ·
        refine ⟨7444160216423733175147003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9925546955231644233529337 7444160216423733175147003)
        ·
          refine ⟨11166240324635599762720505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7444160216423733175147003 11166240324635599762720505)
          ·
            refine ⟨8374680243476699822040379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11166240324635599762720505 8374680243476699822040379)
            ·
              refine ⟨12562020365215049733060569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8374680243476699822040379 12562020365215049733060569)
              ·
                refine ⟨9421515273911287299795427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12562020365215049733060569 9421515273911287299795427)
                ·
                  refine ⟨14132272910866930949693141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421515273911287299795427 14132272910866930949693141)
                  ·
                    refine ⟨331225146348443694133433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14132272910866930949693141 331225146348443694133433)
                    ·
                      rfl

theorem cell22_967588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_967588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967588 prefixEnd_967588 := by exact prefixLift 967588
  have htrace : WordTrace (prefixWord ++ tailWord_967588) baseStart_967588 baseEnd_967588 := by
    simpa [prefixWord, tailWord_967588, baseEnd_967588] using wordTrace_append hprefix tailTrace_967588
  have hstable : (prefixWord ++ tailWord_967588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967588).length < 2 ^ (prefixWord ++ tailWord_967588).sum := by decide
  have hdescent : baseEnd_967588 < baseStart_967588 := by decide
  rcases family_descends (prefixWord ++ tailWord_967588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967603 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 5, 4]
def baseStart_967603 : Nat := 118140960795 + 967603 * 2 ^ 59
def prefixEnd_967603 : Nat := 4983230072969 + 3 ^ 40 * 967603 * 2
def baseEnd_967603 : Nat := 331230281154988655008387

theorem tailTrace_967603 : CollatzResearch.WordTrace tailWord_967603 prefixEnd_967603 331230281154988655008387 := by
  unfold tailWord_967603
  simp only [CollatzResearch.WordTrace]
  refine ⟨35291380713547059281011463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23527587142364706187340975 35291380713547059281011463)
  ·
    refine ⟨52937071070320588921517195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35291380713547059281011463 52937071070320588921517195)
    ·
      refine ⟨79405606605480883382275793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52937071070320588921517195 79405606605480883382275793)
      ·
        refine ⟨59554204954110662536706845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79405606605480883382275793 59554204954110662536706845)
        ·
          refine ⟨22332826857791498451265067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59554204954110662536706845 22332826857791498451265067)
          ·
            refine ⟨33499240286687247676897601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22332826857791498451265067 33499240286687247676897601)
            ·
              refine ⟨25124430215015435757673201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33499240286687247676897601 25124430215015435757673201)
              ·
                refine ⟨18843322661261576818254901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25124430215015435757673201 18843322661261576818254901)
                ·
                  refine ⟨1766561499493272826711397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18843322661261576818254901 1766561499493272826711397)
                  ·
                    refine ⟨331230281154988655008387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1766561499493272826711397 331230281154988655008387)
                    ·
                      rfl

theorem cell22_967603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 4].length) (baseStart_967603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967603 prefixEnd_967603 := by exact prefixLift 967603
  have htrace : WordTrace (prefixWord ++ tailWord_967603) baseStart_967603 baseEnd_967603 := by
    simpa [prefixWord, tailWord_967603, baseEnd_967603] using wordTrace_append hprefix tailTrace_967603
  have hstable : (prefixWord ++ tailWord_967603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967603).length < 2 ^ (prefixWord ++ tailWord_967603).sum := by decide
  have hdescent : baseEnd_967603 < baseStart_967603 := by decide
  rcases family_descends (prefixWord ++ tailWord_967603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967663 : List Nat := [1, 1, 2, 1, 4, 3, 10]
def baseStart_967663 : Nat := 118140960795 + 967663 * 2 ^ 59
def prefixEnd_967663 : Nat := 4983230072969 + 3 ^ 40 * 967663 * 2
def baseEnd_967663 : Nat := 12268548903006240685489

theorem tailTrace_967663 : CollatzResearch.WordTrace tailWord_967663 prefixEnd_967663 12268548903006240685489 := by
  unfold tailWord_967663
  simp only [CollatzResearch.WordTrace]
  refine ⟨35293569093329689528195643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23529046062219793018797095 35293569093329689528195643)
  ·
    refine ⟨52940353639994534292293465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35293569093329689528195643 52940353639994534292293465)
    ·
      refine ⟨39705265229995900719220099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52940353639994534292293465 39705265229995900719220099)
      ·
        refine ⟨59557897844993851078830149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39705265229995900719220099 59557897844993851078830149)
        ·
          refine ⟨11167105845936347077280653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59557897844993851078830149 11167105845936347077280653)
          ·
            refine ⟨4187664692226130153980245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11167105845936347077280653 4187664692226130153980245)
            ·
              refine ⟨12268548903006240685489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4187664692226130153980245 12268548903006240685489)
              ·
                rfl

theorem cell22_967663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 10].length) (baseStart_967663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967663 prefixEnd_967663 := by exact prefixLift 967663
  have htrace : WordTrace (prefixWord ++ tailWord_967663) baseStart_967663 baseEnd_967663 := by
    simpa [prefixWord, tailWord_967663, baseEnd_967663] using wordTrace_append hprefix tailTrace_967663
  have hstable : (prefixWord ++ tailWord_967663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967663).length < 2 ^ (prefixWord ++ tailWord_967663).sum := by decide
  have hdescent : baseEnd_967663 < baseStart_967663 := by decide
  rcases family_descends (prefixWord ++ tailWord_967663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967665 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 4, 4]
def baseStart_967665 : Nat := 118140960795 + 967665 * 2 ^ 59
def prefixEnd_967665 : Nat := 4983230072969 + 3 ^ 40 * 967665 * 2
def baseEnd_967665 : Nat := 331251505022041159958197

theorem tailTrace_967665 : CollatzResearch.WordTrace tailWord_967665 prefixEnd_967665 331251505022041159958197 := by
  unfold tailWord_967665
  simp only [CollatzResearch.WordTrace]
  refine ⟨35293642039322443869768449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23529094692881629246512299 35293642039322443869768449)
  ·
    refine ⟨26470231529491832902326337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35293642039322443869768449 26470231529491832902326337)
    ·
      refine ⟨19852673647118874676744753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26470231529491832902326337 19852673647118874676744753)
      ·
        refine ⟨14889505235339156007558565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19852673647118874676744753 14889505235339156007558565)
        ·
          refine ⟨2791782231626091751417231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14889505235339156007558565 2791782231626091751417231)
          ·
            refine ⟨4187673347439137627125847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791782231626091751417231 4187673347439137627125847)
            ·
              refine ⟨6281510021158706440688771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187673347439137627125847 6281510021158706440688771)
              ·
                refine ⟨9422265031738059661033157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281510021158706440688771 9422265031738059661033157)
                ·
                  refine ⟨1766674693450886186443717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9422265031738059661033157 1766674693450886186443717)
                  ·
                    refine ⟨331251505022041159958197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1766674693450886186443717 331251505022041159958197)
                    ·
                      rfl

theorem cell22_967665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_967665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967665 prefixEnd_967665 := by exact prefixLift 967665
  have htrace : WordTrace (prefixWord ++ tailWord_967665) baseStart_967665 baseEnd_967665 := by
    simpa [prefixWord, tailWord_967665, baseEnd_967665] using wordTrace_append hprefix tailTrace_967665
  have hstable : (prefixWord ++ tailWord_967665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967665).length < 2 ^ (prefixWord ++ tailWord_967665).sum := by decide
  have hdescent : baseEnd_967665 < baseStart_967665 := by decide
  rcases family_descends (prefixWord ++ tailWord_967665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967729 : List Nat := [1, 2, 2, 3, 1, 2, 3, 4, 1, 3]
def baseStart_967729 : Nat := 118140960795 + 967729 * 2 ^ 59
def prefixEnd_967729 : Nat := 4983230072969 + 3 ^ 40 * 967729 * 2
def baseEnd_967729 : Nat := 331273413529966326358001

theorem tailTrace_967729 : CollatzResearch.WordTrace tailWord_967729 prefixEnd_967729 331273413529966326358001 := by
  unfold tailWord_967729
  simp only [CollatzResearch.WordTrace]
  refine ⟨35295976311090582800098241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23530650874060388533398827 35295976311090582800098241)
  ·
    refine ⟨26471982233317937100073681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35295976311090582800098241 26471982233317937100073681)
    ·
      refine ⟨19853986674988452825055261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26471982233317937100073681 19853986674988452825055261)
      ·
        refine ⟨7445245003120669809395723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19853986674988452825055261 7445245003120669809395723)
        ·
          refine ⟨11167867504681004714093585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7445245003120669809395723 11167867504681004714093585)
          ·
            refine ⟨8375900628510753535570189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11167867504681004714093585 8375900628510753535570189)
            ·
              refine ⟨3140962735691532575838821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8375900628510753535570189 3140962735691532575838821)
              ·
                refine ⟨588930512942162357969779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3140962735691532575838821 588930512942162357969779)
                ·
                  refine ⟨883395769413243536954669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 588930512942162357969779 883395769413243536954669)
                  ·
                    refine ⟨331273413529966326358001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 883395769413243536954669 331273413529966326358001)
                    ·
                      rfl

theorem cell22_967729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_967729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967729 prefixEnd_967729 := by exact prefixLift 967729
  have htrace : WordTrace (prefixWord ++ tailWord_967729) baseStart_967729 baseEnd_967729 := by
    simpa [prefixWord, tailWord_967729, baseEnd_967729] using wordTrace_append hprefix tailTrace_967729
  have hstable : (prefixWord ++ tailWord_967729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967729).length < 2 ^ (prefixWord ++ tailWord_967729).sum := by decide
  have hdescent : baseEnd_967729 < baseStart_967729 := by decide
  rcases family_descends (prefixWord ++ tailWord_967729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967740 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_967740 : Nat := 118140960795 + 967740 * 2 ^ 59
def prefixEnd_967740 : Nat := 4983230072969 + 3 ^ 40 * 967740 * 2
def baseEnd_967740 : Nat := 331277179054765964332967

theorem tailTrace_967740 : CollatzResearch.WordTrace tailWord_967740 prefixEnd_967740 331277179054765964332967 := by
  unfold tailWord_967740
  simp only [CollatzResearch.WordTrace]
  refine ⟨17648188757025365839374337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23530918342700487785832449 17648188757025365839374337)
  ·
    refine ⟨13236141567769024379530753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17648188757025365839374337 13236141567769024379530753)
    ·
      refine ⟨9927106175826768284648065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13236141567769024379530753 9927106175826768284648065)
      ·
        refine ⟨7445329631870076213486049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9927106175826768284648065 7445329631870076213486049)
        ·
          refine ⟨5583997223902557160114537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7445329631870076213486049 5583997223902557160114537)
          ·
            refine ⟨4187997917926917870085903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5583997223902557160114537 4187997917926917870085903)
            ·
              refine ⟨6281996876890376805128855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187997917926917870085903 6281996876890376805128855)
              ·
                refine ⟨9422995315335565207693283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281996876890376805128855 9422995315335565207693283)
                ·
                  refine ⟨14134492973003347811539925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9422995315335565207693283 14134492973003347811539925)
                  ·
                    refine ⟨331277179054765964332967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14134492973003347811539925 331277179054765964332967)
                    ·
                      rfl

theorem cell22_967740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_967740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967740 prefixEnd_967740 := by exact prefixLift 967740
  have htrace : WordTrace (prefixWord ++ tailWord_967740) baseStart_967740 baseEnd_967740 := by
    simpa [prefixWord, tailWord_967740, baseEnd_967740] using wordTrace_append hprefix tailTrace_967740
  have hstable : (prefixWord ++ tailWord_967740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967740).length < 2 ^ (prefixWord ++ tailWord_967740).sum := by decide
  have hdescent : baseEnd_967740 < baseStart_967740 := by decide
  rcases family_descends (prefixWord ++ tailWord_967740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967800 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_967800 : Nat := 118140960795 + 967800 * 2 ^ 59
def prefixEnd_967800 : Nat := 4983230072969 + 3 ^ 40 * 967800 * 2
def baseEnd_967800 : Nat := 331297718280945807832783

theorem tailTrace_967800 : CollatzResearch.WordTrace tailWord_967800 prefixEnd_967800 331297718280945807832783 := by
  unfold tailWord_967800
  simp only [CollatzResearch.WordTrace]
  refine ⟨17649282946916680962966427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23532377262555574617288569 17649282946916680962966427)
  ·
    refine ⟨26473924420375021444449641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17649282946916680962966427 26473924420375021444449641)
    ·
      refine ⟨19855443315281266083337231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26473924420375021444449641 19855443315281266083337231)
      ·
        refine ⟨29783164972921899125005847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19855443315281266083337231 29783164972921899125005847)
        ·
          refine ⟨44674747459382848687508771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29783164972921899125005847 44674747459382848687508771)
          ·
            refine ⟨67012121189074273031263157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44674747459382848687508771 67012121189074273031263157)
            ·
              refine ⟨6282386361475713096680921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67012121189074273031263157 6282386361475713096680921)
              ·
                refine ⟨4711789771106784822510691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6282386361475713096680921 4711789771106784822510691)
                ·
                  refine ⟨7067684656660177233766037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711789771106784822510691 7067684656660177233766037)
                  ·
                    refine ⟨331297718280945807832783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7067684656660177233766037 331297718280945807832783)
                    ·
                      rfl

theorem cell22_967800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_967800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967800 prefixEnd_967800 := by exact prefixLift 967800
  have htrace : WordTrace (prefixWord ++ tailWord_967800) baseStart_967800 baseEnd_967800 := by
    simpa [prefixWord, tailWord_967800, baseEnd_967800] using wordTrace_append hprefix tailTrace_967800
  have hstable : (prefixWord ++ tailWord_967800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967800).length < 2 ^ (prefixWord ++ tailWord_967800).sum := by decide
  have hdescent : baseEnd_967800 < baseStart_967800 := by decide
  rcases family_descends (prefixWord ++ tailWord_967800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967832 : List Nat := [2, 1, 2, 4, 2, 3, 8]
def baseStart_967832 : Nat := 118140960795 + 967832 * 2 ^ 59
def prefixEnd_967832 : Nat := 4983230072969 + 3 ^ 40 * 967832 * 2
def baseEnd_967832 : Nat := 12270691575366977445655

theorem tailTrace_967832 : CollatzResearch.WordTrace tailWord_967832 prefixEnd_967832 12270691575366977445655 := by
  unfold tailWord_967832
  simp only [CollatzResearch.WordTrace]
  refine ⟨17649866514858715695548875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23533155353144954260731833 17649866514858715695548875)
  ·
    refine ⟨26474799772288073543323313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17649866514858715695548875 26474799772288073543323313)
    ·
      refine ⟨19856099829216055157492485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26474799772288073543323313 19856099829216055157492485)
      ·
        refine ⟨3723018717978010342029841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19856099829216055157492485 3723018717978010342029841)
        ·
          refine ⟨2792264038483507756522381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3723018717978010342029841 2792264038483507756522381)
          ·
            refine ⟨1047099014431315408695893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2792264038483507756522381 1047099014431315408695893)
            ·
              refine ⟨12270691575366977445655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1047099014431315408695893 12270691575366977445655)
              ·
                rfl

theorem cell22_967832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 8].length) (baseStart_967832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967832 prefixEnd_967832 := by exact prefixLift 967832
  have htrace : WordTrace (prefixWord ++ tailWord_967832) baseStart_967832 baseEnd_967832 := by
    simpa [prefixWord, tailWord_967832, baseEnd_967832] using wordTrace_append hprefix tailTrace_967832
  have hstable : (prefixWord ++ tailWord_967832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967832).length < 2 ^ (prefixWord ++ tailWord_967832).sum := by decide
  have hdescent : baseEnd_967832 < baseStart_967832 := by decide
  rcases family_descends (prefixWord ++ tailWord_967832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967834 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_967834 : Nat := 118140960795 + 967834 * 2 ^ 59
def prefixEnd_967834 : Nat := 4983230072969 + 3 ^ 40 * 967834 * 2
def baseEnd_967834 : Nat := 331309357175781052482679

theorem tailTrace_967834 : CollatzResearch.WordTrace tailWord_967834 prefixEnd_967834 331309357175781052482679 := by
  unfold tailWord_967834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8824951493927546433167639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23533203983806790488447037 8824951493927546433167639)
  ·
    refine ⟨13237427240891319649751459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8824951493927546433167639 13237427240891319649751459)
    ·
      refine ⟨19856140861336979474627189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13237427240891319649751459 19856140861336979474627189)
      ·
        refine ⟨1861513205750341825746299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19856140861336979474627189 1861513205750341825746299)
        ·
          refine ⟨2792269808625512738619449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861513205750341825746299 2792269808625512738619449)
          ·
            refine ⟨2094202356469134553964587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2792269808625512738619449 2094202356469134553964587)
            ·
              refine ⟨3141303534703701830946881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094202356469134553964587 3141303534703701830946881)
              ·
                refine ⟨2355977651027776373210161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141303534703701830946881 2355977651027776373210161)
                ·
                  refine ⟨1766983238270832279907621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2355977651027776373210161 1766983238270832279907621)
                  ·
                    refine ⟨331309357175781052482679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1766983238270832279907621 331309357175781052482679)
                    ·
                      rfl

theorem cell22_967834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_967834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967834 prefixEnd_967834 := by exact prefixLift 967834
  have htrace : WordTrace (prefixWord ++ tailWord_967834) baseStart_967834 baseEnd_967834 := by
    simpa [prefixWord, tailWord_967834, baseEnd_967834] using wordTrace_append hprefix tailTrace_967834
  have hstable : (prefixWord ++ tailWord_967834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967834).length < 2 ^ (prefixWord ++ tailWord_967834).sum := by decide
  have hdescent : baseEnd_967834 < baseStart_967834 := by decide
  rcases family_descends (prefixWord ++ tailWord_967834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967838 : List Nat := [4, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_967838 : Nat := 118140960795 + 967838 * 2 ^ 59
def prefixEnd_967838 : Nat := 4983230072969 + 3 ^ 40 * 967838 * 2
def baseEnd_967838 : Nat := 110436908819175458460889

theorem tailTrace_967838 : CollatzResearch.WordTrace tailWord_967838 prefixEnd_967838 110436908819175458460889 := by
  unfold tailWord_967838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4412493983461961801977021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23533301245130462943877445 4412493983461961801977021)
  ·
    refine ⟨1654685243798235675741383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4412493983461961801977021 1654685243798235675741383)
    ·
      refine ⟨2482027865697353513612075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654685243798235675741383 2482027865697353513612075)
      ·
        refine ⟨3723041798546030270418113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482027865697353513612075 3723041798546030270418113)
        ·
          refine ⟨2792281348909522702813585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3723041798546030270418113 2792281348909522702813585)
          ·
            refine ⟨2094211011682142027110189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2792281348909522702813585 2094211011682142027110189)
            ·
              refine ⟨785329129380803260166321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2094211011682142027110189 785329129380803260166321)
              ·
                refine ⟨588996847035602445124741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 785329129380803260166321 588996847035602445124741)
                ·
                  refine ⟨110436908819175458460889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 588996847035602445124741 110436908819175458460889)
                  ·
                    rfl

theorem cell22_967838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_967838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967838 prefixEnd_967838 := by exact prefixLift 967838
  have htrace : WordTrace (prefixWord ++ tailWord_967838) baseStart_967838 baseEnd_967838 := by
    simpa [prefixWord, tailWord_967838, baseEnd_967838] using wordTrace_append hprefix tailTrace_967838
  have hstable : (prefixWord ++ tailWord_967838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967838).length < 2 ^ (prefixWord ++ tailWord_967838).sum := by decide
  have hdescent : baseEnd_967838 < baseStart_967838 := by decide
  rcases family_descends (prefixWord ++ tailWord_967838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967875 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 3, 7]
def baseStart_967875 : Nat := 118140960795 + 967875 * 2 ^ 59
def prefixEnd_967875 : Nat := 4983230072969 + 3 ^ 40 * 967875 * 2
def baseEnd_967875 : Nat := 331323392313670612207553

theorem tailTrace_967875 : CollatzResearch.WordTrace tailWord_967875 prefixEnd_967875 331323392313670612207553 := by
  unfold tailWord_967875
  simp only [CollatzResearch.WordTrace]
  refine ⟨35301301368561649734913079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23534200912374433156608719 35301301368561649734913079)
  ·
    refine ⟨52951952052842474602369619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35301301368561649734913079 52951952052842474602369619)
    ·
      refine ⟨79427928079263711903554429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52951952052842474602369619 79427928079263711903554429)
      ·
        refine ⟨29785473029723891963832911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79427928079263711903554429 29785473029723891963832911)
        ·
          refine ⟨44678209544585837945749367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29785473029723891963832911 44678209544585837945749367)
          ·
            refine ⟨67017314316878756918624051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44678209544585837945749367 67017314316878756918624051)
            ·
              refine ⟨100525971475318135377936077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67017314316878756918624051 100525971475318135377936077)
              ·
                refine ⟨37697239303244300766726029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100525971475318135377936077 37697239303244300766726029)
                ·
                  refine ⟨14136464738716612787522261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37697239303244300766726029 14136464738716612787522261)
                  ·
                    refine ⟨331323392313670612207553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14136464738716612787522261 331323392313670612207553)
                    ·
                      rfl

theorem cell22_967875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_967875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967875 prefixEnd_967875 := by exact prefixLift 967875
  have htrace : WordTrace (prefixWord ++ tailWord_967875) baseStart_967875 baseEnd_967875 := by
    simpa [prefixWord, tailWord_967875, baseEnd_967875] using wordTrace_append hprefix tailTrace_967875
  have hstable : (prefixWord ++ tailWord_967875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967875).length < 2 ^ (prefixWord ++ tailWord_967875).sum := by decide
  have hdescent : baseEnd_967875 < baseStart_967875 := by decide
  rcases family_descends (prefixWord ++ tailWord_967875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967909 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_967909 : Nat := 118140960795 + 967909 * 2 ^ 59
def prefixEnd_967909 : Nat := 4983230072969 + 3 ^ 40 * 967909 * 2
def baseEnd_967909 : Nat := 331335031208505856857449

theorem tailTrace_967909 : CollatzResearch.WordTrace tailWord_967909 prefixEnd_967909 331335031208505856857449 := by
  unfold tailWord_967909
  simp only [CollatzResearch.WordTrace]
  refine ⟨35302541450438473541650781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23535027633625649027767187 35302541450438473541650781)
  ·
    refine ⟨13238453043914427578119043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35302541450438473541650781 13238453043914427578119043)
    ·
      refine ⟨19857679565871641367178565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13238453043914427578119043 19857679565871641367178565)
      ·
        refine ⟨3723314918600932756345981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19857679565871641367178565 3723314918600932756345981)
        ·
          refine ⟨1396243094475349783629743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3723314918600932756345981 1396243094475349783629743)
          ·
            refine ⟨2094364641713024675444615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396243094475349783629743 2094364641713024675444615)
            ·
              refine ⟨3141546962569537013166923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094364641713024675444615 3141546962569537013166923)
              ·
                refine ⟨4712320443854305519750385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3141546962569537013166923 4712320443854305519750385)
                ·
                  refine ⟨3534240332890729139812789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4712320443854305519750385 3534240332890729139812789)
                  ·
                    refine ⟨331335031208505856857449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3534240332890729139812789 331335031208505856857449)
                    ·
                      rfl

theorem cell22_967909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_967909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967909 prefixEnd_967909 := by exact prefixLift 967909
  have htrace : WordTrace (prefixWord ++ tailWord_967909) baseStart_967909 baseEnd_967909 := by
    simpa [prefixWord, tailWord_967909, baseEnd_967909] using wordTrace_append hprefix tailTrace_967909
  have hstable : (prefixWord ++ tailWord_967909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967909).length < 2 ^ (prefixWord ++ tailWord_967909).sum := by decide
  have hdescent : baseEnd_967909 < baseStart_967909 := by decide
  rcases family_descends (prefixWord ++ tailWord_967909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_967939 : List Nat := [1, 1, 1, 3, 2, 4, 1, 5, 4]
def baseStart_967939 : Nat := 118140960795 + 967939 * 2 ^ 59
def prefixEnd_967939 : Nat := 4983230072969 + 3 ^ 40 * 967939 * 2
def baseEnd_967939 : Nat := 110448433607198592869119

theorem tailTrace_967939 : CollatzResearch.WordTrace tailWord_967939 prefixEnd_967939 110448433607198592869119 := by
  unfold tailWord_967939
  simp only [CollatzResearch.WordTrace]
  refine ⟨35303635640329788665242871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23535757093553192443495247 35303635640329788665242871)
  ·
    refine ⟨52955453460494682997864307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35303635640329788665242871 52955453460494682997864307)
    ·
      refine ⟨79433180190742024496796461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52955453460494682997864307 79433180190742024496796461)
      ·
        refine ⟨29787442571528259186298673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79433180190742024496796461 29787442571528259186298673)
        ·
          refine ⟨22340581928646194389724005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29787442571528259186298673 22340581928646194389724005)
          ·
            refine ⟨4188859111621161448073251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22340581928646194389724005 4188859111621161448073251)
            ·
              refine ⟨6283288667431742172109877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4188859111621161448073251 6283288667431742172109877)
              ·
                refine ⟨589058312571725828635301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6283288667431742172109877 589058312571725828635301)
                ·
                  refine ⟨110448433607198592869119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 589058312571725828635301 110448433607198592869119)
                  ·
                    rfl

theorem cell22_967939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 4].length) (baseStart_967939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_967939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_967939 prefixEnd_967939 := by exact prefixLift 967939
  have htrace : WordTrace (prefixWord ++ tailWord_967939) baseStart_967939 baseEnd_967939 := by
    simpa [prefixWord, tailWord_967939, baseEnd_967939] using wordTrace_append hprefix tailTrace_967939
  have hstable : (prefixWord ++ tailWord_967939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_967939).length < 2 ^ (prefixWord ++ tailWord_967939).sum := by decide
  have hdescent : baseEnd_967939 < baseStart_967939 := by decide
  rcases family_descends (prefixWord ++ tailWord_967939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968089 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 1, 5]
def baseStart_968089 : Nat := 118140960795 + 968089 * 2 ^ 59
def prefixEnd_968089 : Nat := 4983230072969 + 3 ^ 40 * 968089 * 2
def baseEnd_968089 : Nat := 331396648887045387356897

theorem tailTrace_968089 : CollatzResearch.WordTrace tailWord_968089 prefixEnd_968089 331396648887045387356897 := by
  unfold tailWord_968089
  simp only [CollatzResearch.WordTrace]
  refine ⟨35309106589786364283203321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23539404393190909522135547 35309106589786364283203321)
  ·
    refine ⟨26481829942339773212402491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35309106589786364283203321 26481829942339773212402491)
    ·
      refine ⟨39722744913509659818603737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26481829942339773212402491 39722744913509659818603737)
      ·
        refine ⟨29792058685132244863952803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39722744913509659818603737 29792058685132244863952803)
        ·
          refine ⟨44688088027698367295929205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29792058685132244863952803 44688088027698367295929205)
          ·
            refine ⟨4189508252596721933993363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44688088027698367295929205 4189508252596721933993363)
            ·
              refine ⟨6284262378895082900990045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189508252596721933993363 6284262378895082900990045)
              ·
                refine ⟨2356598392085656087871267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6284262378895082900990045 2356598392085656087871267)
                ·
                  refine ⟨3534897588128484131806901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356598392085656087871267 3534897588128484131806901)
                  ·
                    refine ⟨331396648887045387356897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3534897588128484131806901 331396648887045387356897)
                    ·
                      rfl

theorem cell22_968089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_968089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968089 prefixEnd_968089 := by exact prefixLift 968089
  have htrace : WordTrace (prefixWord ++ tailWord_968089) baseStart_968089 baseEnd_968089 := by
    simpa [prefixWord, tailWord_968089, baseEnd_968089] using wordTrace_append hprefix tailTrace_968089
  have hstable : (prefixWord ++ tailWord_968089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968089).length < 2 ^ (prefixWord ++ tailWord_968089).sum := by decide
  have hdescent : baseEnd_968089 < baseStart_968089 := by decide
  rcases family_descends (prefixWord ++ tailWord_968089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968140 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 2, 3]
def baseStart_968140 : Nat := 118140960795 + 968140 * 2 ^ 59
def prefixEnd_968140 : Nat := 4983230072969 + 3 ^ 40 * 968140 * 2
def baseEnd_968140 : Nat := 331414107229298254331741

theorem tailTrace_968140 : CollatzResearch.WordTrace tailWord_968140 prefixEnd_968140 331414107229298254331741 := by
  unfold tailWord_968140
  simp only [CollatzResearch.WordTrace]
  refine ⟨17655483356300799996654937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23540644475067733328873249 17655483356300799996654937)
  ·
    refine ⟨13241612517225599997491203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17655483356300799996654937 13241612517225599997491203)
    ·
      refine ⟨19862418775838399996236805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13241612517225599997491203 19862418775838399996236805)
      ·
        refine ⟨3724203520469699999294401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19862418775838399996236805 3724203520469699999294401)
        ·
          refine ⟨2793152640352274999470801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3724203520469699999294401 2793152640352274999470801)
          ·
            refine ⟨2094864480264206249603101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2793152640352274999470801 2094864480264206249603101)
            ·
              refine ⟨785574180099077343601163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2094864480264206249603101 785574180099077343601163)
              ·
                refine ⟨1178361270148616015401745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785574180099077343601163 1178361270148616015401745)
                ·
                  refine ⟨883770952611462011551309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1178361270148616015401745 883770952611462011551309)
                  ·
                    refine ⟨331414107229298254331741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 883770952611462011551309 331414107229298254331741)
                    ·
                      rfl

theorem cell22_968140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_968140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968140 prefixEnd_968140 := by exact prefixLift 968140
  have htrace : WordTrace (prefixWord ++ tailWord_968140) baseStart_968140 baseEnd_968140 := by
    simpa [prefixWord, tailWord_968140, baseEnd_968140] using wordTrace_append hprefix tailTrace_968140
  have hstable : (prefixWord ++ tailWord_968140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968140).length < 2 ^ (prefixWord ++ tailWord_968140).sum := by decide
  have hdescent : baseEnd_968140 < baseStart_968140 := by decide
  rcases family_descends (prefixWord ++ tailWord_968140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968179 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 2, 5]
def baseStart_968179 : Nat := 118140960795 + 968179 * 2 ^ 59
def prefixEnd_968179 : Nat := 4983230072969 + 3 ^ 40 * 968179 * 2
def baseEnd_968179 : Nat := 331427457726315152606621

theorem tailTrace_968179 : CollatzResearch.WordTrace tailWord_968179 prefixEnd_968179 331427457726315152606621 := by
  unfold tailWord_968179
  simp only [CollatzResearch.WordTrace]
  refine ⟨35312389159460309653979591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23541592772973539769319727 35312389159460309653979591)
  ·
    refine ⟨52968583739190464480969387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35312389159460309653979591 52968583739190464480969387)
    ·
      refine ⟨79452875608785696721454081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52968583739190464480969387 79452875608785696721454081)
      ·
        refine ⟨59589656706589272541090561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79452875608785696721454081 59589656706589272541090561)
        ·
          refine ⟨44692242529941954405817921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59589656706589272541090561 44692242529941954405817921)
          ·
            refine ⟨33519181897456465804363441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44692242529941954405817921 33519181897456465804363441)
            ·
              refine ⟨25139386423092349353272581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33519181897456465804363441 25139386423092349353272581)
              ·
                refine ⟨4713634954329815503738609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25139386423092349353272581 4713634954329815503738609)
                ·
                  refine ⟨3535226215747361627803957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4713634954329815503738609 3535226215747361627803957)
                  ·
                    refine ⟨331427457726315152606621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3535226215747361627803957 331427457726315152606621)
                    ·
                      rfl

theorem cell22_968179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_968179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968179 prefixEnd_968179 := by exact prefixLift 968179
  have htrace : WordTrace (prefixWord ++ tailWord_968179) baseStart_968179 baseEnd_968179 := by
    simpa [prefixWord, tailWord_968179, baseEnd_968179] using wordTrace_append hprefix tailTrace_968179
  have hstable : (prefixWord ++ tailWord_968179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968179).length < 2 ^ (prefixWord ++ tailWord_968179).sum := by decide
  have hdescent : baseEnd_968179 < baseStart_968179 := by decide
  rcases family_descends (prefixWord ++ tailWord_968179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968209 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 8]
def baseStart_968209 : Nat := 118140960795 + 968209 * 2 ^ 59
def prefixEnd_968209 : Nat := 4983230072969 + 3 ^ 40 * 968209 * 2
def baseEnd_968209 : Nat := 110479242446468358118843

theorem tailTrace_968209 : CollatzResearch.WordTrace tailWord_968209 prefixEnd_968209 110479242446468358118843 := by
  unfold tailWord_968209
  simp only [CollatzResearch.WordTrace]
  refine ⟨35313483349351624777571681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23542322232901083185047787 35313483349351624777571681)
  ·
    refine ⟨26485112512013718583178761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35313483349351624777571681 26485112512013718583178761)
    ·
      refine ⟨19863834384010288937384071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26485112512013718583178761 19863834384010288937384071)
      ·
        refine ⟨29795751576015433406076107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19863834384010288937384071 29795751576015433406076107)
        ·
          refine ⟨44693627364023150109114161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29795751576015433406076107 44693627364023150109114161)
          ·
            refine ⟨33520220523017362581835621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44693627364023150109114161 33520220523017362581835621)
            ·
              refine ⟨6285041348065755484094179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33520220523017362581835621 6285041348065755484094179)
              ·
                refine ⟨9427562022098633226141269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6285041348065755484094179 9427562022098633226141269)
                ·
                  refine ⟨110479242446468358118843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9427562022098633226141269 110479242446468358118843)
                  ·
                    rfl

theorem cell22_968209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_968209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968209 prefixEnd_968209 := by exact prefixLift 968209
  have htrace : WordTrace (prefixWord ++ tailWord_968209) baseStart_968209 baseEnd_968209 := by
    simpa [prefixWord, tailWord_968209, baseEnd_968209] using wordTrace_append hprefix tailTrace_968209
  have hstable : (prefixWord ++ tailWord_968209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968209).length < 2 ^ (prefixWord ++ tailWord_968209).sum := by decide
  have hdescent : baseEnd_968209 < baseStart_968209 := by decide
  rcases family_descends (prefixWord ++ tailWord_968209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968211 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 3, 4]
def baseStart_968211 : Nat := 118140960795 + 968211 * 2 ^ 59
def prefixEnd_968211 : Nat := 4983230072969 + 3 ^ 40 * 968211 * 2
def baseEnd_968211 : Nat := 331438411980277735806523

theorem tailTrace_968211 : CollatzResearch.WordTrace tailWord_968211 prefixEnd_968211 331438411980277735806523 := by
  unfold tailWord_968211
  simp only [CollatzResearch.WordTrace]
  refine ⟨35313556295344379119144487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23542370863562919412762991 35313556295344379119144487)
  ·
    refine ⟨52970334443016568678716731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35313556295344379119144487 52970334443016568678716731)
    ·
      refine ⟨79455501664524853018075097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52970334443016568678716731 79455501664524853018075097)
      ·
        refine ⟨59591626248393639763556323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79455501664524853018075097 59591626248393639763556323)
        ·
          refine ⟨89387439372590459645334485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59591626248393639763556323 89387439372590459645334485)
          ·
            refine ⟨2095018110295088897937527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 89387439372590459645334485 2095018110295088897937527)
            ·
              refine ⟨3142527165442633346906291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2095018110295088897937527 3142527165442633346906291)
              ·
                refine ⟨4713790748163950020359437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142527165442633346906291 4713790748163950020359437)
                ·
                  refine ⟨1767671530561481257634789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4713790748163950020359437 1767671530561481257634789)
                  ·
                    refine ⟨331438411980277735806523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1767671530561481257634789 331438411980277735806523)
                    ·
                      rfl

theorem cell22_968211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 4].length) (baseStart_968211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968211 prefixEnd_968211 := by exact prefixLift 968211
  have htrace : WordTrace (prefixWord ++ tailWord_968211) baseStart_968211 baseEnd_968211 := by
    simpa [prefixWord, tailWord_968211, baseEnd_968211] using wordTrace_append hprefix tailTrace_968211
  have hstable : (prefixWord ++ tailWord_968211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968211).length < 2 ^ (prefixWord ++ tailWord_968211).sum := by decide
  have hdescent : baseEnd_968211 < baseStart_968211 := by decide
  rcases family_descends (prefixWord ++ tailWord_968211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968243 : List Nat := [1, 1, 1, 2, 4, 4, 1, 4, 4]
def baseStart_968243 : Nat := 118140960795 + 968243 * 2 ^ 59
def prefixEnd_968243 : Nat := 4983230072969 + 3 ^ 40 * 968243 * 2
def baseEnd_968243 : Nat := 110483122078080106335475

theorem tailTrace_968243 : CollatzResearch.WordTrace tailWord_968243 prefixEnd_968243 110483122078080106335475 := by
  unfold tailWord_968243
  simp only [CollatzResearch.WordTrace]
  refine ⟨35314723431228448584309383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23543148954152299056206255 35314723431228448584309383)
  ·
    refine ⟨52972085146842672876464075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35314723431228448584309383 52972085146842672876464075)
    ·
      refine ⟨79458127720264009314696113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52972085146842672876464075 79458127720264009314696113)
      ·
        refine ⟨59593595790198006986022085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79458127720264009314696113 59593595790198006986022085)
        ·
          refine ⟨11173799210662126309879141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59593595790198006986022085 11173799210662126309879141)
          ·
            refine ⟨2095087351999148683102339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11173799210662126309879141 2095087351999148683102339)
            ·
              refine ⟨3142631027998723024653509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2095087351999148683102339 3142631027998723024653509)
              ·
                refine ⟨589243317749760567122533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3142631027998723024653509 589243317749760567122533)
                ·
                  refine ⟨110483122078080106335475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 589243317749760567122533 110483122078080106335475)
                  ·
                    rfl

theorem cell22_968243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 4].length) (baseStart_968243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968243 prefixEnd_968243 := by exact prefixLift 968243
  have htrace : WordTrace (prefixWord ++ tailWord_968243) baseStart_968243 baseEnd_968243 := by
    simpa [prefixWord, tailWord_968243, baseEnd_968243] using wordTrace_append hprefix tailTrace_968243
  have hstable : (prefixWord ++ tailWord_968243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968243).length < 2 ^ (prefixWord ++ tailWord_968243).sum := by decide
  have hdescent : baseEnd_968243 < baseStart_968243 := by decide
  rcases family_descends (prefixWord ++ tailWord_968243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968354 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_968354 : Nat := 118140960795 + 968354 * 2 ^ 59
def prefixEnd_968354 : Nat := 4983230072969 + 3 ^ 40 * 968354 * 2
def baseEnd_968354 : Nat := 331487363802673029481085

theorem tailTrace_968354 : CollatzResearch.WordTrace tailWord_968354 prefixEnd_968354 331487363802673029481085 := by
  unfold tailWord_968354
  simp only [CollatzResearch.WordTrace]
  refine ⟨8829692983456578635400029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23545847955884209694400077 8829692983456578635400029)
  ·
    refine ⟨3311134868796216988275011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8829692983456578635400029 3311134868796216988275011)
    ·
      refine ⟨4966702303194325482412517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3311134868796216988275011 4966702303194325482412517)
      ·
        refine ⟨931256681848936027952347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4966702303194325482412517 931256681848936027952347)
        ·
          refine ⟨1396885022773404041928521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931256681848936027952347 1396885022773404041928521)
          ·
            refine ⟨1047663767080053031446391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1396885022773404041928521 1047663767080053031446391)
            ·
              refine ⟨1571495650620079547169587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1047663767080053031446391 1571495650620079547169587)
              ·
                refine ⟨2357243475930119320754381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571495650620079547169587 2357243475930119320754381)
                ·
                  refine ⟨883966303473794745282893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2357243475930119320754381 883966303473794745282893)
                  ·
                    refine ⟨331487363802673029481085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 883966303473794745282893 331487363802673029481085)
                    ·
                      rfl

theorem cell22_968354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_968354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968354 prefixEnd_968354 := by exact prefixLift 968354
  have htrace : WordTrace (prefixWord ++ tailWord_968354) baseStart_968354 baseEnd_968354 := by
    simpa [prefixWord, tailWord_968354, baseEnd_968354] using wordTrace_append hprefix tailTrace_968354
  have hstable : (prefixWord ++ tailWord_968354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968354).length < 2 ^ (prefixWord ++ tailWord_968354).sum := by decide
  have hdescent : baseEnd_968354 < baseStart_968354 := by decide
  rcases family_descends (prefixWord ++ tailWord_968354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968376 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_968376 : Nat := 118140960795 + 968376 * 2 ^ 59
def prefixEnd_968376 : Nat := 4983230072969 + 3 ^ 40 * 968376 * 2
def baseEnd_968376 : Nat := 331494894852272305431017

theorem tailTrace_968376 : CollatzResearch.WordTrace tailWord_968376 prefixEnd_968376 331494894852272305431017 := by
  unfold tailWord_968376
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659787169873306149450491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23546382893164408199267321 17659787169873306149450491)
  ·
    refine ⟨26489680754809959224175737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17659787169873306149450491 26489680754809959224175737)
    ·
      refine ⟨19867260566107469418131803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26489680754809959224175737 19867260566107469418131803)
      ·
        refine ⟨29800890849161204127197705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19867260566107469418131803 29800890849161204127197705)
        ·
          refine ⟨22350668136870903095398279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29800890849161204127197705 22350668136870903095398279)
          ·
            refine ⟨33526002205306354643097419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22350668136870903095398279 33526002205306354643097419)
            ·
              refine ⟨50289003307959531964646129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33526002205306354643097419 50289003307959531964646129)
              ·
                refine ⟨37716752480969648973484597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50289003307959531964646129 37716752480969648973484597)
                ·
                  refine ⟨3535945545090904591264181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37716752480969648973484597 3535945545090904591264181)
                  ·
                    refine ⟨331494894852272305431017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3535945545090904591264181 331494894852272305431017)
                    ·
                      rfl

theorem cell22_968376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_968376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968376 prefixEnd_968376 := by exact prefixLift 968376
  have htrace : WordTrace (prefixWord ++ tailWord_968376) baseStart_968376 baseEnd_968376 := by
    simpa [prefixWord, tailWord_968376, baseEnd_968376] using wordTrace_append hprefix tailTrace_968376
  have hstable : (prefixWord ++ tailWord_968376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968376).length < 2 ^ (prefixWord ++ tailWord_968376).sum := by decide
  have hdescent : baseEnd_968376 < baseStart_968376 := by decide
  rcases family_descends (prefixWord ++ tailWord_968376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968380 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_968380 : Nat := 118140960795 + 968380 * 2 ^ 59
def prefixEnd_968380 : Nat := 4983230072969 + 3 ^ 40 * 968380 * 2
def baseEnd_968380 : Nat := 331496264134017628331005

theorem tailTrace_968380 : CollatzResearch.WordTrace tailWord_968380 prefixEnd_968380 331496264134017628331005 := by
  unfold tailWord_968380
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659860115866060491023297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23546480154488080654697729 17659860115866060491023297)
  ·
    refine ⟨13244895086899545368267473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17659860115866060491023297 13244895086899545368267473)
    ·
      refine ⟨9933671315174659026200605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13244895086899545368267473 9933671315174659026200605)
      ·
        refine ⟨3725126743190497134825227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9933671315174659026200605 3725126743190497134825227)
        ·
          refine ⟨5587690114785745702237841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3725126743190497134825227 5587690114785745702237841)
          ·
            refine ⟨4190767586089309276678381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5587690114785745702237841 4190767586089309276678381)
            ·
              refine ⟨1571537844783490978754393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4190767586089309276678381 1571537844783490978754393)
              ·
                refine ⟨1178653383587618234065795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1571537844783490978754393 1178653383587618234065795)
                ·
                  refine ⟨1767980075381427351098693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178653383587618234065795 1767980075381427351098693)
                  ·
                    refine ⟨331496264134017628331005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1767980075381427351098693 331496264134017628331005)
                    ·
                      rfl

theorem cell22_968380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_968380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968380 prefixEnd_968380 := by exact prefixLift 968380
  have htrace : WordTrace (prefixWord ++ tailWord_968380) baseStart_968380 baseEnd_968380 := by
    simpa [prefixWord, tailWord_968380, baseEnd_968380] using wordTrace_append hprefix tailTrace_968380
  have hstable : (prefixWord ++ tailWord_968380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968380).length < 2 ^ (prefixWord ++ tailWord_968380).sum := by decide
  have hdescent : baseEnd_968380 < baseStart_968380 := by decide
  rcases family_descends (prefixWord ++ tailWord_968380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968408 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 2, 4]
def baseStart_968408 : Nat := 118140960795 + 968408 * 2 ^ 59
def prefixEnd_968408 : Nat := 4983230072969 + 3 ^ 40 * 968408 * 2
def baseEnd_968408 : Nat := 331505849106234888630919

theorem tailTrace_968408 : CollatzResearch.WordTrace tailWord_968408 prefixEnd_968408 331505849106234888630919 := by
  unfold tailWord_968408
  simp only [CollatzResearch.WordTrace]
  refine ⟨17660370737815340882032939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23547160983753787842710585 17660370737815340882032939)
  ·
    refine ⟨26490556106723011323049409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17660370737815340882032939 26490556106723011323049409)
    ·
      refine ⟨19867917080042258492287057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26490556106723011323049409 19867917080042258492287057)
      ·
        refine ⟨14900937810031693869215293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19867917080042258492287057 14900937810031693869215293)
        ·
          refine ⟨5587851678761885200955735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14900937810031693869215293 5587851678761885200955735)
          ·
            refine ⟨8381777518142827801433603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587851678761885200955735 8381777518142827801433603)
            ·
              refine ⟨12572666277214241702150405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8381777518142827801433603 12572666277214241702150405)
              ·
                refine ⟨2357374926977670319153201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12572666277214241702150405 2357374926977670319153201)
                ·
                  refine ⟨1768031195233252739364901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2357374926977670319153201 1768031195233252739364901)
                  ·
                    refine ⟨331505849106234888630919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1768031195233252739364901 331505849106234888630919)
                    ·
                      rfl

theorem cell22_968408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_968408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968408 prefixEnd_968408 := by exact prefixLift 968408
  have htrace : WordTrace (prefixWord ++ tailWord_968408) baseStart_968408 baseEnd_968408 := by
    simpa [prefixWord, tailWord_968408, baseEnd_968408] using wordTrace_append hprefix tailTrace_968408
  have hstable : (prefixWord ++ tailWord_968408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968408).length < 2 ^ (prefixWord ++ tailWord_968408).sum := by decide
  have hdescent : baseEnd_968408 < baseStart_968408 := by decide
  rcases family_descends (prefixWord ++ tailWord_968408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968410 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 2, 3]
def baseStart_968410 : Nat := 118140960795 + 968410 * 2 ^ 59
def prefixEnd_968410 : Nat := 4983230072969 + 3 ^ 40 * 968410 * 2
def baseEnd_968410 : Nat := 331506533747107550080913

theorem tailTrace_968410 : CollatzResearch.WordTrace tailWord_968410 prefixEnd_968410 331506533747107550080913 := by
  unfold tailWord_968410
  simp only [CollatzResearch.WordTrace]
  refine ⟨8830203605405859026409671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23547209614415624070425789 8830203605405859026409671)
  ·
    refine ⟨13245305408108788539614507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8830203605405859026409671 13245305408108788539614507)
    ·
      refine ⟨19867958112163182809421761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13245305408108788539614507 19867958112163182809421761)
      ·
        refine ⟨14900968584122387107066321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19867958112163182809421761 14900968584122387107066321)
        ·
          refine ⟨11175726438091790330299741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14900968584122387107066321 11175726438091790330299741)
          ·
            refine ⟨4190897414284421373862403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11175726438091790330299741 4190897414284421373862403)
            ·
              refine ⟨6286346121426632060793605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190897414284421373862403 6286346121426632060793605)
              ·
                refine ⟨1178689897767493511398801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6286346121426632060793605 1178689897767493511398801)
                ·
                  refine ⟨884017423325620133549101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1178689897767493511398801 884017423325620133549101)
                  ·
                    refine ⟨331506533747107550080913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 884017423325620133549101 331506533747107550080913)
                    ·
                      rfl

theorem cell22_968410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_968410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968410 prefixEnd_968410 := by exact prefixLift 968410
  have htrace : WordTrace (prefixWord ++ tailWord_968410) baseStart_968410 baseEnd_968410 := by
    simpa [prefixWord, tailWord_968410, baseEnd_968410] using wordTrace_append hprefix tailTrace_968410
  have hstable : (prefixWord ++ tailWord_968410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968410).length < 2 ^ (prefixWord ++ tailWord_968410).sum := by decide
  have hdescent : baseEnd_968410 < baseStart_968410 := by decide
  rcases family_descends (prefixWord ++ tailWord_968410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968472 : List Nat := [2, 1, 2, 3, 1, 1, 4, 4, 1, 3]
def baseStart_968472 : Nat := 118140960795 + 968472 * 2 ^ 59
def prefixEnd_968472 : Nat := 4983230072969 + 3 ^ 40 * 968472 * 2
def baseEnd_968472 : Nat := 331527757614160055030723

theorem tailTrace_968472 : CollatzResearch.WordTrace tailWord_968472 prefixEnd_968472 331527757614160055030723 := by
  unfold tailWord_968472
  simp only [CollatzResearch.WordTrace]
  refine ⟨17661537873699410347197835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23548717164932547129597113 17661537873699410347197835)
  ·
    refine ⟨26492306810549115520796753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17661537873699410347197835 26492306810549115520796753)
    ·
      refine ⟨19869230107911836640597565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26492306810549115520796753 19869230107911836640597565)
      ·
        refine ⟨7450961290466938740224087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19869230107911836640597565 7450961290466938740224087)
        ·
          refine ⟨11176441935700408110336131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7450961290466938740224087 11176441935700408110336131)
          ·
            refine ⟨16764662903550612165504197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11176441935700408110336131 16764662903550612165504197)
            ·
              refine ⟨3143374294415739781032037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16764662903550612165504197 3143374294415739781032037)
              ·
                refine ⟨589382680202951208943507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3143374294415739781032037 589382680202951208943507)
                ·
                  refine ⟨884074020304426813415261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 589382680202951208943507 884074020304426813415261)
                  ·
                    refine ⟨331527757614160055030723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 884074020304426813415261 331527757614160055030723)
                    ·
                      rfl

theorem cell22_968472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_968472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968472 prefixEnd_968472 := by exact prefixLift 968472
  have htrace : WordTrace (prefixWord ++ tailWord_968472) baseStart_968472 baseEnd_968472 := by
    simpa [prefixWord, tailWord_968472, baseEnd_968472] using wordTrace_append hprefix tailTrace_968472
  have hstable : (prefixWord ++ tailWord_968472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968472).length < 2 ^ (prefixWord ++ tailWord_968472).sum := by decide
  have hdescent : baseEnd_968472 < baseStart_968472 := by decide
  rcases family_descends (prefixWord ++ tailWord_968472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968478 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_968478 : Nat := 118140960795 + 968478 * 2 ^ 59
def prefixEnd_968478 : Nat := 4983230072969 + 3 ^ 40 * 968478 * 2
def baseEnd_968478 : Nat := 331529811536778039380705

theorem tailTrace_968478 : CollatzResearch.WordTrace tailWord_968478 prefixEnd_968478 331529811536778039380705 := by
  unfold tailWord_968478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415411823172135464889261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23548863056918055812742725 4415411823172135464889261)
  ·
    refine ⟨1655779433689550799333473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4415411823172135464889261 1655779433689550799333473)
    ·
      refine ⟨1241834575267163099500105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1655779433689550799333473 1241834575267163099500105)
      ·
        refine ⟨931375931450372324625079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1241834575267163099500105 931375931450372324625079)
        ·
          refine ⟨1397063897175558486937619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931375931450372324625079 1397063897175558486937619)
          ·
            refine ⟨2095595845763337730406429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397063897175558486937619 2095595845763337730406429)
            ·
              refine ⟨785848442161251648902411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2095595845763337730406429 785848442161251648902411)
              ·
                refine ⟨1178772663241877473353617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785848442161251648902411 1178772663241877473353617)
                ·
                  refine ⟨884079497431408105015213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1178772663241877473353617 884079497431408105015213)
                  ·
                    refine ⟨331529811536778039380705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 884079497431408105015213 331529811536778039380705)
                    ·
                      rfl

theorem cell22_968478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_968478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968478 prefixEnd_968478 := by exact prefixLift 968478
  have htrace : WordTrace (prefixWord ++ tailWord_968478) baseStart_968478 baseEnd_968478 := by
    simpa [prefixWord, tailWord_968478, baseEnd_968478] using wordTrace_append hprefix tailTrace_968478
  have hstable : (prefixWord ++ tailWord_968478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968478).length < 2 ^ (prefixWord ++ tailWord_968478).sum := by decide
  have hdescent : baseEnd_968478 < baseStart_968478 := by decide
  rcases family_descends (prefixWord ++ tailWord_968478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968483 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 2, 5]
def baseStart_968483 : Nat := 118140960795 + 968483 * 2 ^ 59
def prefixEnd_968483 : Nat := 4983230072969 + 3 ^ 40 * 968483 * 2
def baseEnd_968483 : Nat := 331531523138959693005689

theorem tailTrace_968483 : CollatzResearch.WordTrace tailWord_968483 prefixEnd_968483 331531523138959693005689 := by
  unfold tailWord_968483
  simp only [CollatzResearch.WordTrace]
  refine ⟨35323476950358969573046103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23548984633572646382030735 35323476950358969573046103)
  ·
    refine ⟨52985215425538454359569155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35323476950358969573046103 52985215425538454359569155)
    ·
      refine ⟨79477823138307681539353733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52985215425538454359569155 79477823138307681539353733)
      ·
        refine ⟨14902091838432690288628825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79477823138307681539353733 14902091838432690288628825)
        ·
          refine ⟨11176568878824517716471619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14902091838432690288628825 11176568878824517716471619)
          ·
            refine ⟨16764853318236776574707429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11176568878824517716471619 16764853318236776574707429)
            ·
              refine ⟨3143409997169395607757643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16764853318236776574707429 3143409997169395607757643)
              ·
                refine ⟨4715114995754093411636465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143409997169395607757643 4715114995754093411636465)
                ·
                  refine ⟨3536336246815570058727349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4715114995754093411636465 3536336246815570058727349)
                  ·
                    refine ⟨331531523138959693005689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3536336246815570058727349 331531523138959693005689)
                    ·
                      rfl

theorem cell22_968483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 5].length) (baseStart_968483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968483 prefixEnd_968483 := by exact prefixLift 968483
  have htrace : WordTrace (prefixWord ++ tailWord_968483) baseStart_968483 baseEnd_968483 := by
    simpa [prefixWord, tailWord_968483, baseEnd_968483] using wordTrace_append hprefix tailTrace_968483
  have hstable : (prefixWord ++ tailWord_968483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968483).length < 2 ^ (prefixWord ++ tailWord_968483).sum := by decide
  have hdescent : baseEnd_968483 < baseStart_968483 := by decide
  rcases family_descends (prefixWord ++ tailWord_968483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968515 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 1, 4]
def baseStart_968515 : Nat := 118140960795 + 968515 * 2 ^ 59
def prefixEnd_968515 : Nat := 4983230072969 + 3 ^ 40 * 968515 * 2
def baseEnd_968515 : Nat := 331542477392922276205591

theorem tailTrace_968515 : CollatzResearch.WordTrace tailWord_968515 prefixEnd_968515 331542477392922276205591 := by
  unfold tailWord_968515
  simp only [CollatzResearch.WordTrace]
  refine ⟨35324644086243039038210999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23549762724162026025473999 35324644086243039038210999)
  ·
    refine ⟨52986966129364558557316499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35324644086243039038210999 52986966129364558557316499)
    ·
      refine ⟨79480449194046837835974749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52986966129364558557316499 79480449194046837835974749)
      ·
        refine ⟨29805168447767564188490531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79480449194046837835974749 29805168447767564188490531)
        ·
          refine ⟨44707752671651346282735797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29805168447767564188490531 44707752671651346282735797)
          ·
            refine ⟨4191351812967313714006481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44707752671651346282735797 4191351812967313714006481)
            ·
              refine ⟨3143513859725485285504861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4191351812967313714006481 3143513859725485285504861)
              ·
                refine ⟨1178817697397056982064323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3143513859725485285504861 1178817697397056982064323)
                ·
                  refine ⟨1768226546095585473096485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178817697397056982064323 1768226546095585473096485)
                  ·
                    refine ⟨331542477392922276205591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1768226546095585473096485 331542477392922276205591)
                    ·
                      rfl

theorem cell22_968515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 4].length) (baseStart_968515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968515 prefixEnd_968515 := by exact prefixLift 968515
  have htrace : WordTrace (prefixWord ++ tailWord_968515) baseStart_968515 baseEnd_968515 := by
    simpa [prefixWord, tailWord_968515, baseEnd_968515] using wordTrace_append hprefix tailTrace_968515
  have hstable : (prefixWord ++ tailWord_968515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968515).length < 2 ^ (prefixWord ++ tailWord_968515).sum := by decide
  have hdescent : baseEnd_968515 < baseStart_968515 := by decide
  rcases family_descends (prefixWord ++ tailWord_968515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968530 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_968530 : Nat := 118140960795 + 968530 * 2 ^ 59
def prefixEnd_968530 : Nat := 4983230072969 + 3 ^ 40 * 968530 * 2
def baseEnd_968530 : Nat := 110515870733155745693515

theorem tailTrace_968530 : CollatzResearch.WordTrace tailWord_968530 prefixEnd_968530 110515870733155745693515 := by
  unfold tailWord_968530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8831297795297174150001761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23550127454125797733338029 8831297795297174150001761)
  ·
    refine ⟨6623473346472880612501321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8831297795297174150001761 6623473346472880612501321)
    ·
      refine ⟨4967605009854660459375991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6623473346472880612501321 4967605009854660459375991)
      ·
        refine ⟨7451407514781990689063987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4967605009854660459375991 7451407514781990689063987)
        ·
          refine ⟨11177111272172986033595981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7451407514781990689063987 11177111272172986033595981)
          ·
            refine ⟨4191416727064869762598493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11177111272172986033595981 4191416727064869762598493)
            ·
              refine ⟨1571781272649326160974435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4191416727064869762598493 1571781272649326160974435)
              ·
                refine ⟨2357671908973989241461653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571781272649326160974435 2357671908973989241461653)
                ·
                  refine ⟨110515870733155745693515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2357671908973989241461653 110515870733155745693515)
                  ·
                    rfl

theorem cell22_968530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_968530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968530 prefixEnd_968530 := by exact prefixLift 968530
  have htrace : WordTrace (prefixWord ++ tailWord_968530) baseStart_968530 baseEnd_968530 := by
    simpa [prefixWord, tailWord_968530, baseEnd_968530] using wordTrace_append hprefix tailTrace_968530
  have hstable : (prefixWord ++ tailWord_968530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968530).length < 2 ^ (prefixWord ++ tailWord_968530).sum := by decide
  have hdescent : baseEnd_968530 < baseStart_968530 := by decide
  rcases family_descends (prefixWord ++ tailWord_968530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968566 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_968566 : Nat := 118140960795 + 968566 * 2 ^ 59
def prefixEnd_968566 : Nat := 4983230072969 + 3 ^ 40 * 968566 * 2
def baseEnd_968566 : Nat := 331559935735175143180435

theorem tailTrace_968566 : CollatzResearch.WordTrace tailWord_968566 prefixEnd_968566 331559935735175143180435 := by
  unfold tailWord_968566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207906513066142171769847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23551002806038849832211701 2207906513066142171769847)
  ·
    refine ⟨3311859769599213257654771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2207906513066142171769847 3311859769599213257654771)
    ·
      refine ⟨4967789654398819886482157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3311859769599213257654771 4967789654398819886482157)
      ·
        refine ⟨1862921120399557457430809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4967789654398819886482157 1862921120399557457430809)
        ·
          refine ⟨1397190840299668093073107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1862921120399557457430809 1397190840299668093073107)
          ·
            refine ⟨2095786260449502139609661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397190840299668093073107 2095786260449502139609661)
            ·
              refine ⟨785919847668563302353623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2095786260449502139609661 785919847668563302353623)
              ·
                refine ⟨1178879771502844953530435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 785919847668563302353623 1178879771502844953530435)
                ·
                  refine ⟨1768319657254267430295653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178879771502844953530435 1768319657254267430295653)
                  ·
                    refine ⟨331559935735175143180435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1768319657254267430295653 331559935735175143180435)
                    ·
                      rfl

theorem cell22_968566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_968566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968566 prefixEnd_968566 := by exact prefixLift 968566
  have htrace : WordTrace (prefixWord ++ tailWord_968566) baseStart_968566 baseEnd_968566 := by
    simpa [prefixWord, tailWord_968566, baseEnd_968566] using wordTrace_append hprefix tailTrace_968566
  have hstable : (prefixWord ++ tailWord_968566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968566).length < 2 ^ (prefixWord ++ tailWord_968566).sum := by decide
  have hdescent : baseEnd_968566 < baseStart_968566 := by decide
  rcases family_descends (prefixWord ++ tailWord_968566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968637 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 5]
def baseStart_968637 : Nat := 118140960795 + 968637 * 2 ^ 59
def prefixEnd_968637 : Nat := 4983230072969 + 3 ^ 40 * 968637 * 2
def baseEnd_968637 : Nat := 110528080162051541551739

theorem tailTrace_968637 : CollatzResearch.WordTrace tailWord_968637 prefixEnd_968637 110528080162051541551739 := by
  unfold tailWord_968637
  simp only [CollatzResearch.WordTrace]
  refine ⟨35329093791801053874152165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23552729194534035916101443 35329093791801053874152165)
  ·
    refine ⟨6624205085962697601403531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35329093791801053874152165 6624205085962697601403531)
    ·
      refine ⟨9936307628944046402105297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6624205085962697601403531 9936307628944046402105297)
      ·
        refine ⟨7452230721708034801578973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9936307628944046402105297 7452230721708034801578973)
        ·
          refine ⟨2794586520640513050592115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7452230721708034801578973 2794586520640513050592115)
          ·
            refine ⟨4191879780960769575888173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794586520640513050592115 4191879780960769575888173)
            ·
              refine ⟨1571954917860288590958065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4191879780960769575888173 1571954917860288590958065)
              ·
                refine ⟨1178966188395216443218549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1571954917860288590958065 1178966188395216443218549)
                ·
                  refine ⟨110528080162051541551739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1178966188395216443218549 110528080162051541551739)
                  ·
                    rfl

theorem cell22_968637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_968637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968637 prefixEnd_968637 := by exact prefixLift 968637
  have htrace : WordTrace (prefixWord ++ tailWord_968637) baseStart_968637 baseEnd_968637 := by
    simpa [prefixWord, tailWord_968637, baseEnd_968637] using wordTrace_append hprefix tailTrace_968637
  have hstable : (prefixWord ++ tailWord_968637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968637).length < 2 ^ (prefixWord ++ tailWord_968637).sum := by decide
  have hdescent : baseEnd_968637 < baseStart_968637 := by decide
  rcases family_descends (prefixWord ++ tailWord_968637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968650 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_968650 : Nat := 118140960795 + 968650 * 2 ^ 59
def prefixEnd_968650 : Nat := 4983230072969 + 3 ^ 40 * 968650 * 2
def baseEnd_968650 : Nat := 331588690651826924080177

theorem tailTrace_968650 : CollatzResearch.WordTrace tailWord_968650 prefixEnd_968650 331588690651826924080177 := by
  unfold tailWord_968650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8832391985188489273593851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23553045293835971396250269 8832391985188489273593851)
  ·
    refine ⟨13248587977782733910390777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8832391985188489273593851 13248587977782733910390777)
    ·
      refine ⟨9936440983337050432793083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13248587977782733910390777 9936440983337050432793083)
      ·
        refine ⟨14904661475005575649189625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9936440983337050432793083 14904661475005575649189625)
        ·
          refine ⟨11178496106254181736892219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14904661475005575649189625 11178496106254181736892219)
          ·
            refine ⟨16767744159381272605338329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11178496106254181736892219 16767744159381272605338329)
            ·
              refine ⟨12575808119535954454003747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16767744159381272605338329 12575808119535954454003747)
              ·
                refine ⟨18863712179303931681005621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12575808119535954454003747 18863712179303931681005621)
                ·
                  refine ⟨1768473016809743595094277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18863712179303931681005621 1768473016809743595094277)
                  ·
                    refine ⟨331588690651826924080177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1768473016809743595094277 331588690651826924080177)
                    ·
                      rfl

theorem cell22_968650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_968650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968650 prefixEnd_968650 := by exact prefixLift 968650
  have htrace : WordTrace (prefixWord ++ tailWord_968650) baseStart_968650 baseEnd_968650 := by
    simpa [prefixWord, tailWord_968650, baseEnd_968650] using wordTrace_append hprefix tailTrace_968650
  have hstable : (prefixWord ++ tailWord_968650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968650).length < 2 ^ (prefixWord ++ tailWord_968650).sum := by decide
  have hdescent : baseEnd_968650 < baseStart_968650 := by decide
  rcases family_descends (prefixWord ++ tailWord_968650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968680 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_968680 : Nat := 118140960795 + 968680 * 2 ^ 59
def prefixEnd_968680 : Nat := 4983230072969 + 3 ^ 40 * 968680 * 2
def baseEnd_968680 : Nat := 331598960264916845830085

theorem tailTrace_968680 : CollatzResearch.WordTrace tailWord_968680 prefixEnd_968680 331598960264916845830085 := by
  unfold tailWord_968680
  simp only [CollatzResearch.WordTrace]
  refine ⟨17665331065322636108983747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23553774753763514811978329 17665331065322636108983747)
  ·
    refine ⟨26497996597983954163475621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17665331065322636108983747 26497996597983954163475621)
    ·
      refine ⟨4968374362121991405651679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26497996597983954163475621 4968374362121991405651679)
      ·
        refine ⟨7452561543182987108477519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4968374362121991405651679 7452561543182987108477519)
        ·
          refine ⟨11178842314774480662716279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7452561543182987108477519 11178842314774480662716279)
          ·
            refine ⟨16768263472161720994074419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11178842314774480662716279 16768263472161720994074419)
            ·
              refine ⟨25152395208242581491111629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16768263472161720994074419 25152395208242581491111629)
              ·
                refine ⟨9432148203090968059166861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25152395208242581491111629 9432148203090968059166861)
                ·
                  refine ⟨3537055576159113022187573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9432148203090968059166861 3537055576159113022187573)
                  ·
                    refine ⟨331598960264916845830085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3537055576159113022187573 331598960264916845830085)
                    ·
                      rfl

theorem cell22_968680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_968680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968680 prefixEnd_968680 := by exact prefixLift 968680
  have htrace : WordTrace (prefixWord ++ tailWord_968680) baseStart_968680 baseEnd_968680 := by
    simpa [prefixWord, tailWord_968680, baseEnd_968680] using wordTrace_append hprefix tailTrace_968680
  have hstable : (prefixWord ++ tailWord_968680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968680).length < 2 ^ (prefixWord ++ tailWord_968680).sum := by decide
  have hdescent : baseEnd_968680 < baseStart_968680 := by decide
  rcases family_descends (prefixWord ++ tailWord_968680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968697 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 4, 3]
def baseStart_968697 : Nat := 118140960795 + 968697 * 2 ^ 59
def prefixEnd_968697 : Nat := 4983230072969 + 3 ^ 40 * 968697 * 2
def baseEnd_968697 : Nat := 331604779712334468155033

theorem tailTrace_968697 : CollatzResearch.WordTrace tailWord_968697 prefixEnd_968697 331604779712334468155033 := by
  unfold tailWord_968697
  simp only [CollatzResearch.WordTrace]
  refine ⟨35331282171583684121336345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23554188114389122747557563 35331282171583684121336345)
  ·
    refine ⟨26498461628687763091002259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35331282171583684121336345 26498461628687763091002259)
    ·
      refine ⟨39747692443031644636503389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26498461628687763091002259 39747692443031644636503389)
      ·
        refine ⟨14905384666136866738688771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39747692443031644636503389 14905384666136866738688771)
        ·
          refine ⟨22358076999205300108033157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14905384666136866738688771 22358076999205300108033157)
          ·
            refine ⟨4192139437350993770256217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22358076999205300108033157 4192139437350993770256217)
            ·
              refine ⟨3144104578013245327692163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4192139437350993770256217 3144104578013245327692163)
              ·
                refine ⟨4716156867019867991538245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144104578013245327692163 4716156867019867991538245)
                ·
                  refine ⟨884279412566225248413421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4716156867019867991538245 884279412566225248413421)
                  ·
                    refine ⟨331604779712334468155033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 884279412566225248413421 331604779712334468155033)
                    ·
                      rfl

theorem cell22_968697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 3].length) (baseStart_968697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968697 prefixEnd_968697 := by exact prefixLift 968697
  have htrace : WordTrace (prefixWord ++ tailWord_968697) baseStart_968697 baseEnd_968697 := by
    simpa [prefixWord, tailWord_968697, baseEnd_968697] using wordTrace_append hprefix tailTrace_968697
  have hstable : (prefixWord ++ tailWord_968697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968697).length < 2 ^ (prefixWord ++ tailWord_968697).sum := by decide
  have hdescent : baseEnd_968697 < baseStart_968697 := by decide
  rcases family_descends (prefixWord ++ tailWord_968697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968744 : List Nat := [2, 1, 5, 3, 2, 9]
def baseStart_968744 : Nat := 118140960795 + 968744 * 2 ^ 59
def prefixEnd_968744 : Nat := 4983230072969 + 3 ^ 40 * 968744 * 2
def baseEnd_968744 : Nat := 4094084799664716200369

theorem tailTrace_968744 : CollatzResearch.WordTrace tailWord_968744 prefixEnd_968744 4094084799664716200369 := by
  unfold tailWord_968744
  simp only [CollatzResearch.WordTrace]
  refine ⟨17666498201206705574148643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23555330934942274098864857 17666498201206705574148643)
  ·
    refine ⟨26499747301810058361222965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17666498201206705574148643 26499747301810058361222965)
    ·
      refine ⟨2484351309544692971364653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26499747301810058361222965 2484351309544692971364653)
      ·
        refine ⟨931631741079259864261745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2484351309544692971364653 931631741079259864261745)
        ·
          refine ⟨698723805809444898196309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 931631741079259864261745 698723805809444898196309)
          ·
            refine ⟨4094084799664716200369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 698723805809444898196309 4094084799664716200369)
            ·
              rfl

theorem cell22_968744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 9].length) (baseStart_968744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968744 prefixEnd_968744 := by exact prefixLift 968744
  have htrace : WordTrace (prefixWord ++ tailWord_968744) baseStart_968744 baseEnd_968744 := by
    simpa [prefixWord, tailWord_968744, baseEnd_968744] using wordTrace_append hprefix tailTrace_968744
  have hstable : (prefixWord ++ tailWord_968744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968744).length < 2 ^ (prefixWord ++ tailWord_968744).sum := by decide
  have hdescent : baseEnd_968744 < baseStart_968744 := by decide
  rcases family_descends (prefixWord ++ tailWord_968744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968755 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 7]
def baseStart_968755 : Nat := 118140960795 + 968755 * 2 ^ 59
def prefixEnd_968755 : Nat := 4983230072969 + 3 ^ 40 * 968755 * 2
def baseEnd_968755 : Nat := 110541544765880550068285

theorem tailTrace_968755 : CollatzResearch.WordTrace tailWord_968755 prefixEnd_968755 110541544765880550068285 := by
  unfold tailWord_968755
  simp only [CollatzResearch.WordTrace]
  refine ⟨35333397605373560026947719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23555598403582373351298479 35333397605373560026947719)
  ·
    refine ⟨53000096408060340040421579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35333397605373560026947719 53000096408060340040421579)
    ·
      refine ⟨79500144612090510060632369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53000096408060340040421579 79500144612090510060632369)
      ·
        refine ⟨59625108459067882545474277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79500144612090510060632369 59625108459067882545474277)
        ·
          refine ⟨11179707836075227977276427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59625108459067882545474277 11179707836075227977276427)
          ·
            refine ⟨16769561754112841965914641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11179707836075227977276427 16769561754112841965914641)
            ·
              refine ⟨12577171315584631474435981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16769561754112841965914641 12577171315584631474435981)
              ·
                refine ⟨4716439243344236802913493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12577171315584631474435981 4716439243344236802913493)
                ·
                  refine ⟨110541544765880550068285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4716439243344236802913493 110541544765880550068285)
                  ·
                    rfl

theorem cell22_968755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 7].length) (baseStart_968755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968755 prefixEnd_968755 := by exact prefixLift 968755
  have htrace : WordTrace (prefixWord ++ tailWord_968755) baseStart_968755 baseEnd_968755 := by
    simpa [prefixWord, tailWord_968755, baseEnd_968755] using wordTrace_append hprefix tailTrace_968755
  have hstable : (prefixWord ++ tailWord_968755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968755).length < 2 ^ (prefixWord ++ tailWord_968755).sum := by decide
  have hdescent : baseEnd_968755 < baseStart_968755 := by decide
  rcases family_descends (prefixWord ++ tailWord_968755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968774 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_968774 : Nat := 118140960795 + 968774 * 2 ^ 59
def prefixEnd_968774 : Nat := 4983230072969 + 3 ^ 40 * 968774 * 2
def baseEnd_968774 : Nat := 331631138385931933979797

theorem tailTrace_968774 : CollatzResearch.WordTrace tailWord_968774 prefixEnd_968774 331631138385931933979797 := by
  unfold tailWord_968774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104190331009522695996543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23556060394869817514592917 1104190331009522695996543)
  ·
    refine ⟨1656285496514284043994815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1104190331009522695996543 1656285496514284043994815)
    ·
      refine ⟨2484428244771426065992223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1656285496514284043994815 2484428244771426065992223)
      ·
        refine ⟨3726642367157139098988335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484428244771426065992223 3726642367157139098988335)
        ·
          refine ⟨5589963550735708648482503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726642367157139098988335 5589963550735708648482503)
          ·
            refine ⟨8384945326103562972723755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589963550735708648482503 8384945326103562972723755)
            ·
              refine ⟨12577417989155344459085633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8384945326103562972723755 12577417989155344459085633)
              ·
                refine ⟨9433063491866508344314225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12577417989155344459085633 9433063491866508344314225)
                ·
                  refine ⟨7074797618899881258235669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9433063491866508344314225 7074797618899881258235669)
                  ·
                    refine ⟨331631138385931933979797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7074797618899881258235669 331631138385931933979797)
                    ·
                      rfl

theorem cell22_968774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_968774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968774 prefixEnd_968774 := by exact prefixLift 968774
  have htrace : WordTrace (prefixWord ++ tailWord_968774) baseStart_968774 baseEnd_968774 := by
    simpa [prefixWord, tailWord_968774, baseEnd_968774] using wordTrace_append hprefix tailTrace_968774
  have hstable : (prefixWord ++ tailWord_968774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968774).length < 2 ^ (prefixWord ++ tailWord_968774).sum := by decide
  have hdescent : baseEnd_968774 < baseStart_968774 := by decide
  rcases family_descends (prefixWord ++ tailWord_968774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_968817 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 6]
def baseStart_968817 : Nat := 118140960795 + 968817 * 2 ^ 59
def prefixEnd_968817 : Nat := 4983230072969 + 3 ^ 40 * 968817 * 2
def baseEnd_968817 : Nat := 110548619388231385051555

theorem tailTrace_968817 : CollatzResearch.WordTrace tailWord_968817 prefixEnd_968817 110548619388231385051555 := by
  unfold tailWord_968817
  simp only [CollatzResearch.WordTrace]
  refine ⟨35335658931148944615704705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23557105954099296410469803 35335658931148944615704705)
  ·
    refine ⟨26501744198361708461778529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35335658931148944615704705 26501744198361708461778529)
    ·
      refine ⟨19876308148771281346333897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26501744198361708461778529 19876308148771281346333897)
      ·
        refine ⟨14907231111578461009750423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19876308148771281346333897 14907231111578461009750423)
        ·
          refine ⟨22360846667367691514625635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14907231111578461009750423 22360846667367691514625635)
          ·
            refine ⟨33541270001051537271938453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22360846667367691514625635 33541270001051537271938453)
            ·
              refine ⟨1572247031299290809622115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33541270001051537271938453 1572247031299290809622115)
              ·
                refine ⟨2358370546948936214433173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572247031299290809622115 2358370546948936214433173)
                ·
                  refine ⟨110548619388231385051555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2358370546948936214433173 110548619388231385051555)
                  ·
                    rfl

theorem cell22_968817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_968817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_968817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_968817 prefixEnd_968817 := by exact prefixLift 968817
  have htrace : WordTrace (prefixWord ++ tailWord_968817) baseStart_968817 baseEnd_968817 := by
    simpa [prefixWord, tailWord_968817, baseEnd_968817] using wordTrace_append hprefix tailTrace_968817
  have hstable : (prefixWord ++ tailWord_968817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_968817).length < 2 ^ (prefixWord ++ tailWord_968817).sum := by decide
  have hdescent : baseEnd_968817 < baseStart_968817 := by decide
  rcases family_descends (prefixWord ++ tailWord_968817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
