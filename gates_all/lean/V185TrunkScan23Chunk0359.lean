import V185TrunkScan23Chunk0358

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2123460 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_2123460 : Nat := 118140960795 + 2123460 * 2 ^ 59
def prefixEnd_2123460 : Nat := 4983230072969 + 3 ^ 40 * 2123460 * 2
def baseEnd_2123460 : Nat := 363451876865455728894797

theorem tailTrace_2123460 : CollatzResearch.WordTrace tailWord_2123460 prefixEnd_2123460 363451876865455728894797 := by
  unfold tailWord_2123460
  simp only [CollatzResearch.WordTrace]
  refine ⟨38724474443537276470211917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51632632591383035293615889 38724474443537276470211917)
  ·
    refine ⟨14521677916326478676329469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38724474443537276470211917 14521677916326478676329469)
    ·
      refine ⟨5445629218622429503623551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14521677916326478676329469 5445629218622429503623551)
      ·
        refine ⟨8168443827933644255435327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5445629218622429503623551 8168443827933644255435327)
        ·
          refine ⟨12252665741900466383152991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8168443827933644255435327 12252665741900466383152991)
          ·
            refine ⟨18378998612850699574729487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12252665741900466383152991 18378998612850699574729487)
            ·
              refine ⟨27568497919276049362094231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18378998612850699574729487 27568497919276049362094231)
              ·
                refine ⟨41352746878914074043141347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27568497919276049362094231 41352746878914074043141347)
                ·
                  refine ⟨62029120318371111064712021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41352746878914074043141347 62029120318371111064712021)
                  ·
                    refine ⟨363451876865455728894797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 62029120318371111064712021 363451876865455728894797)
                    ·
                      rfl

theorem cell23_2123460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_2123460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123460 prefixEnd_2123460 := by exact prefixLift 2123460
  have htrace : WordTrace (prefixWord ++ tailWord_2123460) baseStart_2123460 baseEnd_2123460 := by
    simpa [prefixWord, tailWord_2123460, baseEnd_2123460] using wordTrace_append hprefix tailTrace_2123460
  have hstable : (prefixWord ++ tailWord_2123460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123460).length < 2 ^ (prefixWord ++ tailWord_2123460).sum := by decide
  have hdescent : baseEnd_2123460 < baseStart_2123460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123474 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_2123474 : Nat := 118140960795 + 2123474 * 2 ^ 59
def prefixEnd_2123474 : Nat := 4983230072969 + 3 ^ 40 * 2123474 * 2
def baseEnd_2123474 : Nat := 1090362819325530131909327

theorem tailTrace_2123474 : CollatzResearch.WordTrace tailWord_2123474 prefixEnd_2123474 1090362819325530131909327 := by
  unfold tailWord_2123474
  simp only [CollatzResearch.WordTrace]
  refine ⟨19362364877255958332858369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51632973006015888887622317 19362364877255958332858369)
  ·
    refine ⟨14521773657941968749643777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19362364877255958332858369 14521773657941968749643777)
    ·
      refine ⟨10891330243456476562232833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14521773657941968749643777 10891330243456476562232833)
      ·
        refine ⟨8168497682592357421674625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10891330243456476562232833 8168497682592357421674625)
        ·
          refine ⟨6126373261944268066255969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8168497682592357421674625 6126373261944268066255969)
          ·
            refine ⟨4594779946458201049691977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6126373261944268066255969 4594779946458201049691977)
            ·
              refine ⟨3446084959843650787268983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4594779946458201049691977 3446084959843650787268983)
              ·
                refine ⟨5169127439765476180903475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3446084959843650787268983 5169127439765476180903475)
                ·
                  refine ⟨7753691159648214271355213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5169127439765476180903475 7753691159648214271355213)
                  ·
                    refine ⟨2907634184868080351758205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7753691159648214271355213 2907634184868080351758205)
                    ·
                      refine ⟨1090362819325530131909327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2907634184868080351758205 1090362819325530131909327)
                      ·
                        rfl

theorem cell23_2123474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_2123474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123474 prefixEnd_2123474 := by exact prefixLift 2123474
  have htrace : WordTrace (prefixWord ++ tailWord_2123474) baseStart_2123474 baseEnd_2123474 := by
    simpa [prefixWord, tailWord_2123474, baseEnd_2123474] using wordTrace_append hprefix tailTrace_2123474
  have hstable : (prefixWord ++ tailWord_2123474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123474).length < 2 ^ (prefixWord ++ tailWord_2123474).sum := by decide
  have hdescent : baseEnd_2123474 < baseStart_2123474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123480 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2123480 : Nat := 118140960795 + 2123480 * 2 ^ 59
def prefixEnd_2123480 : Nat := 4983230072969 + 3 ^ 40 * 2123480 * 2
def baseEnd_2123480 : Nat := 1090365900209457108434299

theorem tailTrace_2123480 : CollatzResearch.WordTrace tailWord_2123480 prefixEnd_2123480 1090365900209457108434299 := by
  unfold tailWord_2123480
  simp only [CollatzResearch.WordTrace]
  refine ⟨38724839173501048178075947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51633118898001397570767929 38724839173501048178075947)
  ·
    refine ⟨58087258760251572267113921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38724839173501048178075947 58087258760251572267113921)
    ·
      refine ⟨43565444070188679200335441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58087258760251572267113921 43565444070188679200335441)
      ·
        refine ⟨32674083052641509400251581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43565444070188679200335441 32674083052641509400251581)
        ·
          refine ⟨12252781144740566025094343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32674083052641509400251581 12252781144740566025094343)
          ·
            refine ⟨18379171717110849037641515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12252781144740566025094343 18379171717110849037641515)
            ·
              refine ⟨27568757575666273556462273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18379171717110849037641515 27568757575666273556462273)
              ·
                refine ⟨20676568181749705167346705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27568757575666273556462273 20676568181749705167346705)
                ·
                  refine ⟨15507426136312278875510029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20676568181749705167346705 15507426136312278875510029)
                  ·
                    refine ⟨5815284801117104578316261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15507426136312278875510029 5815284801117104578316261)
                    ·
                      refine ⟨1090365900209457108434299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5815284801117104578316261 1090365900209457108434299)
                      ·
                        rfl

theorem cell23_2123480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2123480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123480 prefixEnd_2123480 := by exact prefixLift 2123480
  have htrace : WordTrace (prefixWord ++ tailWord_2123480) baseStart_2123480 baseEnd_2123480 := by
    simpa [prefixWord, tailWord_2123480, baseEnd_2123480] using wordTrace_append hprefix tailTrace_2123480
  have hstable : (prefixWord ++ tailWord_2123480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123480).length < 2 ^ (prefixWord ++ tailWord_2123480).sum := by decide
  have hdescent : baseEnd_2123480 < baseStart_2123480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123495 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2123495 : Nat := 118140960795 + 2123495 * 2 ^ 59
def prefixEnd_2123495 : Nat := 4983230072969 + 3 ^ 40 * 2123495 * 2
def baseEnd_2123495 : Nat := 1090373602419274549746731

theorem tailTrace_2123495 : CollatzResearch.WordTrace tailWord_2123495 prefixEnd_2123495 1090373602419274549746731 := by
  unfold tailWord_2123495
  simp only [CollatzResearch.WordTrace]
  refine ⟨77450225441947753917947939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51633483627965169278631959 77450225441947753917947939)
  ·
    refine ⟨116175338162921630876921909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77450225441947753917947939 116175338162921630876921909)
    ·
      refine ⟨10891437952773902894711429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116175338162921630876921909 10891437952773902894711429)
      ·
        refine ⟨2042144616145106792758393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10891437952773902894711429 2042144616145106792758393)
        ·
          refine ⟨1531608462108830094568795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2042144616145106792758393 1531608462108830094568795)
          ·
            refine ⟨2297412693163245141853193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531608462108830094568795 2297412693163245141853193)
            ·
              refine ⟨1723059519872433856389895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2297412693163245141853193 1723059519872433856389895)
              ·
                refine ⟨2584589279808650784584843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723059519872433856389895 2584589279808650784584843)
                ·
                  refine ⟨3876883919712976176877265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584589279808650784584843 3876883919712976176877265)
                  ·
                    refine ⟨2907662939784732132657949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3876883919712976176877265 2907662939784732132657949)
                    ·
                      refine ⟨1090373602419274549746731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2907662939784732132657949 1090373602419274549746731)
                      ·
                        rfl

theorem cell23_2123495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2123495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123495 prefixEnd_2123495 := by exact prefixLift 2123495
  have htrace : WordTrace (prefixWord ++ tailWord_2123495) baseStart_2123495 baseEnd_2123495 := by
    simpa [prefixWord, tailWord_2123495, baseEnd_2123495] using wordTrace_append hprefix tailTrace_2123495
  have hstable : (prefixWord ++ tailWord_2123495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123495).length < 2 ^ (prefixWord ++ tailWord_2123495).sum := by decide
  have hdescent : baseEnd_2123495 < baseStart_2123495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123500 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_2123500 : Nat := 118140960795 + 2123500 * 2 ^ 59
def prefixEnd_2123500 : Nat := 4983230072969 + 3 ^ 40 * 2123500 * 2
def baseEnd_2123500 : Nat := 1090376169822547030184207

theorem tailTrace_2123500 : CollatzResearch.WordTrace tailWord_2123500 prefixEnd_2123500 1090376169822547030184207 := by
  unfold tailWord_2123500
  simp only [CollatzResearch.WordTrace]
  refine ⟨38725203903464819885939977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51633605204619759847919969 38725203903464819885939977)
  ·
    refine ⟨29043902927598614914454983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38725203903464819885939977 29043902927598614914454983)
    ·
      refine ⟨43565854391397922371682475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29043902927598614914454983 43565854391397922371682475)
      ·
        refine ⟨65348781587096883557523713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43565854391397922371682475 65348781587096883557523713)
        ·
          refine ⟨49011586190322662668142785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65348781587096883557523713 49011586190322662668142785)
          ·
            refine ⟨36758689642741997001107089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49011586190322662668142785 36758689642741997001107089)
            ·
              refine ⟨27569017232056497750830317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36758689642741997001107089 27569017232056497750830317)
              ·
                refine ⟨10338381462021186656561369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27569017232056497750830317 10338381462021186656561369)
                ·
                  refine ⟨7753786096515889992421027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10338381462021186656561369 7753786096515889992421027)
                  ·
                    refine ⟨11630679144773834988631541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7753786096515889992421027 11630679144773834988631541)
                    ·
                      refine ⟨1090376169822547030184207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11630679144773834988631541 1090376169822547030184207)
                      ·
                        rfl

theorem cell23_2123500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_2123500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123500 prefixEnd_2123500 := by exact prefixLift 2123500
  have htrace : WordTrace (prefixWord ++ tailWord_2123500) baseStart_2123500 baseEnd_2123500 := by
    simpa [prefixWord, tailWord_2123500, baseEnd_2123500] using wordTrace_append hprefix tailTrace_2123500
  have hstable : (prefixWord ++ tailWord_2123500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123500).length < 2 ^ (prefixWord ++ tailWord_2123500).sum := by decide
  have hdescent : baseEnd_2123500 < baseStart_2123500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123501 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_2123501 : Nat := 118140960795 + 2123501 * 2 ^ 59
def prefixEnd_2123501 : Nat := 4983230072969 + 3 ^ 40 * 2123501 * 2
def baseEnd_2123501 : Nat := 1090376683303201526271703

theorem tailTrace_2123501 : CollatzResearch.WordTrace tailWord_2123501 prefixEnd_2123501 1090376683303201526271703 := by
  unfold tailWord_2123501
  simp only [CollatzResearch.WordTrace]
  refine ⟨77450444279926016942666357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51633629519950677961777571 77450444279926016942666357)
  ·
    refine ⟨7260979151243064088374971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77450444279926016942666357 7260979151243064088374971)
    ·
      refine ⟨10891468726864596132562457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7260979151243064088374971 10891468726864596132562457)
      ·
        refine ⟨8168601545148447099421843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10891468726864596132562457 8168601545148447099421843)
        ·
          refine ⟨12252902317722670649132765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8168601545148447099421843 12252902317722670649132765)
          ·
            refine ⟨4594838369146001493424787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12252902317722670649132765 4594838369146001493424787)
            ·
              refine ⟨6892257553719002240137181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594838369146001493424787 6892257553719002240137181)
              ·
                refine ⟨2584596582644625840051443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6892257553719002240137181 2584596582644625840051443)
                ·
                  refine ⟨3876894873966938760077165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584596582644625840051443 3876894873966938760077165)
                  ·
                    refine ⟨1453835577737602035028937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3876894873966938760077165 1453835577737602035028937)
                    ·
                      refine ⟨1090376683303201526271703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1453835577737602035028937 1090376683303201526271703)
                      ·
                        rfl

theorem cell23_2123501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_2123501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123501 prefixEnd_2123501 := by exact prefixLift 2123501
  have htrace : WordTrace (prefixWord ++ tailWord_2123501) baseStart_2123501 baseEnd_2123501 := by
    simpa [prefixWord, tailWord_2123501, baseEnd_2123501] using wordTrace_append hprefix tailTrace_2123501
  have hstable : (prefixWord ++ tailWord_2123501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123501).length < 2 ^ (prefixWord ++ tailWord_2123501).sum := by decide
  have hdescent : baseEnd_2123501 < baseStart_2123501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123508 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2123508 : Nat := 118140960795 + 2123508 * 2 ^ 59
def prefixEnd_2123508 : Nat := 4983230072969 + 3 ^ 40 * 2123508 * 2
def baseEnd_2123508 : Nat := 1090380277667782998884171

theorem tailTrace_2123508 : CollatzResearch.WordTrace tailWord_2123508 prefixEnd_2123508 1090380277667782998884171 := by
  unfold tailWord_2123508
  simp only [CollatzResearch.WordTrace]
  refine ⟨38725349795450328569085589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51633799727267104758780785 38725349795450328569085589)
  ·
    refine ⟨1815250771661734151675887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38725349795450328569085589 1815250771661734151675887)
    ·
      refine ⟨2722876157492601227513831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1815250771661734151675887 2722876157492601227513831)
      ·
        refine ⟨4084314236238901841270747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2722876157492601227513831 4084314236238901841270747)
        ·
          refine ⟨6126471354358352761906121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4084314236238901841270747 6126471354358352761906121)
          ·
            refine ⟨4594853515768764571429591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6126471354358352761906121 4594853515768764571429591)
            ·
              refine ⟨6892280273653146857144387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4594853515768764571429591 6892280273653146857144387)
              ·
                refine ⟨10338420410479720285716581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6892280273653146857144387 10338420410479720285716581)
                ·
                  refine ⟨1938453826964947553571859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10338420410479720285716581 1938453826964947553571859)
                  ·
                    refine ⟨2907680740447421330357789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1938453826964947553571859 2907680740447421330357789)
                    ·
                      refine ⟨1090380277667782998884171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2907680740447421330357789 1090380277667782998884171)
                      ·
                        rfl

theorem cell23_2123508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2123508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123508 prefixEnd_2123508 := by exact prefixLift 2123508
  have htrace : WordTrace (prefixWord ++ tailWord_2123508) baseStart_2123508 baseEnd_2123508 := by
    simpa [prefixWord, tailWord_2123508, baseEnd_2123508] using wordTrace_append hprefix tailTrace_2123508
  have hstable : (prefixWord ++ tailWord_2123508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123508).length < 2 ^ (prefixWord ++ tailWord_2123508).sum := by decide
  have hdescent : baseEnd_2123508 < baseStart_2123508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123571 : List Nat := [1, 1, 1, 2, 7, 1, 3, 2, 5]
def baseStart_2123571 : Nat := 118140960795 + 2123571 * 2 ^ 59
def prefixEnd_2123571 : Nat := 4983230072969 + 3 ^ 40 * 2123571 * 2
def baseEnd_2123571 : Nat := 121156958549890694710709

theorem tailTrace_2123571 : CollatzResearch.WordTrace tailWord_2123571 prefixEnd_2123571 121156958549890694710709 := by
  unfold tailWord_2123571
  simp only [CollatzResearch.WordTrace]
  refine ⟨77452997389672418897714567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51635331593114945931809711 77452997389672418897714567)
  ·
    refine ⟨116179496084508628346571851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77452997389672418897714567 116179496084508628346571851)
    ·
      refine ⟨174269244126762942519857777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116179496084508628346571851 174269244126762942519857777)
      ·
        refine ⟨130701933095072206889893333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174269244126762942519857777 130701933095072206889893333)
        ·
          refine ⟨3063326556915754848981875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 130701933095072206889893333 3063326556915754848981875)
          ·
            refine ⟨4594989835373632273472813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063326556915754848981875 4594989835373632273472813)
            ·
              refine ⟨1723121188265112102552305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4594989835373632273472813 1723121188265112102552305)
              ·
                refine ⟨1292340891198834076914229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1723121188265112102552305 1292340891198834076914229)
                ·
                  refine ⟨121156958549890694710709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1292340891198834076914229 121156958549890694710709)
                  ·
                    rfl

theorem cell23_2123571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 5].length) (baseStart_2123571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123571 prefixEnd_2123571 := by exact prefixLift 2123571
  have htrace : WordTrace (prefixWord ++ tailWord_2123571) baseStart_2123571 baseEnd_2123571 := by
    simpa [prefixWord, tailWord_2123571, baseEnd_2123571] using wordTrace_append hprefix tailTrace_2123571
  have hstable : (prefixWord ++ tailWord_2123571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123571).length < 2 ^ (prefixWord ++ tailWord_2123571).sum := by decide
  have hdescent : baseEnd_2123571 < baseStart_2123571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123600 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_2123600 : Nat := 118140960795 + 2123600 * 2 ^ 59
def prefixEnd_2123600 : Nat := 4983230072969 + 3 ^ 40 * 2123600 * 2
def baseEnd_2123600 : Nat := 1090427517887996638933747

theorem tailTrace_2123600 : CollatzResearch.WordTrace tailWord_2123600 prefixEnd_2123600 1090427517887996638933747 := by
  unfold tailWord_2123600
  simp only [CollatzResearch.WordTrace]
  refine ⟨38727027553283678425260127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51636036737711571233680169 38727027553283678425260127)
  ·
    refine ⟨58090541329925517637890191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38727027553283678425260127 58090541329925517637890191)
    ·
      refine ⟨87135811994888276456835287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58090541329925517637890191 87135811994888276456835287)
      ·
        refine ⟨130703717992332414685252931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87135811994888276456835287 130703717992332414685252931)
        ·
          refine ⟨196055576988498622027879397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130703717992332414685252931 196055576988498622027879397)
          ·
            refine ⟨36760420685343491630227387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196055576988498622027879397 36760420685343491630227387)
            ·
              refine ⟨55140631028015237445341081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36760420685343491630227387 55140631028015237445341081)
              ·
                refine ⟨41355473271011428084005811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55140631028015237445341081 41355473271011428084005811)
                ·
                  refine ⟨62033209906517142126008717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41355473271011428084005811 62033209906517142126008717)
                  ·
                    refine ⟨23262453714943928297253269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62033209906517142126008717 23262453714943928297253269)
                    ·
                      refine ⟨1090427517887996638933747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23262453714943928297253269 1090427517887996638933747)
                      ·
                        rfl

theorem cell23_2123600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_2123600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123600 prefixEnd_2123600 := by exact prefixLift 2123600
  have htrace : WordTrace (prefixWord ++ tailWord_2123600) baseStart_2123600 baseEnd_2123600 := by
    simpa [prefixWord, tailWord_2123600, baseEnd_2123600] using wordTrace_append hprefix tailTrace_2123600
  have hstable : (prefixWord ++ tailWord_2123600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123600).length < 2 ^ (prefixWord ++ tailWord_2123600).sum := by decide
  have hdescent : baseEnd_2123600 < baseStart_2123600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123604 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_2123604 : Nat := 118140960795 + 2123604 * 2 ^ 59
def prefixEnd_2123604 : Nat := 4983230072969 + 3 ^ 40 * 2123604 * 2
def baseEnd_2123604 : Nat := 1090429571810614623283729

theorem tailTrace_2123604 : CollatzResearch.WordTrace tailWord_2123604 prefixEnd_2123604 1090429571810614623283729 := by
  unfold tailWord_2123604
  simp only [CollatzResearch.WordTrace]
  refine ⟨38727100499276432766832933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51636133999035243689110577 38727100499276432766832933)
  ·
    refine ⟨7261331343614331143781175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38727100499276432766832933 7261331343614331143781175)
    ·
      refine ⟨10891997015421496715671763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7261331343614331143781175 10891997015421496715671763)
      ·
        refine ⟨16337995523132245073507645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10891997015421496715671763 16337995523132245073507645)
        ·
          refine ⟨6126748321174591902565367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16337995523132245073507645 6126748321174591902565367)
          ·
            refine ⟨9190122481761887853848051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6126748321174591902565367 9190122481761887853848051)
            ·
              refine ⟨13785183722642831780772077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9190122481761887853848051 13785183722642831780772077)
              ·
                refine ⟨5169443895991061917789529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13785183722642831780772077 5169443895991061917789529)
                ·
                  refine ⟨3877082921993296438342147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5169443895991061917789529 3877082921993296438342147)
                  ·
                    refine ⟨5815624382989944657513221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3877082921993296438342147 5815624382989944657513221)
                    ·
                      refine ⟨1090429571810614623283729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5815624382989944657513221 1090429571810614623283729)
                      ·
                        rfl

theorem cell23_2123604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_2123604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123604 prefixEnd_2123604 := by exact prefixLift 2123604
  have htrace : WordTrace (prefixWord ++ tailWord_2123604) baseStart_2123604 baseEnd_2123604 := by
    simpa [prefixWord, tailWord_2123604, baseEnd_2123604] using wordTrace_append hprefix tailTrace_2123604
  have hstable : (prefixWord ++ tailWord_2123604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123604).length < 2 ^ (prefixWord ++ tailWord_2123604).sum := by decide
  have hdescent : baseEnd_2123604 < baseStart_2123604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123624 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2123624 : Nat := 118140960795 + 2123624 * 2 ^ 59
def prefixEnd_2123624 : Nat := 4983230072969 + 3 ^ 40 * 2123624 * 2
def baseEnd_2123624 : Nat := 1090439841423704545033637

theorem tailTrace_2123624 : CollatzResearch.WordTrace tailWord_2123624 prefixEnd_2123624 1090439841423704545033637 := by
  unfold tailWord_2123624
  simp only [CollatzResearch.WordTrace]
  refine ⟨38727465229240204474696963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51636620305653605966262617 38727465229240204474696963)
  ·
    refine ⟨58091197843860306712045445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38727465229240204474696963 58091197843860306712045445)
    ·
      refine ⟨10892099595723807508508521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58091197843860306712045445 10892099595723807508508521)
      ·
        refine ⟨8169074696792855631381391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10892099595723807508508521 8169074696792855631381391)
        ·
          refine ⟨12253612045189283447072087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8169074696792855631381391 12253612045189283447072087)
          ·
            refine ⟨18380418067783925170608131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12253612045189283447072087 18380418067783925170608131)
            ·
              refine ⟨27570627101675887755912197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18380418067783925170608131 27570627101675887755912197)
              ·
                refine ⟨5169492581564228954233537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27570627101675887755912197 5169492581564228954233537)
                ·
                  refine ⟨3877119436173171715675153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5169492581564228954233537 3877119436173171715675153)
                  ·
                    refine ⟨2907839577129878786756365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3877119436173171715675153 2907839577129878786756365)
                    ·
                      refine ⟨1090439841423704545033637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2907839577129878786756365 1090439841423704545033637)
                      ·
                        rfl

theorem cell23_2123624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2123624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123624 prefixEnd_2123624 := by exact prefixLift 2123624
  have htrace : WordTrace (prefixWord ++ tailWord_2123624) baseStart_2123624 baseEnd_2123624 := by
    simpa [prefixWord, tailWord_2123624, baseEnd_2123624] using wordTrace_append hprefix tailTrace_2123624
  have hstable : (prefixWord ++ tailWord_2123624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123624).length < 2 ^ (prefixWord ++ tailWord_2123624).sum := by decide
  have hdescent : baseEnd_2123624 < baseStart_2123624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123638 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2123638 : Nat := 118140960795 + 2123638 * 2 ^ 59
def prefixEnd_2123638 : Nat := 4983230072969 + 3 ^ 40 * 2123638 * 2
def baseEnd_2123638 : Nat := 1090447030152867490258573

theorem tailTrace_2123638 : CollatzResearch.WordTrace tailWord_2123638 prefixEnd_2123638 1090447030152867490258573 := by
  unfold tailWord_2123638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4840965067526855583775223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51636960720286459560269045 4840965067526855583775223)
  ·
    refine ⟨7261447601290283375662835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4840965067526855583775223 7261447601290283375662835)
    ·
      refine ⟨10892171401935425063494253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7261447601290283375662835 10892171401935425063494253)
      ·
        refine ⟨4084564275725784398810345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10892171401935425063494253 4084564275725784398810345)
        ·
          refine ⟨3063423206794338299107759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4084564275725784398810345 3063423206794338299107759)
          ·
            refine ⟨4595134810191507448661639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063423206794338299107759 4595134810191507448661639)
            ·
              refine ⟨6892702215287261172992459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4595134810191507448661639 6892702215287261172992459)
              ·
                refine ⟨10339053322930891759488689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6892702215287261172992459 10339053322930891759488689)
                ·
                  refine ⟨7754289992198168819616517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10339053322930891759488689 7754289992198168819616517)
                  ·
                    refine ⟨1453929373537156653678097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7754289992198168819616517 1453929373537156653678097)
                    ·
                      refine ⟨1090447030152867490258573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1453929373537156653678097 1090447030152867490258573)
                      ·
                        rfl

theorem cell23_2123638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2123638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123638 prefixEnd_2123638 := by exact prefixLift 2123638
  have htrace : WordTrace (prefixWord ++ tailWord_2123638) baseStart_2123638 baseEnd_2123638 := by
    simpa [prefixWord, tailWord_2123638, baseEnd_2123638] using wordTrace_append hprefix tailTrace_2123638
  have hstable : (prefixWord ++ tailWord_2123638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123638).length < 2 ^ (prefixWord ++ tailWord_2123638).sum := by decide
  have hdescent : baseEnd_2123638 < baseStart_2123638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123657 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 3, 5]
def baseStart_2123657 : Nat := 118140960795 + 2123657 * 2 ^ 59
def prefixEnd_2123657 : Nat := 4983230072969 + 3 ^ 40 * 2123657 * 2
def baseEnd_2123657 : Nat := 363485595428434305306995

theorem tailTrace_2123657 : CollatzResearch.WordTrace tailWord_2123657 prefixEnd_2123657 363485595428434305306995 := by
  unfold tailWord_2123657
  simp only [CollatzResearch.WordTrace]
  refine ⟨77456134067360855585345225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51637422711573903723563483 77456134067360855585345225)
  ·
    refine ⟨58092100550520641689008919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77456134067360855585345225 58092100550520641689008919)
    ·
      refine ⟨87138150825780962533513379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58092100550520641689008919 87138150825780962533513379)
      ·
        refine ⟨130707226238671443800270069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87138150825780962533513379 130707226238671443800270069)
        ·
          refine ⟨12253802459875447856275319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130707226238671443800270069 12253802459875447856275319)
          ·
            refine ⟨18380703689813171784412979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12253802459875447856275319 18380703689813171784412979)
            ·
              refine ⟨27571055534719757676619469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18380703689813171784412979 27571055534719757676619469)
              ·
                refine ⟨10339145825519909128732301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27571055534719757676619469 10339145825519909128732301)
                ·
                  refine ⟨3877179684569965923274613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10339145825519909128732301 3877179684569965923274613)
                  ·
                    refine ⟨363485595428434305306995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3877179684569965923274613 363485595428434305306995)
                    ·
                      rfl

theorem cell23_2123657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_2123657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123657 prefixEnd_2123657 := by exact prefixLift 2123657
  have htrace : WordTrace (prefixWord ++ tailWord_2123657) baseStart_2123657 baseEnd_2123657 := by
    simpa [prefixWord, tailWord_2123657, baseEnd_2123657] using wordTrace_append hprefix tailTrace_2123657
  have hstable : (prefixWord ++ tailWord_2123657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123657).length < 2 ^ (prefixWord ++ tailWord_2123657).sum := by decide
  have hdescent : baseEnd_2123657 < baseStart_2123657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123658 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2123658 : Nat := 118140960795 + 2123658 * 2 ^ 59
def prefixEnd_2123658 : Nat := 4983230072969 + 3 ^ 40 * 2123658 * 2
def baseEnd_2123658 : Nat := 1090457299765957412008481

theorem tailTrace_2123658 : CollatzResearch.WordTrace tailWord_2123658 prefixEnd_2123658 1090457299765957412008481 := by
  unfold tailWord_2123658
  simp only [CollatzResearch.WordTrace]
  refine ⟨19364042635089308189032907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51637447026904821837421085 19364042635089308189032907)
  ·
    refine ⟨29046063952633962283549361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19364042635089308189032907 29046063952633962283549361)
    ·
      refine ⟨21784547964475471712662021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29046063952633962283549361 21784547964475471712662021)
      ·
        refine ⟨4084602743339150946124129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21784547964475471712662021 4084602743339150946124129)
        ·
          refine ⟨3063452057504363209593097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4084602743339150946124129 3063452057504363209593097)
          ·
            refine ⟨2297589043128272407194823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3063452057504363209593097 2297589043128272407194823)
            ·
              refine ⟨3446383564692408610792235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297589043128272407194823 3446383564692408610792235)
              ·
                refine ⟨5169575347038612916188353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3446383564692408610792235 5169575347038612916188353)
                ·
                  refine ⟨3877181510278959687141265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5169575347038612916188353 3877181510278959687141265)
                  ·
                    refine ⟨2907886132709219765355949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3877181510278959687141265 2907886132709219765355949)
                    ·
                      refine ⟨1090457299765957412008481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2907886132709219765355949 1090457299765957412008481)
                      ·
                        rfl

theorem cell23_2123658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2123658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123658 prefixEnd_2123658 := by exact prefixLift 2123658
  have htrace : WordTrace (prefixWord ++ tailWord_2123658) baseStart_2123658 baseEnd_2123658 := by
    simpa [prefixWord, tailWord_2123658, baseEnd_2123658] using wordTrace_append hprefix tailTrace_2123658
  have hstable : (prefixWord ++ tailWord_2123658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123658).length < 2 ^ (prefixWord ++ tailWord_2123658).sum := by decide
  have hdescent : baseEnd_2123658 < baseStart_2123658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123708 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 1, 5]
def baseStart_2123708 : Nat := 118140960795 + 2123708 * 2 ^ 59
def prefixEnd_2123708 : Nat := 4983230072969 + 3 ^ 40 * 2123708 * 2
def baseEnd_2123708 : Nat := 363494324599560738794417

theorem tailTrace_2123708 : CollatzResearch.WordTrace tailWord_2123708 prefixEnd_2123708 363494324599560738794417 := by
  unfold tailWord_2123708
  simp only [CollatzResearch.WordTrace]
  refine ⟨38728997095088045647725889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51638662793450727530301185 38728997095088045647725889)
  ·
    refine ⟨29046747821316034235794417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38728997095088045647725889 29046747821316034235794417)
    ·
      refine ⟨21785060865987025676845813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29046747821316034235794417 21785060865987025676845813)
      ·
        refine ⟨2042349456186283657204295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21785060865987025676845813 2042349456186283657204295)
        ·
          refine ⟨3063524184279425485806443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2042349456186283657204295 3063524184279425485806443)
          ·
            refine ⟨4595286276419138228709665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3063524184279425485806443 4595286276419138228709665)
            ·
              refine ⟨3446464707314353671532249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4595286276419138228709665 3446464707314353671532249)
              ·
                refine ⟨2584848530485765253649187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3446464707314353671532249 2584848530485765253649187)
                ·
                  refine ⟨3877272795728647880473781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2584848530485765253649187 3877272795728647880473781)
                  ·
                    refine ⟨363494324599560738794417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3877272795728647880473781 363494324599560738794417)
                    ·
                      rfl

theorem cell23_2123708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_2123708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123708 prefixEnd_2123708 := by exact prefixLift 2123708
  have htrace : WordTrace (prefixWord ++ tailWord_2123708) baseStart_2123708 baseEnd_2123708 := by
    simpa [prefixWord, tailWord_2123708, baseEnd_2123708] using wordTrace_append hprefix tailTrace_2123708
  have hstable : (prefixWord ++ tailWord_2123708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123708).length < 2 ^ (prefixWord ++ tailWord_2123708).sum := by decide
  have hdescent : baseEnd_2123708 < baseStart_2123708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123711 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 3, 2, 2]
def baseStart_2123711 : Nat := 118140960795 + 2123711 * 2 ^ 59
def prefixEnd_2123711 : Nat := 4983230072969 + 3 ^ 40 * 2123711 * 2
def baseEnd_2123711 : Nat := 1090484514240645704645737

theorem tailTrace_2123711 : CollatzResearch.WordTrace tailWord_2123711 prefixEnd_2123711 1090484514240645704645737 := by
  unfold tailWord_2123711
  simp only [CollatzResearch.WordTrace]
  refine ⟨77458103609165222807810987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51638735739443481871873991 77458103609165222807810987)
  ·
    refine ⟨116187155413747834211716481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77458103609165222807810987 116187155413747834211716481)
    ·
      refine ⟨87140366560310875658787361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116187155413747834211716481 87140366560310875658787361)
      ·
        refine ⟨65355274920233156744090521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87140366560310875658787361 65355274920233156744090521)
        ·
          refine ⟨49016456190174867558067891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65355274920233156744090521 49016456190174867558067891)
          ·
            refine ⟨73524684285262301337101837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49016456190174867558067891 73524684285262301337101837)
            ·
              refine ⟨27571756606973363001413189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73524684285262301337101837 27571756606973363001413189)
              ·
                refine ⟨5169704363807505562764973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27571756606973363001413189 5169704363807505562764973)
                ·
                  refine ⟨1938639136427814586036865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5169704363807505562764973 1938639136427814586036865)
                  ·
                    refine ⟨1453979352320860939527649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1938639136427814586036865 1453979352320860939527649)
                    ·
                      refine ⟨1090484514240645704645737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1453979352320860939527649 1090484514240645704645737)
                      ·
                        rfl

theorem cell23_2123711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 2, 2].length) (baseStart_2123711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123711 prefixEnd_2123711 := by exact prefixLift 2123711
  have htrace : WordTrace (prefixWord ++ tailWord_2123711) baseStart_2123711 baseEnd_2123711 := by
    simpa [prefixWord, tailWord_2123711, baseEnd_2123711] using wordTrace_append hprefix tailTrace_2123711
  have hstable : (prefixWord ++ tailWord_2123711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123711).length < 2 ^ (prefixWord ++ tailWord_2123711).sum := by decide
  have hdescent : baseEnd_2123711 < baseStart_2123711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123817 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_2123817 : Nat := 118140960795 + 2123817 * 2 ^ 59
def prefixEnd_2123817 : Nat := 4983230072969 + 3 ^ 40 * 2123817 * 2
def baseEnd_2123817 : Nat := 1090538943190022289920249

theorem tailTrace_2123817 : CollatzResearch.WordTrace tailWord_2123817 prefixEnd_2123817 1090538943190022289920249 := by
  unfold tailWord_2123817
  simp only [CollatzResearch.WordTrace]
  refine ⟨77461969746781202911169705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51641313164520801940779803 77461969746781202911169705)
  ·
    refine ⟨58096477310085902183377279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77461969746781202911169705 58096477310085902183377279)
    ·
      refine ⟨87144715965128853275065919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58096477310085902183377279 87144715965128853275065919)
      ·
        refine ⟨130717073947693279912598879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87144715965128853275065919 130717073947693279912598879)
        ·
          refine ⟨196075610921539919868898319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130717073947693279912598879 196075610921539919868898319)
          ·
            refine ⟨294113416382309879803347479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196075610921539919868898319 294113416382309879803347479)
            ·
              refine ⟨441170124573464819705021219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294113416382309879803347479 441170124573464819705021219)
              ·
                refine ⟨661755186860197229557531829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441170124573464819705021219 661755186860197229557531829)
                ·
                  refine ⟨62039548768143490271018609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 661755186860197229557531829 62039548768143490271018609)
                  ·
                    refine ⟨46529661576107617703263957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62039548768143490271018609 46529661576107617703263957)
                    ·
                      refine ⟨1090538943190022289920249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46529661576107617703263957 1090538943190022289920249)
                      ·
                        rfl

theorem cell23_2123817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_2123817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123817 prefixEnd_2123817 := by exact prefixLift 2123817
  have htrace : WordTrace (prefixWord ++ tailWord_2123817) baseStart_2123817 baseEnd_2123817 := by
    simpa [prefixWord, tailWord_2123817, baseEnd_2123817] using wordTrace_append hprefix tailTrace_2123817
  have hstable : (prefixWord ++ tailWord_2123817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123817).length < 2 ^ (prefixWord ++ tailWord_2123817).sum := by decide
  have hdescent : baseEnd_2123817 < baseStart_2123817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123818 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_2123818 : Nat := 118140960795 + 2123818 * 2 ^ 59
def prefixEnd_2123818 : Nat := 4983230072969 + 3 ^ 40 * 2123818 * 2
def baseEnd_2123818 : Nat := 1090539456670676786007745

theorem tailTrace_2123818 : CollatzResearch.WordTrace tailWord_2123818 prefixEnd_2123818 1090539456670676786007745 := by
  unfold tailWord_2123818
  simp only [CollatzResearch.WordTrace]
  refine ⟨19365501554944395020489027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51641337479851720054637405 19365501554944395020489027)
  ·
    refine ⟨29048252332416592530733541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19365501554944395020489027 29048252332416592530733541)
    ·
      refine ⟨5446547312328111099512539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29048252332416592530733541 5446547312328111099512539)
      ·
        refine ⟨8169820968492166649268809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5446547312328111099512539 8169820968492166649268809)
        ·
          refine ⟨6127365726369124986951607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8169820968492166649268809 6127365726369124986951607)
          ·
            refine ⟨9191048589553687480427411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6127365726369124986951607 9191048589553687480427411)
            ·
              refine ⟨13786572884330531220641117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9191048589553687480427411 13786572884330531220641117)
              ·
                refine ⟨5169964831623949207740419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13786572884330531220641117 5169964831623949207740419)
                ·
                  refine ⟨7754947247435923811610629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5169964831623949207740419 7754947247435923811610629)
                  ·
                    refine ⟨1454052608894235714676993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7754947247435923811610629 1454052608894235714676993)
                    ·
                      refine ⟨1090539456670676786007745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454052608894235714676993 1090539456670676786007745)
                      ·
                        rfl

theorem cell23_2123818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_2123818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123818 prefixEnd_2123818 := by exact prefixLift 2123818
  have htrace : WordTrace (prefixWord ++ tailWord_2123818) baseStart_2123818 baseEnd_2123818 := by
    simpa [prefixWord, tailWord_2123818, baseEnd_2123818] using wordTrace_append hprefix tailTrace_2123818
  have hstable : (prefixWord ++ tailWord_2123818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123818).length < 2 ^ (prefixWord ++ tailWord_2123818).sum := by decide
  have hdescent : baseEnd_2123818 < baseStart_2123818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123824 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 7]
def baseStart_2123824 : Nat := 118140960795 + 2123824 * 2 ^ 59
def prefixEnd_2123824 : Nat := 4983230072969 + 3 ^ 40 * 2123824 * 2
def baseEnd_2123824 : Nat := 121171393061622640281413

theorem tailTrace_2123824 : CollatzResearch.WordTrace tailWord_2123824 prefixEnd_2123824 121171393061622640281413 := by
  unfold tailWord_2123824
  simp only [CollatzResearch.WordTrace]
  refine ⟨38731112528877921553337263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51641483371837228737783017 38731112528877921553337263)
  ·
    refine ⟨58096668793316882330005895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38731112528877921553337263 58096668793316882330005895)
    ·
      refine ⟨87145003189975323495008843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58096668793316882330005895 87145003189975323495008843)
      ·
        refine ⟨130717504784962985242513265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87145003189975323495008843 130717504784962985242513265)
        ·
          refine ⟨98038128588722238931884949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130717504784962985242513265 98038128588722238931884949)
          ·
            refine ⟨4595537277596354949932107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98038128588722238931884949 4595537277596354949932107)
            ·
              refine ⟨6893305916394532424898161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4595537277596354949932107 6893305916394532424898161)
              ·
                refine ⟨5169979437295899318673621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6893305916394532424898161 5169979437295899318673621)
                ·
                  refine ⟨121171393061622640281413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5169979437295899318673621 121171393061622640281413)
                  ·
                    rfl

theorem cell23_2123824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 7].length) (baseStart_2123824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123824 prefixEnd_2123824 := by exact prefixLift 2123824
  have htrace : WordTrace (prefixWord ++ tailWord_2123824) baseStart_2123824 baseEnd_2123824 := by
    simpa [prefixWord, tailWord_2123824, baseEnd_2123824] using wordTrace_append hprefix tailTrace_2123824
  have hstable : (prefixWord ++ tailWord_2123824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123824).length < 2 ^ (prefixWord ++ tailWord_2123824).sum := by decide
  have hdescent : baseEnd_2123824 < baseStart_2123824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123834 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3]
def baseStart_2123834 : Nat := 118140960795 + 2123834 * 2 ^ 59
def prefixEnd_2123834 : Nat := 4983230072969 + 3 ^ 40 * 2123834 * 2
def baseEnd_2123834 : Nat := 1090547672361148723407671

theorem tailTrace_2123834 : CollatzResearch.WordTrace tailWord_2123834 prefixEnd_2123834 1090547672361148723407671 := by
  unfold tailWord_2123834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19365647446929903703634639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51641726525146409876359037 19365647446929903703634639)
  ·
    refine ⟨29048471170394855555451959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19365647446929903703634639 29048471170394855555451959)
    ·
      refine ⟨43572706755592283333177939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29048471170394855555451959 43572706755592283333177939)
      ·
        refine ⟨65359060133388424999766909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43572706755592283333177939 65359060133388424999766909)
        ·
          refine ⟨24509647550020659374912591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65359060133388424999766909 24509647550020659374912591)
          ·
            refine ⟨36764471325030989062368887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24509647550020659374912591 36764471325030989062368887)
            ·
              refine ⟨55146706987546483593553331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36764471325030989062368887 55146706987546483593553331)
              ·
                refine ⟨82720060481319725390329997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55146706987546483593553331 82720060481319725390329997)
                ·
                  refine ⟨31020022680494897021373749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82720060481319725390329997 31020022680494897021373749)
                  ·
                    refine ⟨2908127126296396595753789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31020022680494897021373749 2908127126296396595753789)
                    ·
                      refine ⟨1090547672361148723407671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2908127126296396595753789 1090547672361148723407671)
                      ·
                        rfl

theorem cell23_2123834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_2123834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123834 prefixEnd_2123834 := by exact prefixLift 2123834
  have htrace : WordTrace (prefixWord ++ tailWord_2123834) baseStart_2123834 baseEnd_2123834 := by
    simpa [prefixWord, tailWord_2123834, baseEnd_2123834] using wordTrace_append hprefix tailTrace_2123834
  have hstable : (prefixWord ++ tailWord_2123834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123834).length < 2 ^ (prefixWord ++ tailWord_2123834).sum := by decide
  have hdescent : baseEnd_2123834 < baseStart_2123834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123869 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_2123869 : Nat := 118140960795 + 2123869 * 2 ^ 59
def prefixEnd_2123869 : Nat := 4983230072969 + 3 ^ 40 * 2123869 * 2
def baseEnd_2123869 : Nat := 1090565644184056086470011

theorem tailTrace_2123869 : CollatzResearch.WordTrace tailWord_2123869 prefixEnd_2123869 1090565644184056086470011 := by
  unfold tailWord_2123869
  simp only [CollatzResearch.WordTrace]
  refine ⟨77463866342592815792062661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51642577561728543861375107 77463866342592815792062661)
  ·
    refine ⟨14524474939236152961011749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77463866342592815792062661 14524474939236152961011749)
    ·
      refine ⟨2723339051106778680189703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14524474939236152961011749 2723339051106778680189703)
      ·
        refine ⟨4085008576660168020284555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2723339051106778680189703 4085008576660168020284555)
        ·
          refine ⟨6127512864990252030426833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4085008576660168020284555 6127512864990252030426833)
          ·
            refine ⟨4595634648742689022820125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6127512864990252030426833 4595634648742689022820125)
            ·
              refine ⟨1723362993278508383557547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4595634648742689022820125 1723362993278508383557547)
              ·
                refine ⟨2585044489917762575336321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723362993278508383557547 2585044489917762575336321)
                ·
                  refine ⟨1938783367438321931502241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2585044489917762575336321 1938783367438321931502241)
                  ·
                    refine ⟨1454087525578741448626681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1938783367438321931502241 1454087525578741448626681)
                    ·
                      refine ⟨1090565644184056086470011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454087525578741448626681 1090565644184056086470011)
                      ·
                        rfl

theorem cell23_2123869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_2123869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123869 prefixEnd_2123869 := by exact prefixLift 2123869
  have htrace : WordTrace (prefixWord ++ tailWord_2123869) baseStart_2123869 baseEnd_2123869 := by
    simpa [prefixWord, tailWord_2123869, baseEnd_2123869] using wordTrace_append hprefix tailTrace_2123869
  have hstable : (prefixWord ++ tailWord_2123869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123869).length < 2 ^ (prefixWord ++ tailWord_2123869).sum := by decide
  have hdescent : baseEnd_2123869 < baseStart_2123869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123911 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_2123911 : Nat := 118140960795 + 2123911 * 2 ^ 59
def prefixEnd_2123911 : Nat := 4983230072969 + 3 ^ 40 * 2123911 * 2
def baseEnd_2123911 : Nat := 1090587210371544922144817

theorem tailTrace_2123911 : CollatzResearch.WordTrace tailWord_2123911 prefixEnd_2123911 1090587210371544922144817 := by
  unfold tailWord_2123911
  simp only [CollatzResearch.WordTrace]
  refine ⟨77465398208440656965091587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51643598805627104643394391 77465398208440656965091587)
  ·
    refine ⟨116198097312660985447637381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77465398208440656965091587 116198097312660985447637381)
    ·
      refine ⟨21787143246123934771432009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116198097312660985447637381 21787143246123934771432009)
      ·
        refine ⟨16340357434592951078574007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21787143246123934771432009 16340357434592951078574007)
        ·
          refine ⟨24510536151889426617861011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16340357434592951078574007 24510536151889426617861011)
          ·
            refine ⟨36765804227834139926791517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24510536151889426617861011 36765804227834139926791517)
            ·
              refine ⟨13787176585437802472546819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36765804227834139926791517 13787176585437802472546819)
              ·
                refine ⟨20680764878156703708820229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13787176585437802472546819 20680764878156703708820229)
                ·
                  refine ⟨3877643414654381945403793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20680764878156703708820229 3877643414654381945403793)
                  ·
                    refine ⟨2908232560990786459052845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3877643414654381945403793 2908232560990786459052845)
                    ·
                      refine ⟨1090587210371544922144817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2908232560990786459052845 1090587210371544922144817)
                      ·
                        rfl

theorem cell23_2123911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_2123911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123911 prefixEnd_2123911 := by exact prefixLift 2123911
  have htrace : WordTrace (prefixWord ++ tailWord_2123911) baseStart_2123911 baseEnd_2123911 := by
    simpa [prefixWord, tailWord_2123911, baseEnd_2123911] using wordTrace_append hprefix tailTrace_2123911
  have hstable : (prefixWord ++ tailWord_2123911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123911).length < 2 ^ (prefixWord ++ tailWord_2123911).sum := by decide
  have hdescent : baseEnd_2123911 < baseStart_2123911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2123991 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 6, 4]
def baseStart_2123991 : Nat := 118140960795 + 2123991 * 2 ^ 59
def prefixEnd_2123991 : Nat := 4983230072969 + 3 ^ 40 * 2123991 * 2
def baseEnd_2123991 : Nat := 363542762941301536381483

theorem tailTrace_2123991 : CollatzResearch.WordTrace tailWord_2123991 prefixEnd_2123991 363542762941301536381483 := by
  unfold tailWord_2123991
  simp only [CollatzResearch.WordTrace]
  refine ⟨77468316048150830628003827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51645544032100553752002551 77468316048150830628003827)
  ·
    refine ⟨116202474072226245942005741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77468316048150830628003827 116202474072226245942005741)
    ·
      refine ⟨43575927777084842228252153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116202474072226245942005741 43575927777084842228252153)
      ·
        refine ⟨32681945832813631671189115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43575927777084842228252153 32681945832813631671189115)
        ·
          refine ⟨49022918749220447506783673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32681945832813631671189115 49022918749220447506783673)
          ·
            refine ⟨36767189061915335630087755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49022918749220447506783673 36767189061915335630087755)
            ·
              refine ⟨55150783592873003445131633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36767189061915335630087755 55150783592873003445131633)
              ·
                refine ⟨41363087694654752583848725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55150783592873003445131633 41363087694654752583848725)
                ·
                  refine ⟨1938894735686941527367909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41363087694654752583848725 1938894735686941527367909)
                  ·
                    refine ⟨363542762941301536381483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1938894735686941527367909 363542762941301536381483)
                    ·
                      rfl

theorem cell23_2123991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_2123991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2123991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2123991 prefixEnd_2123991 := by exact prefixLift 2123991
  have htrace : WordTrace (prefixWord ++ tailWord_2123991) baseStart_2123991 baseEnd_2123991 := by
    simpa [prefixWord, tailWord_2123991, baseEnd_2123991] using wordTrace_append hprefix tailTrace_2123991
  have hstable : (prefixWord ++ tailWord_2123991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2123991).length < 2 ^ (prefixWord ++ tailWord_2123991).sum := by decide
  have hdescent : baseEnd_2123991 < baseStart_2123991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2123991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124011 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 4]
def baseStart_2124011 : Nat := 118140960795 + 2124011 * 2 ^ 59
def prefixEnd_2124011 : Nat := 4983230072969 + 3 ^ 40 * 2124011 * 2
def baseEnd_2124011 : Nat := 1090638558436994530894357

theorem tailTrace_2124011 : CollatzResearch.WordTrace tailWord_2124011 prefixEnd_2124011 1090638558436994530894357 := by
  unfold tailWord_2124011
  simp only [CollatzResearch.WordTrace]
  refine ⟨77469045508078374043731887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51646030338718916029154591 77469045508078374043731887)
  ·
    refine ⟨116203568262117561065597831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77469045508078374043731887 116203568262117561065597831)
    ·
      refine ⟨174305352393176341598396747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116203568262117561065597831 174305352393176341598396747)
      ·
        refine ⟨261458028589764512397595121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174305352393176341598396747 261458028589764512397595121)
        ·
          refine ⟨196093521442323384298196341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261458028589764512397595121 196093521442323384298196341)
          ·
            refine ⟨18383767635217817277955907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 196093521442323384298196341 18383767635217817277955907)
            ·
              refine ⟨27575651452826725916933861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18383767635217817277955907 27575651452826725916933861)
              ·
                refine ⟨5170434647405011109425099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27575651452826725916933861 5170434647405011109425099)
                ·
                  refine ⟨7755651971107516664137649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5170434647405011109425099 7755651971107516664137649)
                  ·
                    refine ⟨5816738978330637498103237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7755651971107516664137649 5816738978330637498103237)
                    ·
                      refine ⟨1090638558436994530894357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5816738978330637498103237 1090638558436994530894357)
                      ·
                        rfl

theorem cell23_2124011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 4].length) (baseStart_2124011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124011 prefixEnd_2124011 := by exact prefixLift 2124011
  have htrace : WordTrace (prefixWord ++ tailWord_2124011) baseStart_2124011 baseEnd_2124011 := by
    simpa [prefixWord, tailWord_2124011, baseEnd_2124011] using wordTrace_append hprefix tailTrace_2124011
  have hstable : (prefixWord ++ tailWord_2124011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124011).length < 2 ^ (prefixWord ++ tailWord_2124011).sum := by decide
  have hdescent : baseEnd_2124011 < baseStart_2124011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124015 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 1, 1, 4]
def baseStart_2124015 : Nat := 118140960795 + 2124015 * 2 ^ 59
def prefixEnd_2124015 : Nat := 4983230072969 + 3 ^ 40 * 2124015 * 2
def baseEnd_2124015 : Nat := 1090640612359612515244339

theorem tailTrace_2124015 : CollatzResearch.WordTrace tailWord_2124015 prefixEnd_2124015 1090640612359612515244339 := by
  unfold tailWord_2124015
  simp only [CollatzResearch.WordTrace]
  refine ⟨77469191400063882726877499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51646127600042588484584999 77469191400063882726877499)
  ·
    refine ⟨116203787100095824090316249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77469191400063882726877499 116203787100095824090316249)
    ·
      refine ⟨87152840325071868067737187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116203787100095824090316249 87152840325071868067737187)
      ·
        refine ⟨130729260487607802101605781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87152840325071868067737187 130729260487607802101605781)
        ·
          refine ⟨6127934085356615723512771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 130729260487607802101605781 6127934085356615723512771)
          ·
            refine ⟨9191901128034923585269157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6127934085356615723512771 9191901128034923585269157)
            ·
              refine ⟨1723481461506548172237967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9191901128034923585269157 1723481461506548172237967)
              ·
                refine ⟨2585222192259822258356951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723481461506548172237967 2585222192259822258356951)
                ·
                  refine ⟨3877833288389733387535427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2585222192259822258356951 3877833288389733387535427)
                  ·
                    refine ⟨5816749932584600081303141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3877833288389733387535427 5816749932584600081303141)
                    ·
                      refine ⟨1090640612359612515244339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5816749932584600081303141 1090640612359612515244339)
                      ·
                        rfl

theorem cell23_2124015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 1, 4].length) (baseStart_2124015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124015 prefixEnd_2124015 := by exact prefixLift 2124015
  have htrace : WordTrace (prefixWord ++ tailWord_2124015) baseStart_2124015 baseEnd_2124015 := by
    simpa [prefixWord, tailWord_2124015, baseEnd_2124015] using wordTrace_append hprefix tailTrace_2124015
  have hstable : (prefixWord ++ tailWord_2124015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124015).length < 2 ^ (prefixWord ++ tailWord_2124015).sum := by decide
  have hdescent : baseEnd_2124015 < baseStart_2124015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124032 : List Nat := [2, 1, 1, 2, 1, 1, 6, 4, 1, 2, 2]
def baseStart_2124032 : Nat := 118140960795 + 2124032 * 2 ^ 59
def prefixEnd_2124032 : Nat := 4983230072969 + 3 ^ 40 * 2124032 * 2
def baseEnd_2124032 : Nat := 1090649341530738948731761

theorem tailTrace_2124032 : CollatzResearch.WordTrace tailWord_2124032 prefixEnd_2124032 1090649341530738948731761 := by
  unfold tailWord_2124032
  simp only [CollatzResearch.WordTrace]
  refine ⟨38734905720501147315123175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51646540960668196420164233 38734905720501147315123175)
  ·
    refine ⟨58102358580751720972684763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38734905720501147315123175 58102358580751720972684763)
    ·
      refine ⟨87153537871127581459027145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58102358580751720972684763 87153537871127581459027145)
      ·
        refine ⟨65365153403345686094270359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87153537871127581459027145 65365153403345686094270359)
        ·
          refine ⟨98047730105018529141405539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65365153403345686094270359 98047730105018529141405539)
          ·
            refine ⟨147071595157527793712108309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98047730105018529141405539 147071595157527793712108309)
            ·
              refine ⟨6893981023009115330255077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147071595157527793712108309 6893981023009115330255077)
              ·
                refine ⟨1292621441814209124422827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6893981023009115330255077 1292621441814209124422827)
                ·
                  refine ⟨1938932162721313686634241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292621441814209124422827 1938932162721313686634241)
                  ·
                    refine ⟨1454199122040985264975681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1938932162721313686634241 1454199122040985264975681)
                    ·
                      refine ⟨1090649341530738948731761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454199122040985264975681 1090649341530738948731761)
                      ·
                        rfl

theorem cell23_2124032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 4, 1, 2, 2].length) (baseStart_2124032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124032 prefixEnd_2124032 := by exact prefixLift 2124032
  have htrace : WordTrace (prefixWord ++ tailWord_2124032) baseStart_2124032 baseEnd_2124032 := by
    simpa [prefixWord, tailWord_2124032, baseEnd_2124032] using wordTrace_append hprefix tailTrace_2124032
  have hstable : (prefixWord ++ tailWord_2124032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124032).length < 2 ^ (prefixWord ++ tailWord_2124032).sum := by decide
  have hdescent : baseEnd_2124032 < baseStart_2124032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124066 : List Nat := [3, 3, 1, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_2124066 : Nat := 118140960795 + 2124066 * 2 ^ 59
def prefixEnd_2124066 : Nat := 4983230072969 + 3 ^ 40 * 2124066 * 2
def baseEnd_2124066 : Nat := 1090666799872991815706605

theorem tailTrace_2124066 : CollatzResearch.WordTrace tailWord_2124066 prefixEnd_2124066 1090666799872991815706605 := by
  unfold tailWord_2124066
  simp only [CollatzResearch.WordTrace]
  refine ⟨19367762880719779609246013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51647367681919412291322701 19367762880719779609246013)
  ·
    refine ⟨7262911080269917353467255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19367762880719779609246013 7262911080269917353467255)
    ·
      refine ⟨10894366620404876030200883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7262911080269917353467255 10894366620404876030200883)
      ·
        refine ⟨16341549930607314045301325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10894366620404876030200883 16341549930607314045301325)
        ·
          refine ⟨6128081223977742766987997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16341549930607314045301325 6128081223977742766987997)
          ·
            refine ⟨2298030458991653537620499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6128081223977742766987997 2298030458991653537620499)
            ·
              refine ⟨3447045688487480306430749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2298030458991653537620499 3447045688487480306430749)
              ·
                refine ⟨1292642133182805114911531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3447045688487480306430749 1292642133182805114911531)
                ·
                  refine ⟨1938963199774207672367297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292642133182805114911531 1938963199774207672367297)
                  ·
                    refine ⟨1454222399830655754275473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1938963199774207672367297 1454222399830655754275473)
                    ·
                      refine ⟨1090666799872991815706605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454222399830655754275473 1090666799872991815706605)
                      ·
                        rfl

theorem cell23_2124066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_2124066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124066 prefixEnd_2124066 := by exact prefixLift 2124066
  have htrace : WordTrace (prefixWord ++ tailWord_2124066) baseStart_2124066 baseEnd_2124066 := by
    simpa [prefixWord, tailWord_2124066, baseEnd_2124066] using wordTrace_append hprefix tailTrace_2124066
  have hstable : (prefixWord ++ tailWord_2124066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124066).length < 2 ^ (prefixWord ++ tailWord_2124066).sum := by decide
  have hdescent : baseEnd_2124066 < baseStart_2124066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124151 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_2124151 : Nat := 118140960795 + 2124151 * 2 ^ 59
def prefixEnd_2124151 : Nat := 4983230072969 + 3 ^ 40 * 2124151 * 2
def baseEnd_2124151 : Nat := 1090710445728623983143713

theorem tailTrace_2124151 : CollatzResearch.WordTrace tailWord_2124151 prefixEnd_2124151 1090710445728623983143713 := by
  unfold tailWord_2124151
  simp only [CollatzResearch.WordTrace]
  refine ⟨77474151727571177953828307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51649434485047451969218871 77474151727571177953828307)
  ·
    refine ⟨116211227591356766930742461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77474151727571177953828307 116211227591356766930742461)
    ·
      refine ⟨43579210346758787599028423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116211227591356766930742461 43579210346758787599028423)
      ·
        refine ⟨65368815520138181398542635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43579210346758787599028423 65368815520138181398542635)
        ·
          refine ⟨98053223280207272097813953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65368815520138181398542635 98053223280207272097813953)
          ·
            refine ⟨73539917460155454073360465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98053223280207272097813953 73539917460155454073360465)
            ·
              refine ⟨55154938095116590555020349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73539917460155454073360465 55154938095116590555020349)
              ·
                refine ⟨20683101785668721458132631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55154938095116590555020349 20683101785668721458132631)
                ·
                  refine ⟨31024652678503082187198947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20683101785668721458132631 31024652678503082187198947)
                  ·
                    refine ⟨46536979017754623280798421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31024652678503082187198947 46536979017754623280798421)
                    ·
                      refine ⟨1090710445728623983143713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46536979017754623280798421 1090710445728623983143713)
                      ·
                        rfl

theorem cell23_2124151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_2124151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124151 prefixEnd_2124151 := by exact prefixLift 2124151
  have htrace : WordTrace (prefixWord ++ tailWord_2124151) baseStart_2124151 baseEnd_2124151 := by
    simpa [prefixWord, tailWord_2124151, baseEnd_2124151] using wordTrace_append hprefix tailTrace_2124151
  have hstable : (prefixWord ++ tailWord_2124151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124151).length < 2 ^ (prefixWord ++ tailWord_2124151).sum := by decide
  have hdescent : baseEnd_2124151 < baseStart_2124151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124162 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 7]
def baseStart_2124162 : Nat := 118140960795 + 2124162 * 2 ^ 59
def prefixEnd_2124162 : Nat := 4983230072969 + 3 ^ 40 * 2124162 * 2
def baseEnd_2124162 : Nat := 121190677112869271122907

theorem tailTrace_2124162 : CollatzResearch.WordTrace tailWord_2124162 prefixEnd_2124162 121190677112869271122907 := by
  unfold tailWord_2124162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19368638232632831708119685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51649701953687551221652493 19368638232632831708119685)
  ·
    refine ⟨3631619668618655945272441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19368638232632831708119685 3631619668618655945272441)
    ·
      refine ⟨2723714751463991958954331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3631619668618655945272441 2723714751463991958954331)
      ·
        refine ⟨4085572127195987938431497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2723714751463991958954331 4085572127195987938431497)
        ·
          refine ⟨3064179095396990953823623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4085572127195987938431497 3064179095396990953823623)
          ·
            refine ⟨4596268643095486430735435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3064179095396990953823623 4596268643095486430735435)
            ·
              refine ⟨6894402964643229646103153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4596268643095486430735435 6894402964643229646103153)
              ·
                refine ⟨5170802223482422234577365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6894402964643229646103153 5170802223482422234577365)
                ·
                  refine ⟨121190677112869271122907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5170802223482422234577365 121190677112869271122907)
                  ·
                    rfl

theorem cell23_2124162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_2124162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124162 prefixEnd_2124162 := by exact prefixLift 2124162
  have htrace : WordTrace (prefixWord ++ tailWord_2124162) baseStart_2124162 baseEnd_2124162 := by
    simpa [prefixWord, tailWord_2124162, baseEnd_2124162] using wordTrace_append hprefix tailTrace_2124162
  have hstable : (prefixWord ++ tailWord_2124162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124162).length < 2 ^ (prefixWord ++ tailWord_2124162).sum := by decide
  have hdescent : baseEnd_2124162 < baseStart_2124162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124195 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 2, 4, 2]
def baseStart_2124195 : Nat := 118140960795 + 2124195 * 2 ^ 59
def prefixEnd_2124195 : Nat := 4983230072969 + 3 ^ 40 * 2124195 * 2
def baseEnd_2124195 : Nat := 1090733038877421810993511

theorem tailTrace_2124195 : CollatzResearch.WordTrace tailWord_2124195 prefixEnd_2124195 1090733038877421810993511 := by
  unfold tailWord_2124195
  simp only [CollatzResearch.WordTrace]
  refine ⟨77475756539411773468430039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51650504359607848978953359 77475756539411773468430039)
  ·
    refine ⟨116213634809117660202645059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77475756539411773468430039 116213634809117660202645059)
    ·
      refine ⟨174320452213676490303967589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116213634809117660202645059 174320452213676490303967589)
      ·
        refine ⟨32685084790064341931993923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174320452213676490303967589 32685084790064341931993923)
        ·
          refine ⟨49027627185096512897990885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32685084790064341931993923 49027627185096512897990885)
          ·
            refine ⟨9192680097205596168373291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49027627185096512897990885 9192680097205596168373291)
            ·
              refine ⟨13789020145808394252559937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9192680097205596168373291 13789020145808394252559937)
              ·
                refine ⟨10341765109356295689419953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13789020145808394252559937 10341765109356295689419953)
                ·
                  refine ⟨7756323832017221767064965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10341765109356295689419953 7756323832017221767064965)
                  ·
                    refine ⟨1454310718503229081324681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7756323832017221767064965 1454310718503229081324681)
                    ·
                      refine ⟨1090733038877421810993511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454310718503229081324681 1090733038877421810993511)
                      ·
                        rfl

theorem cell23_2124195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 4, 2].length) (baseStart_2124195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124195 prefixEnd_2124195 := by exact prefixLift 2124195
  have htrace : WordTrace (prefixWord ++ tailWord_2124195) baseStart_2124195 baseEnd_2124195 := by
    simpa [prefixWord, tailWord_2124195, baseEnd_2124195] using wordTrace_append hprefix tailTrace_2124195
  have hstable : (prefixWord ++ tailWord_2124195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124195).length < 2 ^ (prefixWord ++ tailWord_2124195).sum := by decide
  have hdescent : baseEnd_2124195 < baseStart_2124195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124218 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 6]
def baseStart_2124218 : Nat := 118140960795 + 2124218 * 2 ^ 59
def prefixEnd_2124218 : Nat := 4983230072969 + 3 ^ 40 * 2124218 * 2
def baseEnd_2124218 : Nat := 121193872103608357889545

theorem tailTrace_2124218 : CollatzResearch.WordTrace tailWord_2124218 prefixEnd_2124218 121193872103608357889545 := by
  unfold tailWord_2124218
  simp only [CollatzResearch.WordTrace]
  refine ⟨19369148854582112099129327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51651063612218965597678205 19369148854582112099129327)
  ·
    refine ⟨29053723281873168148693991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19369148854582112099129327 29053723281873168148693991)
    ·
      refine ⟨43580584922809752223040987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29053723281873168148693991 43580584922809752223040987)
      ·
        refine ⟨65370877384214628334561481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43580584922809752223040987 65370877384214628334561481)
        ·
          refine ⟨49028158038160971250921111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65370877384214628334561481 49028158038160971250921111)
          ·
            refine ⟨73542237057241456876381667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49028158038160971250921111 73542237057241456876381667)
            ·
              refine ⟨110313355585862185314572501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73542237057241456876381667 110313355585862185314572501)
              ·
                refine ⟨2585469271543644968310293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 110313355585862185314572501 2585469271543644968310293)
                ·
                  refine ⟨121193872103608357889545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2585469271543644968310293 121193872103608357889545)
                  ·
                    rfl

theorem cell23_2124218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_2124218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124218 prefixEnd_2124218 := by exact prefixLift 2124218
  have htrace : WordTrace (prefixWord ++ tailWord_2124218) baseStart_2124218 baseEnd_2124218 := by
    simpa [prefixWord, tailWord_2124218, baseEnd_2124218] using wordTrace_append hprefix tailTrace_2124218
  have hstable : (prefixWord ++ tailWord_2124218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124218).length < 2 ^ (prefixWord ++ tailWord_2124218).sum := by decide
  have hdescent : baseEnd_2124218 < baseStart_2124218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124248 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 5, 5]
def baseStart_2124248 : Nat := 118140960795 + 2124248 * 2 ^ 59
def prefixEnd_2124248 : Nat := 4983230072969 + 3 ^ 40 * 2124248 * 2
def baseEnd_2124248 : Nat := 363586751117370034543589

theorem tailTrace_2124248 : CollatzResearch.WordTrace tailWord_2124248 prefixEnd_2124248 363586751117370034543589 := by
  unfold tailWord_2124248
  simp only [CollatzResearch.WordTrace]
  refine ⟨38738844804109881760054699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51651793072146509013406265 38738844804109881760054699)
  ·
    refine ⟨58108267206164822640082049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38738844804109881760054699 58108267206164822640082049)
    ·
      refine ⟨43581200404623616980061537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58108267206164822640082049 43581200404623616980061537)
      ·
        refine ⟨32685900303467712735046153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43581200404623616980061537 32685900303467712735046153)
        ·
          refine ⟨24514425227600784551284615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32685900303467712735046153 24514425227600784551284615)
          ·
            refine ⟨36771637841401176826926923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24514425227600784551284615 36771637841401176826926923)
            ·
              refine ⟨55157456762101765240390385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36771637841401176826926923 55157456762101765240390385)
              ·
                refine ⟨41368092571576323930292789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55157456762101765240390385 41368092571576323930292789)
                ·
                  refine ⟨3878258678585280368464949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41368092571576323930292789 3878258678585280368464949)
                  ·
                    refine ⟨363586751117370034543589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3878258678585280368464949 363586751117370034543589)
                    ·
                      rfl

theorem cell23_2124248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_2124248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124248 prefixEnd_2124248 := by exact prefixLift 2124248
  have htrace : WordTrace (prefixWord ++ tailWord_2124248) baseStart_2124248 baseEnd_2124248 := by
    simpa [prefixWord, tailWord_2124248, baseEnd_2124248] using wordTrace_append hprefix tailTrace_2124248
  have hstable : (prefixWord ++ tailWord_2124248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124248).length < 2 ^ (prefixWord ++ tailWord_2124248).sum := by decide
  have hdescent : baseEnd_2124248 < baseStart_2124248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124269 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 6]
def baseStart_2124269 : Nat := 118140960795 + 2124269 * 2 ^ 59
def prefixEnd_2124269 : Nat := 4983230072969 + 3 ^ 40 * 2124269 * 2
def baseEnd_2124269 : Nat := 121196781827317169052019

theorem tailTrace_2124269 : CollatzResearch.WordTrace tailWord_2124269 prefixEnd_2124269 121196781827317169052019 := by
  unfold tailWord_2124269
  simp only [CollatzResearch.WordTrace]
  refine ⟨77478455541143684106623861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51652303694095789404415907 77478455541143684106623861)
  ·
    refine ⟨7263605206982220384995987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77478455541143684106623861 7263605206982220384995987)
    ·
      refine ⟨10895407810473330577493981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7263605206982220384995987 10895407810473330577493981)
      ·
        refine ⟨4085777928927498966560243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10895407810473330577493981 4085777928927498966560243)
        ·
          refine ⟨6128666893391248449840365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4085777928927498966560243 6128666893391248449840365)
          ·
            refine ⟨2298250085021718168690137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6128666893391248449840365 2298250085021718168690137)
            ·
              refine ⟨1723687563766288626517603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298250085021718168690137 1723687563766288626517603)
              ·
                refine ⟨2585531345649432939776405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723687563766288626517603 2585531345649432939776405)
                ·
                  refine ⟨121196781827317169052019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2585531345649432939776405 121196781827317169052019)
                  ·
                    rfl

theorem cell23_2124269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_2124269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124269 prefixEnd_2124269 := by exact prefixLift 2124269
  have htrace : WordTrace (prefixWord ++ tailWord_2124269) baseStart_2124269 baseEnd_2124269 := by
    simpa [prefixWord, tailWord_2124269, baseEnd_2124269] using wordTrace_append hprefix tailTrace_2124269
  have hstable : (prefixWord ++ tailWord_2124269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124269).length < 2 ^ (prefixWord ++ tailWord_2124269).sum := by decide
  have hdescent : baseEnd_2124269 < baseStart_2124269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124285 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_2124285 : Nat := 118140960795 + 2124285 * 2 ^ 59
def prefixEnd_2124285 : Nat := 4983230072969 + 3 ^ 40 * 2124285 * 2
def baseEnd_2124285 : Nat := 1090779252136326458868097

theorem tailTrace_2124285 : CollatzResearch.WordTrace tailWord_2124285 prefixEnd_2124285 1090779252136326458868097 := by
  unfold tailWord_2124285
  simp only [CollatzResearch.WordTrace]
  refine ⟨77479039109085718839206309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51652692739390479226137539 77479039109085718839206309)
  ·
    refine ⟨14527319832953572282351183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77479039109085718839206309 14527319832953572282351183)
    ·
      refine ⟨21790979749430358423526775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14527319832953572282351183 21790979749430358423526775)
      ·
        refine ⟨32686469624145537635290163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21790979749430358423526775 32686469624145537635290163)
        ·
          refine ⟨49029704436218306452935245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32686469624145537635290163 49029704436218306452935245)
          ·
            refine ⟨18386139163581864919850717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49029704436218306452935245 18386139163581864919850717)
            ·
              refine ⟨6894802186343199344944019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18386139163581864919850717 6894802186343199344944019)
              ·
                refine ⟨10342203279514799017416029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6894802186343199344944019 10342203279514799017416029)
                ·
                  refine ⟨3878326229818049631531011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10342203279514799017416029 3878326229818049631531011)
                  ·
                    refine ⟨5817489344727074447296517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3878326229818049631531011 5817489344727074447296517)
                    ·
                      refine ⟨1090779252136326458868097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5817489344727074447296517 1090779252136326458868097)
                      ·
                        rfl

theorem cell23_2124285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_2124285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124285 prefixEnd_2124285 := by exact prefixLift 2124285
  have htrace : WordTrace (prefixWord ++ tailWord_2124285) baseStart_2124285 baseEnd_2124285 := by
    simpa [prefixWord, tailWord_2124285, baseEnd_2124285] using wordTrace_append hprefix tailTrace_2124285
  have hstable : (prefixWord ++ tailWord_2124285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124285).length < 2 ^ (prefixWord ++ tailWord_2124285).sum := by decide
  have hdescent : baseEnd_2124285 < baseStart_2124285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124289 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_2124289 : Nat := 118140960795 + 2124289 * 2 ^ 59
def prefixEnd_2124289 : Nat := 4983230072969 + 3 ^ 40 * 2124289 * 2
def baseEnd_2124289 : Nat := 1090781306058944443218079

theorem tailTrace_2124289 : CollatzResearch.WordTrace tailWord_2124289 prefixEnd_2124289 1090781306058944443218079 := by
  unfold tailWord_2124289
  simp only [CollatzResearch.WordTrace]
  refine ⟨77479185001071227522351921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51652790000714151681567947 77479185001071227522351921)
  ·
    refine ⟨58109388750803420641763941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77479185001071227522351921 58109388750803420641763941)
    ·
      refine ⟨10895510390775641370330739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58109388750803420641763941 10895510390775641370330739)
      ·
        refine ⟨16343265586163462055496109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10895510390775641370330739 16343265586163462055496109)
        ·
          refine ⟨6128724594811298270811041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16343265586163462055496109 6128724594811298270811041)
          ·
            refine ⟨4596543446108473703108281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6128724594811298270811041 4596543446108473703108281)
            ·
              refine ⟨3447407584581355277331211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4596543446108473703108281 3447407584581355277331211)
              ·
                refine ⟨5171111376872032915996817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3447407584581355277331211 5171111376872032915996817)
                ·
                  refine ⟨3878333532654024686997613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5171111376872032915996817 3878333532654024686997613)
                  ·
                    refine ⟨1454375074745259257624105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3878333532654024686997613 1454375074745259257624105)
                    ·
                      refine ⟨1090781306058944443218079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454375074745259257624105 1090781306058944443218079)
                      ·
                        rfl

theorem cell23_2124289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_2124289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124289 prefixEnd_2124289 := by exact prefixLift 2124289
  have htrace : WordTrace (prefixWord ++ tailWord_2124289) baseStart_2124289 baseEnd_2124289 := by
    simpa [prefixWord, tailWord_2124289, baseEnd_2124289] using wordTrace_append hprefix tailTrace_2124289
  have hstable : (prefixWord ++ tailWord_2124289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124289).length < 2 ^ (prefixWord ++ tailWord_2124289).sum := by decide
  have hdescent : baseEnd_2124289 < baseStart_2124289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124312 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 2, 4]
def baseStart_2124312 : Nat := 118140960795 + 2124312 * 2 ^ 59
def prefixEnd_2124312 : Nat := 4983230072969 + 3 ^ 40 * 2124312 * 2
def baseEnd_2124312 : Nat := 363597705371332617743491

theorem tailTrace_2124312 : CollatzResearch.WordTrace tailWord_2124312 prefixEnd_2124312 363597705371332617743491 := by
  unfold tailWord_2124312
  simp only [CollatzResearch.WordTrace]
  refine ⟨38740011939993951225219595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51653349253325268300292793 38740011939993951225219595)
  ·
    refine ⟨58110017909990926837829393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38740011939993951225219595 58110017909990926837829393)
    ·
      refine ⟨43582513432493195128372045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58110017909990926837829393 43582513432493195128372045)
      ·
        refine ⟨16343442537184948173139517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43582513432493195128372045 16343442537184948173139517)
        ·
          refine ⟨6128790951444355564927319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16343442537184948173139517 6128790951444355564927319)
          ·
            refine ⟨9193186427166533347390979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6128790951444355564927319 9193186427166533347390979)
            ·
              refine ⟨13789779640749800021086469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9193186427166533347390979 13789779640749800021086469)
              ·
                refine ⟨2585583682640587503953713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13789779640749800021086469 2585583682640587503953713)
                ·
                  refine ⟨1939187761980440627965285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2585583682640587503953713 1939187761980440627965285)
                  ·
                    refine ⟨363597705371332617743491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1939187761980440627965285 363597705371332617743491)
                    ·
                      rfl

theorem cell23_2124312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_2124312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124312 prefixEnd_2124312 := by exact prefixLift 2124312
  have htrace : WordTrace (prefixWord ++ tailWord_2124312) baseStart_2124312 baseEnd_2124312 := by
    simpa [prefixWord, tailWord_2124312, baseEnd_2124312] using wordTrace_append hprefix tailTrace_2124312
  have hstable : (prefixWord ++ tailWord_2124312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124312).length < 2 ^ (prefixWord ++ tailWord_2124312).sum := by decide
  have hdescent : baseEnd_2124312 < baseStart_2124312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124340 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2124340 : Nat := 118140960795 + 2124340 * 2 ^ 59
def prefixEnd_2124340 : Nat := 4983230072969 + 3 ^ 40 * 2124340 * 2
def baseEnd_2124340 : Nat := 1090807493572323743680345

theorem tailTrace_2124340 : CollatzResearch.WordTrace tailWord_2124340 prefixEnd_2124340 1090807493572323743680345 := by
  unfold tailWord_2124340
  simp only [CollatzResearch.WordTrace]
  refine ⟨38740522561943231616229237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51654030082590975488305649 38740522561943231616229237)
  ·
    refine ⟨3631923990182177964021491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38740522561943231616229237 3631923990182177964021491)
    ·
      refine ⟨5447885985273266946032237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631923990182177964021491 5447885985273266946032237)
      ·
        refine ⟨2042957244477475104762089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5447885985273266946032237 2042957244477475104762089)
        ·
          refine ⟨1532217933358106328571567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2042957244477475104762089 1532217933358106328571567)
          ·
            refine ⟨2298326900037159492857351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532217933358106328571567 2298326900037159492857351)
            ·
              refine ⟨3447490350055739239286027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2298326900037159492857351 3447490350055739239286027)
              ·
                refine ⟨5171235525083608858929041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3447490350055739239286027 5171235525083608858929041)
                ·
                  refine ⟨3878426643812706644196781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5171235525083608858929041 3878426643812706644196781)
                  ·
                    refine ⟨1454409991429764991573793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3878426643812706644196781 1454409991429764991573793)
                    ·
                      refine ⟨1090807493572323743680345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454409991429764991573793 1090807493572323743680345)
                      ·
                        rfl

theorem cell23_2124340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2124340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124340 prefixEnd_2124340 := by exact prefixLift 2124340
  have htrace : WordTrace (prefixWord ++ tailWord_2124340) baseStart_2124340 baseEnd_2124340 := by
    simpa [prefixWord, tailWord_2124340, baseEnd_2124340] using wordTrace_append hprefix tailTrace_2124340
  have hstable : (prefixWord ++ tailWord_2124340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124340).length < 2 ^ (prefixWord ++ tailWord_2124340).sum := by decide
  have hdescent : baseEnd_2124340 < baseStart_2124340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124353 : List Nat := [1, 2, 5, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_2124353 : Nat := 118140960795 + 2124353 * 2 ^ 59
def prefixEnd_2124353 : Nat := 4983230072969 + 3 ^ 40 * 2124353 * 2
def baseEnd_2124353 : Nat := 1090814168820832192817785

theorem tailTrace_2124353 : CollatzResearch.WordTrace tailWord_2124353 prefixEnd_2124353 1090814168820832192817785 := by
  unfold tailWord_2124353
  simp only [CollatzResearch.WordTrace]
  refine ⟨77481519272839366452681713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51654346181892910968454475 77481519272839366452681713)
  ·
    refine ⟨58111139454629524839511285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77481519272839366452681713 58111139454629524839511285)
    ·
      refine ⟨5447919323871517953704183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58111139454629524839511285 5447919323871517953704183)
      ·
        refine ⟨8171878985807276930556275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5447919323871517953704183 8171878985807276930556275)
        ·
          refine ⟨12257818478710915395834413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8171878985807276930556275 12257818478710915395834413)
          ·
            refine ⟨4596681929516593273437905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12257818478710915395834413 4596681929516593273437905)
            ·
              refine ⟨3447511447137444955078429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4596681929516593273437905 3447511447137444955078429)
              ·
                refine ⟨1292816792676541858154411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3447511447137444955078429 1292816792676541858154411)
                ·
                  refine ⟨1939225189014812787231617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292816792676541858154411 1939225189014812787231617)
                  ·
                    refine ⟨1454418891761109590423713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1939225189014812787231617 1454418891761109590423713)
                    ·
                      refine ⟨1090814168820832192817785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454418891761109590423713 1090814168820832192817785)
                      ·
                        rfl

theorem cell23_2124353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_2124353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124353 prefixEnd_2124353 := by exact prefixLift 2124353
  have htrace : WordTrace (prefixWord ++ tailWord_2124353) baseStart_2124353 baseEnd_2124353 := by
    simpa [prefixWord, tailWord_2124353, baseEnd_2124353] using wordTrace_append hprefix tailTrace_2124353
  have hstable : (prefixWord ++ tailWord_2124353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124353).length < 2 ^ (prefixWord ++ tailWord_2124353).sum := by decide
  have hdescent : baseEnd_2124353 < baseStart_2124353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124369 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 2, 1, 3]
def baseStart_2124369 : Nat := 118140960795 + 2124369 * 2 ^ 59
def prefixEnd_2124369 : Nat := 4983230072969 + 3 ^ 40 * 2124369 * 2
def baseEnd_2124369 : Nat := 1090822384511304130217711

theorem tailTrace_2124369 : CollatzResearch.WordTrace tailWord_2124369 prefixEnd_2124369 1090822384511304130217711 := by
  unfold tailWord_2124369
  simp only [CollatzResearch.WordTrace]
  refine ⟨77482102840781401185264161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51654735227187600790176107 77482102840781401185264161)
  ·
    refine ⟨58111577130586050888948121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77482102840781401185264161 58111577130586050888948121)
    ·
      refine ⟨43583682847939538166711091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58111577130586050888948121 43583682847939538166711091)
      ·
        refine ⟨65375524271909307250066637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43583682847939538166711091 65375524271909307250066637)
        ·
          refine ⟨24515821601965990218774989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65375524271909307250066637 24515821601965990218774989)
          ·
            refine ⟨9193433100737246332040621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24515821601965990218774989 9193433100737246332040621)
            ·
              refine ⟨3447537412776467374515233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9193433100737246332040621 3447537412776467374515233)
              ·
                refine ⟨2585653059582350530886425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3447537412776467374515233 2585653059582350530886425)
                ·
                  refine ⟨1939239794686762898164819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2585653059582350530886425 1939239794686762898164819)
                  ·
                    refine ⟨2908859692030144347247229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1939239794686762898164819 2908859692030144347247229)
                    ·
                      refine ⟨1090822384511304130217711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2908859692030144347247229 1090822384511304130217711)
                      ·
                        rfl

theorem cell23_2124369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_2124369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124369 prefixEnd_2124369 := by exact prefixLift 2124369
  have htrace : WordTrace (prefixWord ++ tailWord_2124369) baseStart_2124369 baseEnd_2124369 := by
    simpa [prefixWord, tailWord_2124369, baseEnd_2124369] using wordTrace_append hprefix tailTrace_2124369
  have hstable : (prefixWord ++ tailWord_2124369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124369).length < 2 ^ (prefixWord ++ tailWord_2124369).sum := by decide
  have hdescent : baseEnd_2124369 < baseStart_2124369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124385 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 2, 6]
def baseStart_2124385 : Nat := 118140960795 + 2124385 * 2 ^ 59
def prefixEnd_2124385 : Nat := 4983230072969 + 3 ^ 40 * 2124385 * 2
def baseEnd_2124385 : Nat := 363610200067258689205879

theorem tailTrace_2124385 : CollatzResearch.WordTrace tailWord_2124385 prefixEnd_2124385 363610200067258689205879 := by
  unfold tailWord_2124385
  simp only [CollatzResearch.WordTrace]
  refine ⟨77482686408723435917846609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51655124272482290611897739 77482686408723435917846609)
  ·
    refine ⟨58112014806542576938384957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77482686408723435917846609 58112014806542576938384957)
    ·
      refine ⟨21792005552453466351894359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58112014806542576938384957 21792005552453466351894359)
      ·
        refine ⟨32688008328680199527841539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21792005552453466351894359 32688008328680199527841539)
        ·
          refine ⟨49032012493020299291762309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32688008328680199527841539 49032012493020299291762309)
          ·
            refine ⟨9193502342441306117205433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49032012493020299291762309 9193502342441306117205433)
            ·
              refine ⟨6895126756830979587904075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9193502342441306117205433 6895126756830979587904075)
              ·
                refine ⟨10342690135246469381856113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6895126756830979587904075 10342690135246469381856113)
                ·
                  refine ⟨7757017601434852036392085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10342690135246469381856113 7757017601434852036392085)
                  ·
                    refine ⟨363610200067258689205879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7757017601434852036392085 363610200067258689205879)
                    ·
                      rfl

theorem cell23_2124385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_2124385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124385 prefixEnd_2124385 := by exact prefixLift 2124385
  have htrace : WordTrace (prefixWord ++ tailWord_2124385) baseStart_2124385 baseEnd_2124385 := by
    simpa [prefixWord, tailWord_2124385, baseEnd_2124385] using wordTrace_append hprefix tailTrace_2124385
  have hstable : (prefixWord ++ tailWord_2124385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124385).length < 2 ^ (prefixWord ++ tailWord_2124385).sum := by decide
  have hdescent : baseEnd_2124385 < baseStart_2124385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124409 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 4, 2, 2]
def baseStart_2124409 : Nat := 118140960795 + 2124409 * 2 ^ 59
def prefixEnd_2124409 : Nat := 4983230072969 + 3 ^ 40 * 2124409 * 2
def baseEnd_2124409 : Nat := 1090842923737483973717527

theorem tailTrace_2124409 : CollatzResearch.WordTrace tailWord_2124409 prefixEnd_2124409 1090842923737483973717527 := by
  unfold tailWord_2124409
  simp only [CollatzResearch.WordTrace]
  refine ⟨77483561760636488016720281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51655707840424325344480187 77483561760636488016720281)
  ·
    refine ⟨58112671320477366012540211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77483561760636488016720281 58112671320477366012540211)
    ·
      refine ⟨87169006980716049018810317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58112671320477366012540211 87169006980716049018810317)
      ·
        refine ⟨32688377617768518382053869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87169006980716049018810317 32688377617768518382053869)
        ·
          refine ⟨12258141606663194393270201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32688377617768518382053869 12258141606663194393270201)
          ·
            refine ⟨9193606204997395794952651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12258141606663194393270201 9193606204997395794952651)
            ·
              refine ⟨13790409307496093692428977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9193606204997395794952651 13790409307496093692428977)
              ·
                refine ⟨10342806980622070269321733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13790409307496093692428977 10342806980622070269321733)
                ·
                  refine ⟨1939276308866638175497825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10342806980622070269321733 1939276308866638175497825)
                  ·
                    refine ⟨1454457231649978631623369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1939276308866638175497825 1454457231649978631623369)
                    ·
                      refine ⟨1090842923737483973717527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454457231649978631623369 1090842923737483973717527)
                      ·
                        rfl

theorem cell23_2124409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_2124409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124409 prefixEnd_2124409 := by exact prefixLift 2124409
  have htrace : WordTrace (prefixWord ++ tailWord_2124409) baseStart_2124409 baseEnd_2124409 := by
    simpa [prefixWord, tailWord_2124409, baseEnd_2124409] using wordTrace_append hprefix tailTrace_2124409
  have hstable : (prefixWord ++ tailWord_2124409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124409).length < 2 ^ (prefixWord ++ tailWord_2124409).sum := by decide
  have hdescent : baseEnd_2124409 < baseStart_2124409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124445 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2124445 : Nat := 118140960795 + 2124445 * 2 ^ 59
def prefixEnd_2124445 : Nat := 4983230072969 + 3 ^ 40 * 2124445 * 2
def baseEnd_2124445 : Nat := 363620469680348610955787

theorem tailTrace_2124445 : CollatzResearch.WordTrace tailWord_2124445 prefixEnd_2124445 363620469680348610955787 := by
  unfold tailWord_2124445
  simp only [CollatzResearch.WordTrace]
  refine ⟨77484874788506066165030789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51656583192337377443353859 77484874788506066165030789)
  ·
    refine ⟨14528414022844887405943273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77484874788506066165030789 14528414022844887405943273)
    ·
      refine ⟨10896310517133665554457455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14528414022844887405943273 10896310517133665554457455)
      ·
        refine ⟨16344465775700498331686183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10896310517133665554457455 16344465775700498331686183)
        ·
          refine ⟨24516698663550747497529275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16344465775700498331686183 24516698663550747497529275)
          ·
            refine ⟨36775047995326121246293913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24516698663550747497529275 36775047995326121246293913)
            ·
              refine ⟨27581285996494590934720435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36775047995326121246293913 27581285996494590934720435)
              ·
                refine ⟨41371928994741886402080653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27581285996494590934720435 41371928994741886402080653)
                ·
                  refine ⟨15514473373028207400780245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41371928994741886402080653 15514473373028207400780245)
                  ·
                    refine ⟨363620469680348610955787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15514473373028207400780245 363620469680348610955787)
                    ·
                      rfl

theorem cell23_2124445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2124445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124445 prefixEnd_2124445 := by exact prefixLift 2124445
  have htrace : WordTrace (prefixWord ++ tailWord_2124445) baseStart_2124445 baseEnd_2124445 := by
    simpa [prefixWord, tailWord_2124445, baseEnd_2124445] using wordTrace_append hprefix tailTrace_2124445
  have hstable : (prefixWord ++ tailWord_2124445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124445).length < 2 ^ (prefixWord ++ tailWord_2124445).sum := by decide
  have hdescent : baseEnd_2124445 < baseStart_2124445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124495 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 4]
def baseStart_2124495 : Nat := 118140960795 + 2124495 * 2 ^ 59
def prefixEnd_2124495 : Nat := 4983230072969 + 3 ^ 40 * 2124495 * 2
def baseEnd_2124495 : Nat := 1090887083073770637242131

theorem tailTrace_2124495 : CollatzResearch.WordTrace tailWord_2124495 prefixEnd_2124495 1090887083073770637242131 := by
  unfold tailWord_2124495
  simp only [CollatzResearch.WordTrace]
  refine ⟨77486698438324924704350939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51657798958883283136233959 77486698438324924704350939)
  ·
    refine ⟨116230047657487387056526409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77486698438324924704350939 116230047657487387056526409)
    ·
      refine ⟨87172535743115540292394807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116230047657487387056526409 87172535743115540292394807)
      ·
        refine ⟨130758803614673310438592211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87172535743115540292394807 130758803614673310438592211)
        ·
          refine ⟨196138205422009965657888317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130758803614673310438592211 196138205422009965657888317)
          ·
            refine ⟨73551827033253737121708119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196138205422009965657888317 73551827033253737121708119)
            ·
              refine ⟨110327740549880605682562179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73551827033253737121708119 110327740549880605682562179)
              ·
                refine ⟨165491610824820908523843269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110327740549880605682562179 165491610824820908523843269)
                ·
                  refine ⟨31029677029653920348220613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165491610824820908523843269 31029677029653920348220613)
                  ·
                    refine ⟨5818064443060110065291365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31029677029653920348220613 5818064443060110065291365)
                    ·
                      refine ⟨1090887083073770637242131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5818064443060110065291365 1090887083073770637242131)
                      ·
                        rfl

theorem cell23_2124495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_2124495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124495 prefixEnd_2124495 := by exact prefixLift 2124495
  have htrace : WordTrace (prefixWord ++ tailWord_2124495) baseStart_2124495 baseEnd_2124495 := by
    simpa [prefixWord, tailWord_2124495, baseEnd_2124495] using wordTrace_append hprefix tailTrace_2124495
  have hstable : (prefixWord ++ tailWord_2124495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124495).length < 2 ^ (prefixWord ++ tailWord_2124495).sum := by decide
  have hdescent : baseEnd_2124495 < baseStart_2124495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124526 : List Nat := [4, 1, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_2124526 : Nat := 118140960795 + 2124526 * 2 ^ 59
def prefixEnd_2124526 : Nat := 4983230072969 + 3 ^ 40 * 2124526 * 2
def baseEnd_2124526 : Nat := 363634333658020005318163

theorem tailTrace_2124526 : CollatzResearch.WordTrace tailWord_2124526 prefixEnd_2124526 363634333658020005318163 := by
  unfold tailWord_2124526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9685978637651577124841179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51658552734141744665819621 9685978637651577124841179)
  ·
    refine ⟨14528967956477365687261769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9685978637651577124841179 14528967956477365687261769)
    ·
      refine ⟨10896725967358024265446327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14528967956477365687261769 10896725967358024265446327)
      ·
        refine ⟨16345088951037036398169491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10896725967358024265446327 16345088951037036398169491)
        ·
          refine ⟨24517633426555554597254237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16345088951037036398169491 24517633426555554597254237)
          ·
            refine ⟨9194112534958332973970339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24517633426555554597254237 9194112534958332973970339)
            ·
              refine ⟨13791168802437499460955509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9194112534958332973970339 13791168802437499460955509)
              ·
                refine ⟨1292922075228515574464579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13791168802437499460955509 1292922075228515574464579)
                ·
                  refine ⟨1939383112842773361696869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1292922075228515574464579 1939383112842773361696869)
                  ·
                    refine ⟨363634333658020005318163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1939383112842773361696869 363634333658020005318163)
                    ·
                      rfl

theorem cell23_2124526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_2124526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124526 prefixEnd_2124526 := by exact prefixLift 2124526
  have htrace : WordTrace (prefixWord ++ tailWord_2124526) baseStart_2124526 baseEnd_2124526 := by
    simpa [prefixWord, tailWord_2124526, baseEnd_2124526] using wordTrace_append hprefix tailTrace_2124526
  have hstable : (prefixWord ++ tailWord_2124526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124526).length < 2 ^ (prefixWord ++ tailWord_2124526).sum := by decide
  have hdescent : baseEnd_2124526 < baseStart_2124526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124599 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 2, 4]
def baseStart_2124599 : Nat := 118140960795 + 2124599 * 2 ^ 59
def prefixEnd_2124599 : Nat := 4983230072969 + 3 ^ 40 * 2124599 * 2
def baseEnd_2124599 : Nat := 363646828353946076780551

theorem tailTrace_2124599 : CollatzResearch.WordTrace tailWord_2124599 prefixEnd_2124599 363646828353946076780551 := by
  unfold tailWord_2124599
  simp only [CollatzResearch.WordTrace]
  refine ⟨77490491629948150466136851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51660327753298766977424567 77490491629948150466136851)
  ·
    refine ⟨116235737444922225699205277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77490491629948150466136851 116235737444922225699205277)
    ·
      refine ⟨43588401541845834637201979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116235737444922225699205277 43588401541845834637201979)
      ·
        refine ⟨65382602312768751955802969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43588401541845834637201979 65382602312768751955802969)
        ·
          refine ⟨49036951734576563966852227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65382602312768751955802969 49036951734576563966852227)
          ·
            refine ⟨73555427601864845950278341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49036951734576563966852227 73555427601864845950278341)
            ·
              refine ⟨13791642675349658615677189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73555427601864845950278341 13791642675349658615677189)
              ·
                refine ⟨2585933001628060990439473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13791642675349658615677189 2585933001628060990439473)
                ·
                  refine ⟨1939449751221045742829605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2585933001628060990439473 1939449751221045742829605)
                  ·
                    refine ⟨363646828353946076780551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1939449751221045742829605 363646828353946076780551)
                    ·
                      rfl

theorem cell23_2124599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_2124599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124599 prefixEnd_2124599 := by exact prefixLift 2124599
  have htrace : WordTrace (prefixWord ++ tailWord_2124599) baseStart_2124599 baseEnd_2124599 := by
    simpa [prefixWord, tailWord_2124599, baseEnd_2124599] using wordTrace_append hprefix tailTrace_2124599
  have hstable : (prefixWord ++ tailWord_2124599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124599).length < 2 ^ (prefixWord ++ tailWord_2124599).sum := by decide
  have hdescent : baseEnd_2124599 < baseStart_2124599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124636 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2124636 : Nat := 118140960795 + 2124636 * 2 ^ 59
def prefixEnd_2124636 : Nat := 4983230072969 + 3 ^ 40 * 2124636 * 2
def baseEnd_2124636 : Nat := 1090959483846054585578983

theorem tailTrace_2124636 : CollatzResearch.WordTrace tailWord_2124636 prefixEnd_2124636 1090959483846054585578983 := by
  unfold tailWord_2124636
  simp only [CollatzResearch.WordTrace]
  refine ⟨38745920565407052892616881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51661227420542737190155841 38745920565407052892616881)
  ·
    refine ⟨29059440424055289669462661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38745920565407052892616881 29059440424055289669462661)
    ·
      refine ⟨5448645079510366813024249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29059440424055289669462661 5448645079510366813024249)
      ·
        refine ⟨4086483809632775109768187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5448645079510366813024249 4086483809632775109768187)
        ·
          refine ⟨6129725714449162664652281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4086483809632775109768187 6129725714449162664652281)
          ·
            refine ⟨4597294285836871998489211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6129725714449162664652281 4597294285836871998489211)
            ·
              refine ⟨6895941428755307997733817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4597294285836871998489211 6895941428755307997733817)
              ·
                refine ⟨5171956071566480998300363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6895941428755307997733817 5171956071566480998300363)
                ·
                  refine ⟨7757934107349721497450545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5171956071566480998300363 7757934107349721497450545)
                  ·
                    refine ⟨5818450580512291123087909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7757934107349721497450545 5818450580512291123087909)
                    ·
                      refine ⟨1090959483846054585578983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5818450580512291123087909 1090959483846054585578983)
                      ·
                        rfl

theorem cell23_2124636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2124636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124636 prefixEnd_2124636 := by exact prefixLift 2124636
  have htrace : WordTrace (prefixWord ++ tailWord_2124636) baseStart_2124636 baseEnd_2124636 := by
    simpa [prefixWord, tailWord_2124636, baseEnd_2124636] using wordTrace_append hprefix tailTrace_2124636
  have hstable : (prefixWord ++ tailWord_2124636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124636).length < 2 ^ (prefixWord ++ tailWord_2124636).sum := by decide
  have hdescent : baseEnd_2124636 < baseStart_2124636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124639 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 3]
def baseStart_2124639 : Nat := 118140960795 + 2124639 * 2 ^ 59
def prefixEnd_2124639 : Nat := 4983230072969 + 3 ^ 40 * 2124639 * 2
def baseEnd_2124639 : Nat := 1090961024288018073841469

theorem tailTrace_2124639 : CollatzResearch.WordTrace tailWord_2124639 prefixEnd_2124639 1090961024288018073841469 := by
  unfold tailWord_2124639
  simp only [CollatzResearch.WordTrace]
  refine ⟨77491950549803237297592971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51661300366535491531728647 77491950549803237297592971)
  ·
    refine ⟨116237925824704855946389457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77491950549803237297592971 116237925824704855946389457)
    ·
      refine ⟨87178444368528641959792093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116237925824704855946389457 87178444368528641959792093)
      ·
        refine ⟨32691916638198240734922035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87178444368528641959792093 32691916638198240734922035)
        ·
          refine ⟨49037874957297361102383053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32691916638198240734922035 49037874957297361102383053)
          ·
            refine ⟨18389203108986510413393645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49037874957297361102383053 18389203108986510413393645)
            ·
              refine ⟨6895951165869941405022617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18389203108986510413393645 6895951165869941405022617)
              ·
                refine ⟨5171963374402456053766963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6895951165869941405022617 5171963374402456053766963)
                ·
                  refine ⟨7757945061603684080650445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5171963374402456053766963 7757945061603684080650445)
                  ·
                    refine ⟨2909229398101381530243917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7757945061603684080650445 2909229398101381530243917)
                    ·
                      refine ⟨1090961024288018073841469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2909229398101381530243917 1090961024288018073841469)
                      ·
                        rfl

theorem cell23_2124639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_2124639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124639 prefixEnd_2124639 := by exact prefixLift 2124639
  have htrace : WordTrace (prefixWord ++ tailWord_2124639) baseStart_2124639 baseEnd_2124639 := by
    simpa [prefixWord, tailWord_2124639, baseEnd_2124639] using wordTrace_append hprefix tailTrace_2124639
  have hstable : (prefixWord ++ tailWord_2124639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124639).length < 2 ^ (prefixWord ++ tailWord_2124639).sum := by decide
  have hdescent : baseEnd_2124639 < baseStart_2124639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124643 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 1, 2, 3]
def baseStart_2124643 : Nat := 118140960795 + 2124643 * 2 ^ 59
def prefixEnd_2124643 : Nat := 4983230072969 + 3 ^ 40 * 2124643 * 2
def baseEnd_2124643 : Nat := 1090963078210636058191451

theorem tailTrace_2124643 : CollatzResearch.WordTrace tailWord_2124643 prefixEnd_2124643 1090963078210636058191451 := by
  unfold tailWord_2124643
  simp only [CollatzResearch.WordTrace]
  refine ⟨77492096441788745980738583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51661397627859163987159055 77492096441788745980738583)
  ·
    refine ⟨116238144662683118971107875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77492096441788745980738583 116238144662683118971107875)
    ·
      refine ⟨174357216994024678456661813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116238144662683118971107875 174357216994024678456661813)
      ·
        refine ⟨16345989093189813605312045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 174357216994024678456661813 16345989093189813605312045)
        ·
          refine ⟨6129745909946180101992017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16345989093189813605312045 6129745909946180101992017)
          ·
            refine ⟨4597309432459635076494013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6129745909946180101992017 4597309432459635076494013)
            ·
              refine ⟨1723991037172363153685255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4597309432459635076494013 1723991037172363153685255)
              ·
                refine ⟨2585986555758544730527883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1723991037172363153685255 2585986555758544730527883)
                ·
                  refine ⟨3878979833637817095791825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2585986555758544730527883 3878979833637817095791825)
                  ·
                    refine ⟨2909234875228362821843869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3878979833637817095791825 2909234875228362821843869)
                    ·
                      refine ⟨1090963078210636058191451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2909234875228362821843869 1090963078210636058191451)
                      ·
                        rfl

theorem cell23_2124643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_2124643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124643 prefixEnd_2124643 := by exact prefixLift 2124643
  have htrace : WordTrace (prefixWord ++ tailWord_2124643) baseStart_2124643 baseEnd_2124643 := by
    simpa [prefixWord, tailWord_2124643, baseEnd_2124643] using wordTrace_append hprefix tailTrace_2124643
  have hstable : (prefixWord ++ tailWord_2124643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124643).length < 2 ^ (prefixWord ++ tailWord_2124643).sum := by decide
  have hdescent : baseEnd_2124643 < baseStart_2124643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124656 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 2, 1, 3]
def baseStart_2124656 : Nat := 118140960795 + 2124656 * 2 ^ 59
def prefixEnd_2124656 : Nat := 4983230072969 + 3 ^ 40 * 2124656 * 2
def baseEnd_2124656 : Nat := 1090969753459144507328891

theorem tailTrace_2124656 : CollatzResearch.WordTrace tailWord_2124656 prefixEnd_2124656 1090969753459144507328891 := by
  unfold tailWord_2124656
  simp only [CollatzResearch.WordTrace]
  refine ⟨38746285295370824600480911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51661713727161099467307881 38746285295370824600480911)
  ·
    refine ⟨58119427943056236900721367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38746285295370824600480911 58119427943056236900721367)
    ·
      refine ⟨87179141914584355351082051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58119427943056236900721367 87179141914584355351082051)
      ·
        refine ⟨130768712871876533026623077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87179141914584355351082051 130768712871876533026623077)
        ·
          refine ⟨24519133663476849942491827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130768712871876533026623077 24519133663476849942491827)
          ·
            refine ⟨36778700495215274913737741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24519133663476849942491827 36778700495215274913737741)
            ·
              refine ⟨13792012685705728092651653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36778700495215274913737741 13792012685705728092651653)
              ·
                refine ⟨2586002378569824017372185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13792012685705728092651653 2586002378569824017372185)
                ·
                  refine ⟨1939501783927368013029139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2586002378569824017372185 1939501783927368013029139)
                  ·
                    refine ⟨2909252675891052019543709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1939501783927368013029139 2909252675891052019543709)
                    ·
                      refine ⟨1090969753459144507328891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2909252675891052019543709 1090969753459144507328891)
                      ·
                        rfl

theorem cell23_2124656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2, 1, 3].length) (baseStart_2124656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124656 prefixEnd_2124656 := by exact prefixLift 2124656
  have htrace : WordTrace (prefixWord ++ tailWord_2124656) baseStart_2124656 baseEnd_2124656 := by
    simpa [prefixWord, tailWord_2124656, baseEnd_2124656] using wordTrace_append hprefix tailTrace_2124656
  have hstable : (prefixWord ++ tailWord_2124656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124656).length < 2 ^ (prefixWord ++ tailWord_2124656).sum := by decide
  have hdescent : baseEnd_2124656 < baseStart_2124656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124657 : List Nat := [1, 2, 2, 2, 1, 6, 2, 2, 1, 2, 2]
def baseStart_2124657 : Nat := 118140960795 + 2124657 * 2 ^ 59
def prefixEnd_2124657 : Nat := 4983230072969 + 3 ^ 40 * 2124657 * 2
def baseEnd_2124657 : Nat := 1090970266939799003416387

theorem tailTrace_2124657 : CollatzResearch.WordTrace tailWord_2124657 prefixEnd_2124657 1090970266939799003416387 := by
  unfold tailWord_2124657
  simp only [CollatzResearch.WordTrace]
  refine ⟨77492607063738026371748225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51661738042492017581165483 77492607063738026371748225)
  ·
    refine ⟨58119455297803519778811169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77492607063738026371748225 58119455297803519778811169)
    ·
      refine ⟨43589591473352639834108377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58119455297803519778811169 43589591473352639834108377)
      ·
        refine ⟨32692193605014479875581283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43589591473352639834108377 32692193605014479875581283)
        ·
          refine ⟨49038290407521719813371925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32692193605014479875581283 49038290407521719813371925)
          ·
            refine ⟨2298669862852580616251809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49038290407521719813371925 2298669862852580616251809)
            ·
              refine ⟨1724002397139435462188857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298669862852580616251809 1724002397139435462188857)
              ·
                refine ⟨1293001797854576596641643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1724002397139435462188857 1293001797854576596641643)
                ·
                  refine ⟨1939502696781864894962465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293001797854576596641643 1939502696781864894962465)
                  ·
                    refine ⟨1454627022586398671221849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1939502696781864894962465 1454627022586398671221849)
                    ·
                      refine ⟨1090970266939799003416387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454627022586398671221849 1090970266939799003416387)
                      ·
                        rfl

theorem cell23_2124657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_2124657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124657 prefixEnd_2124657 := by exact prefixLift 2124657
  have htrace : WordTrace (prefixWord ++ tailWord_2124657) baseStart_2124657 baseEnd_2124657 := by
    simpa [prefixWord, tailWord_2124657, baseEnd_2124657] using wordTrace_append hprefix tailTrace_2124657
  have hstable : (prefixWord ++ tailWord_2124657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124657).length < 2 ^ (prefixWord ++ tailWord_2124657).sum := by decide
  have hdescent : baseEnd_2124657 < baseStart_2124657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124694 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_2124694 : Nat := 118140960795 + 2124694 * 2 ^ 59
def prefixEnd_2124694 : Nat := 4983230072969 + 3 ^ 40 * 2124694 * 2
def baseEnd_2124694 : Nat := 1090989265724015358653717

theorem tailTrace_2124694 : CollatzResearch.WordTrace tailWord_2124694 prefixEnd_2124694 1090989265724015358653717 := by
  unfold tailWord_2124694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4843372285287748855677821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51662637709735987793896757 4843372285287748855677821)
  ·
    refine ⟨1816264606982905820879183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4843372285287748855677821 1816264606982905820879183)
    ·
      refine ⟨2724396910474358731318775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1816264606982905820879183 2724396910474358731318775)
      ·
        refine ⟨4086595365711538096978163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2724396910474358731318775 4086595365711538096978163)
        ·
          refine ⟨6129893048567307145467245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4086595365711538096978163 6129893048567307145467245)
          ·
            refine ⟨2298709893212740179550217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6129893048567307145467245 2298709893212740179550217)
            ·
              refine ⟨1724032419909555134662663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2298709893212740179550217 1724032419909555134662663)
              ·
                refine ⟨2586048629864332701993995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724032419909555134662663 2586048629864332701993995)
                ·
                  refine ⟨3879072944796499052990993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586048629864332701993995 3879072944796499052990993)
                  ·
                    refine ⟨2909304708597374289743245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3879072944796499052990993 2909304708597374289743245)
                    ·
                      refine ⟨1090989265724015358653717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2909304708597374289743245 1090989265724015358653717)
                      ·
                        rfl

theorem cell23_2124694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_2124694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124694 prefixEnd_2124694 := by exact prefixLift 2124694
  have htrace : WordTrace (prefixWord ++ tailWord_2124694) baseStart_2124694 baseEnd_2124694 := by
    simpa [prefixWord, tailWord_2124694, baseEnd_2124694] using wordTrace_append hprefix tailTrace_2124694
  have hstable : (prefixWord ++ tailWord_2124694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124694).length < 2 ^ (prefixWord ++ tailWord_2124694).sum := by decide
  have hdescent : baseEnd_2124694 < baseStart_2124694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124700 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_2124700 : Nat := 118140960795 + 2124700 * 2 ^ 59
def prefixEnd_2124700 : Nat := 4983230072969 + 3 ^ 40 * 2124700 * 2
def baseEnd_2124700 : Nat := 1090992346607942335178689

theorem tailTrace_2124700 : CollatzResearch.WordTrace tailWord_2124700 prefixEnd_2124700 1090992346607942335178689 := by
  unfold tailWord_2124700
  simp only [CollatzResearch.WordTrace]
  refine ⟨38747087701291122357781777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51662783601721496477042369 38747087701291122357781777)
  ·
    refine ⟨29060315775968341768336333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38747087701291122357781777 29060315775968341768336333)
    ·
      refine ⟨10897618415988128163126125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29060315775968341768336333 10897618415988128163126125)
      ·
        refine ⟨4086606905995548061172297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10897618415988128163126125 4086606905995548061172297)
        ·
          refine ⟨3064955179496661045879223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4086606905995548061172297 3064955179496661045879223)
          ·
            refine ⟨4597432769244991568818835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3064955179496661045879223 4597432769244991568818835)
            ·
              refine ⟨6896149153867487353228253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4597432769244991568818835 6896149153867487353228253)
              ·
                refine ⟨2586055932700307757460595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6896149153867487353228253 2586055932700307757460595)
                ·
                  refine ⟨3879083899050461636190893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586055932700307757460595 3879083899050461636190893)
                  ·
                    refine ⟨1454656462143923113571585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3879083899050461636190893 1454656462143923113571585)
                    ·
                      refine ⟨1090992346607942335178689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454656462143923113571585 1090992346607942335178689)
                      ·
                        rfl

theorem cell23_2124700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_2124700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124700 prefixEnd_2124700 := by exact prefixLift 2124700
  have htrace : WordTrace (prefixWord ++ tailWord_2124700) baseStart_2124700 baseEnd_2124700 := by
    simpa [prefixWord, tailWord_2124700, baseEnd_2124700] using wordTrace_append hprefix tailTrace_2124700
  have hstable : (prefixWord ++ tailWord_2124700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124700).length < 2 ^ (prefixWord ++ tailWord_2124700).sum := by decide
  have hdescent : baseEnd_2124700 < baseStart_2124700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124730 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2]
def baseStart_2124730 : Nat := 118140960795 + 2124730 * 2 ^ 59
def prefixEnd_2124730 : Nat := 4983230072969 + 3 ^ 40 * 2124730 * 2
def baseEnd_2124730 : Nat := 1091007751027577217803551

theorem tailTrace_2124730 : CollatzResearch.WordTrace tailWord_2124730 prefixEnd_2124730 1091007751027577217803551 := by
  unfold tailWord_2124730
  simp only [CollatzResearch.WordTrace]
  refine ⟨19373817398118389959788911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51663513061649039892770429 19373817398118389959788911)
  ·
    refine ⟨29060726097177584939683367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19373817398118389959788911 29060726097177584939683367)
    ·
      refine ⟨43591089145766377409525051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29060726097177584939683367 43591089145766377409525051)
      ·
        refine ⟨65386633718649566114287577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43591089145766377409525051 65386633718649566114287577)
        ·
          refine ⟨49039975288987174585715683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65386633718649566114287577 49039975288987174585715683)
          ·
            refine ⟨73559962933480761878573525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49039975288987174585715683 73559962933480761878573525)
            ·
              refine ⟨1724061631253455356529067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 73559962933480761878573525 1724061631253455356529067)
              ·
                refine ⟨2586092446880183034793601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724061631253455356529067 2586092446880183034793601)
                ·
                  refine ⟨1939569335160137276095201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2586092446880183034793601 1939569335160137276095201)
                  ·
                    refine ⟨1454677001370102957071401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1939569335160137276095201 1454677001370102957071401)
                    ·
                      refine ⟨1091007751027577217803551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454677001370102957071401 1091007751027577217803551)
                      ·
                        rfl

theorem cell23_2124730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2].length) (baseStart_2124730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124730 prefixEnd_2124730 := by exact prefixLift 2124730
  have htrace : WordTrace (prefixWord ++ tailWord_2124730) baseStart_2124730 baseEnd_2124730 := by
    simpa [prefixWord, tailWord_2124730, baseEnd_2124730] using wordTrace_append hprefix tailTrace_2124730
  have hstable : (prefixWord ++ tailWord_2124730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124730).length < 2 ^ (prefixWord ++ tailWord_2124730).sum := by decide
  have hdescent : baseEnd_2124730 < baseStart_2124730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124823 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2124823 : Nat := 118140960795 + 2124823 * 2 ^ 59
def prefixEnd_2124823 : Nat := 4983230072969 + 3 ^ 40 * 2124823 * 2
def baseEnd_2124823 : Nat := 1091055504728445353940623

theorem tailTrace_2124823 : CollatzResearch.WordTrace tailWord_2124823 prefixEnd_2124823 1091055504728445353940623 := by
  unfold tailWord_2124823
  simp only [CollatzResearch.WordTrace]
  refine ⟨77498661581136636722291123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51665774387424424481527415 77498661581136636722291123)
  ·
    refine ⟨116247992371704955083436685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77498661581136636722291123 116247992371704955083436685)
    ·
      refine ⟨43592997139389358156288757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116247992371704955083436685 43592997139389358156288757)
      ·
        refine ⟨4086843481817752327152071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43592997139389358156288757 4086843481817752327152071)
        ·
          refine ⟨6130265222726628490728107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4086843481817752327152071 6130265222726628490728107)
          ·
            refine ⟨9195397834089942736092161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6130265222726628490728107 9195397834089942736092161)
            ·
              refine ⟨6896548375567457052069121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9195397834089942736092161 6896548375567457052069121)
              ·
                refine ⟨5172411281675592789051841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6896548375567457052069121 5172411281675592789051841)
                ·
                  refine ⟨3879308461256694591788881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5172411281675592789051841 3879308461256694591788881)
                  ·
                    refine ⟨2909481345942520943841661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3879308461256694591788881 2909481345942520943841661)
                    ·
                      refine ⟨1091055504728445353940623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2909481345942520943841661 1091055504728445353940623)
                      ·
                        rfl

theorem cell23_2124823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2124823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124823 prefixEnd_2124823 := by exact prefixLift 2124823
  have htrace : WordTrace (prefixWord ++ tailWord_2124823) baseStart_2124823 baseEnd_2124823 := by
    simpa [prefixWord, tailWord_2124823, baseEnd_2124823] using wordTrace_append hprefix tailTrace_2124823
  have hstable : (prefixWord ++ tailWord_2124823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124823).length < 2 ^ (prefixWord ++ tailWord_2124823).sum := by decide
  have hdescent : baseEnd_2124823 < baseStart_2124823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124826 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 6]
def baseStart_2124826 : Nat := 118140960795 + 2124826 * 2 ^ 59
def prefixEnd_2124826 : Nat := 4983230072969 + 3 ^ 40 * 2124826 * 2
def baseEnd_2124826 : Nat := 121228560574489871355901

theorem tailTrace_2124826 : CollatzResearch.WordTrace tailWord_2124826 prefixEnd_2124826 121228560574489871355901 := by
  unfold tailWord_2124826
  simp only [CollatzResearch.WordTrace]
  refine ⟨19374692750031442058662583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51665847333417178823100221 19374692750031442058662583)
  ·
    refine ⟨29062039125047163087993875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19374692750031442058662583 29062039125047163087993875)
    ·
      refine ⟨43593058687570744631990813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29062039125047163087993875 43593058687570744631990813)
      ·
        refine ⟨16347397007839029236996555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43593058687570744631990813 16347397007839029236996555)
        ·
          refine ⟨24521095511758543855494833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16347397007839029236996555 24521095511758543855494833)
          ·
            refine ⟨18390821633818907891621125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24521095511758543855494833 18390821633818907891621125)
            ·
              refine ⟨3448279056341045229678961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18390821633818907891621125 3448279056341045229678961)
              ·
                refine ⟨2586209292255783922259221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3448279056341045229678961 2586209292255783922259221)
                ·
                  refine ⟨121228560574489871355901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2586209292255783922259221 121228560574489871355901)
                  ·
                    rfl

theorem cell23_2124826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_2124826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124826 prefixEnd_2124826 := by exact prefixLift 2124826
  have htrace : WordTrace (prefixWord ++ tailWord_2124826) baseStart_2124826 baseEnd_2124826 := by
    simpa [prefixWord, tailWord_2124826, baseEnd_2124826] using wordTrace_append hprefix tailTrace_2124826
  have hstable : (prefixWord ++ tailWord_2124826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124826).length < 2 ^ (prefixWord ++ tailWord_2124826).sum := by decide
  have hdescent : baseEnd_2124826 < baseStart_2124826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124849 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2124849 : Nat := 118140960795 + 2124849 * 2 ^ 59
def prefixEnd_2124849 : Nat := 4983230072969 + 3 ^ 40 * 2124849 * 2
def baseEnd_2124849 : Nat := 1091068855225462252215503

theorem tailTrace_2124849 : CollatzResearch.WordTrace tailWord_2124849 prefixEnd_2124849 1091068855225462252215503 := by
  unfold tailWord_2124849
  simp only [CollatzResearch.WordTrace]
  refine ⟨77499609879042443162737601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51666406586028295441825067 77499609879042443162737601)
  ·
    refine ⟨58124707409281832372053201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77499609879042443162737601 58124707409281832372053201)
    ·
      refine ⟨43593530556961374279039901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58124707409281832372053201 43593530556961374279039901)
      ·
        refine ⟨16347573958860515354639963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43593530556961374279039901 16347573958860515354639963)
        ·
          refine ⟨24521360938290773031959945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16347573958860515354639963 24521360938290773031959945)
          ·
            refine ⟨18391020703718079773969959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24521360938290773031959945 18391020703718079773969959)
            ·
              refine ⟨27586531055577119660954939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18391020703718079773969959 27586531055577119660954939)
              ·
                refine ⟨41379796583365679491432409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27586531055577119660954939 41379796583365679491432409)
                ·
                  refine ⟨31034847437524259618574307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41379796583365679491432409 31034847437524259618574307)
                  ·
                    refine ⟨46552271156286389427861461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31034847437524259618574307 46552271156286389427861461)
                    ·
                      refine ⟨1091068855225462252215503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46552271156286389427861461 1091068855225462252215503)
                      ·
                        rfl

theorem cell23_2124849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2124849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124849 prefixEnd_2124849 := by exact prefixLift 2124849
  have htrace : WordTrace (prefixWord ++ tailWord_2124849) baseStart_2124849 baseEnd_2124849 := by
    simpa [prefixWord, tailWord_2124849, baseEnd_2124849] using wordTrace_append hprefix tailTrace_2124849
  have hstable : (prefixWord ++ tailWord_2124849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124849).length < 2 ^ (prefixWord ++ tailWord_2124849).sum := by decide
  have hdescent : baseEnd_2124849 < baseStart_2124849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124856 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 3, 5]
def baseStart_2124856 : Nat := 118140960795 + 2124856 * 2 ^ 59
def prefixEnd_2124856 : Nat := 4983230072969 + 3 ^ 40 * 2124856 * 2
def baseEnd_2124856 : Nat := 363690816530014574942657

theorem tailTrace_2124856 : CollatzResearch.WordTrace tailWord_2124856 prefixEnd_2124856 363690816530014574942657 := by
  unfold tailWord_2124856
  simp only [CollatzResearch.WordTrace]
  refine ⟨38749932595008541679121211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51666576793344722238828281 38749932595008541679121211)
  ·
    refine ⟨58124898892512812518681817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38749932595008541679121211 58124898892512812518681817)
    ·
      refine ⟨43593674169384609389011363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58124898892512812518681817 43593674169384609389011363)
      ·
        refine ⟨65390511254076914083517045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43593674169384609389011363 65390511254076914083517045)
        ·
          refine ⟨6130360430069710695329723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65390511254076914083517045 6130360430069710695329723)
          ·
            refine ⟨9195540645104566042994585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6130360430069710695329723 9195540645104566042994585)
            ·
              refine ⟨6896655483828424532245939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9195540645104566042994585 6896655483828424532245939)
              ·
                refine ⟨10344983225742636798368909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6896655483828424532245939 10344983225742636798368909)
                ·
                  refine ⟨3879368709653488799388341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10344983225742636798368909 3879368709653488799388341)
                  ·
                    refine ⟨363690816530014574942657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3879368709653488799388341 363690816530014574942657)
                    ·
                      rfl

theorem cell23_2124856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_2124856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124856 prefixEnd_2124856 := by exact prefixLift 2124856
  have htrace : WordTrace (prefixWord ++ tailWord_2124856) baseStart_2124856 baseEnd_2124856 := by
    simpa [prefixWord, tailWord_2124856, baseEnd_2124856] using wordTrace_append hprefix tailTrace_2124856
  have hstable : (prefixWord ++ tailWord_2124856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124856).length < 2 ^ (prefixWord ++ tailWord_2124856).sum := by decide
  have hdescent : baseEnd_2124856 < baseStart_2124856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124896 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 5]
def baseStart_2124896 : Nat := 118140960795 + 2124896 * 2 ^ 59
def prefixEnd_2124896 : Nat := 4983230072969 + 3 ^ 40 * 2124896 * 2
def baseEnd_2124896 : Nat := 1091092988816223568327787

theorem tailTrace_2124896 : CollatzResearch.WordTrace tailWord_2124896 prefixEnd_2124896 1091092988816223568327787 := by
  unfold tailWord_2124896
  simp only [CollatzResearch.WordTrace]
  refine ⟨38750662054936085094849271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51667549406581446793132361 38750662054936085094849271)
  ·
    refine ⟨58125993082404127642273907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38750662054936085094849271 58125993082404127642273907)
    ·
      refine ⟨87188989623606191463410861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58125993082404127642273907 87188989623606191463410861)
      ·
        refine ⟨32695871108852321798779073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87188989623606191463410861 32695871108852321798779073)
        ·
          refine ⟨24521903331639241349084305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32695871108852321798779073 24521903331639241349084305)
          ·
            refine ⟨18391427498729431011813229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24521903331639241349084305 18391427498729431011813229)
            ·
              refine ⟨6896785312023536629429961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18391427498729431011813229 6896785312023536629429961)
              ·
                refine ⟨5172588984017652472072471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6896785312023536629429961 5172588984017652472072471)
                ·
                  refine ⟨7758883476026478708108707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5172588984017652472072471 7758883476026478708108707)
                  ·
                    refine ⟨11638325214039718062163061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7758883476026478708108707 11638325214039718062163061)
                    ·
                      refine ⟨1091092988816223568327787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11638325214039718062163061 1091092988816223568327787)
                      ·
                        rfl

theorem cell23_2124896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_2124896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124896 prefixEnd_2124896 := by exact prefixLift 2124896
  have htrace : WordTrace (prefixWord ++ tailWord_2124896) baseStart_2124896 baseEnd_2124896 := by
    simpa [prefixWord, tailWord_2124896, baseEnd_2124896] using wordTrace_append hprefix tailTrace_2124896
  have hstable : (prefixWord ++ tailWord_2124896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124896).length < 2 ^ (prefixWord ++ tailWord_2124896).sum := by decide
  have hdescent : baseEnd_2124896 < baseStart_2124896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124899 : List Nat := [1, 1, 1, 5, 1, 1, 1, 12]
def baseStart_2124899 : Nat := 118140960795 + 2124899 * 2 ^ 59
def prefixEnd_2124899 : Nat := 4983230072969 + 3 ^ 40 * 2124899 * 2
def baseEnd_2124899 : Nat := 40410908491043965058899

theorem tailTrace_2124899 : CollatzResearch.WordTrace tailWord_2124899 prefixEnd_2124899 40410908491043965058899 := by
  unfold tailWord_2124899
  simp only [CollatzResearch.WordTrace]
  refine ⟨77501433528861301702057751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51667622352574201134705167 77501433528861301702057751)
  ·
    refine ⟨116252150293291952553086627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77501433528861301702057751 116252150293291952553086627)
    ·
      refine ⟨174378225439937928829629941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116252150293291952553086627 174378225439937928829629941)
      ·
        refine ⟨16347958634994180827777807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 174378225439937928829629941 16347958634994180827777807)
        ·
          refine ⟨24521937952491271241666711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16347958634994180827777807 24521937952491271241666711)
          ·
            refine ⟨36782906928736906862500067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24521937952491271241666711 36782906928736906862500067)
            ·
              refine ⟨55174360393105360293750101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36782906928736906862500067 55174360393105360293750101)
              ·
                refine ⟨40410908491043965058899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 55174360393105360293750101 40410908491043965058899)
                ·
                  rfl

theorem cell23_2124899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 12].length) (baseStart_2124899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124899 prefixEnd_2124899 := by exact prefixLift 2124899
  have htrace : WordTrace (prefixWord ++ tailWord_2124899) baseStart_2124899 baseEnd_2124899 := by
    simpa [prefixWord, tailWord_2124899, baseEnd_2124899] using wordTrace_append hprefix tailTrace_2124899
  have hstable : (prefixWord ++ tailWord_2124899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124899).length < 2 ^ (prefixWord ++ tailWord_2124899).sum := by decide
  have hdescent : baseEnd_2124899 < baseStart_2124899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124903 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 1, 6]
def baseStart_2124903 : Nat := 118140960795 + 2124903 * 2 ^ 59
def prefixEnd_2124903 : Nat := 4983230072969 + 3 ^ 40 * 2124903 * 2
def baseEnd_2124903 : Nat := 363698861060268346980085

theorem tailTrace_2124903 : CollatzResearch.WordTrace tailWord_2124903 prefixEnd_2124903 363698861060268346980085 := by
  unfold tailWord_2124903
  simp only [CollatzResearch.WordTrace]
  refine ⟨77501579420846810385203363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51667719613897873590135575 77501579420846810385203363)
  ·
    refine ⟨116252369131270215577805045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77501579420846810385203363 116252369131270215577805045)
    ·
      refine ⟨10898659606056582710419223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116252369131270215577805045 10898659606056582710419223)
      ·
        refine ⟨16347989409084874065628835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10898659606056582710419223 16347989409084874065628835)
        ·
          refine ⟨24521984113627311098443253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16347989409084874065628835 24521984113627311098443253)
          ·
            refine ⟨2298936010652560415479055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24521984113627311098443253 2298936010652560415479055)
            ·
              refine ⟨3448404015978840623218583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2298936010652560415479055 3448404015978840623218583)
              ·
                refine ⟨5172606023968260934827875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3448404015978840623218583 5172606023968260934827875)
                ·
                  refine ⟨7758909035952391402241813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5172606023968260934827875 7758909035952391402241813)
                  ·
                    refine ⟨363698861060268346980085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7758909035952391402241813 363698861060268346980085)
                    ·
                      rfl

theorem cell23_2124903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_2124903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124903 prefixEnd_2124903 := by exact prefixLift 2124903
  have htrace : WordTrace (prefixWord ++ tailWord_2124903) baseStart_2124903 baseEnd_2124903 := by
    simpa [prefixWord, tailWord_2124903, baseEnd_2124903] using wordTrace_append hprefix tailTrace_2124903
  have hstable : (prefixWord ++ tailWord_2124903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124903).length < 2 ^ (prefixWord ++ tailWord_2124903).sum := by decide
  have hdescent : baseEnd_2124903 < baseStart_2124903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124910 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_2124910 : Nat := 118140960795 + 2124910 * 2 ^ 59
def prefixEnd_2124910 : Nat := 4983230072969 + 3 ^ 40 * 2124910 * 2
def baseEnd_2124910 : Nat := 1091100177545386513552723

theorem tailTrace_2124910 : CollatzResearch.WordTrace tailWord_2124910 prefixEnd_2124910 1091100177545386513552723 := by
  unfold tailWord_2124910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9687729341477681322588523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51667889821214300387138789 9687729341477681322588523)
  ·
    refine ⟨14531594012216521983882785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9687729341477681322588523 14531594012216521983882785)
    ·
      refine ⟨10898695509162391487912089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14531594012216521983882785 10898695509162391487912089)
      ·
        refine ⟨8174021631871793615934067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10898695509162391487912089 8174021631871793615934067)
        ·
          refine ⟨12261032447807690423901101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8174021631871793615934067 12261032447807690423901101)
          ·
            refine ⟨4597887167927883908962913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12261032447807690423901101 4597887167927883908962913)
            ·
              refine ⟨3448415375945912931722185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4597887167927883908962913 3448415375945912931722185)
              ·
                refine ⟨2586311531959434698791639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3448415375945912931722185 2586311531959434698791639)
                ·
                  refine ⟨3879467297939152048187459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586311531959434698791639 3879467297939152048187459)
                  ·
                    refine ⟨5819200946908728072281189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3879467297939152048187459 5819200946908728072281189)
                    ·
                      refine ⟨1091100177545386513552723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5819200946908728072281189 1091100177545386513552723)
                      ·
                        rfl

theorem cell23_2124910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_2124910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124910 prefixEnd_2124910 := by exact prefixLift 2124910
  have htrace : WordTrace (prefixWord ++ tailWord_2124910) baseStart_2124910 baseEnd_2124910 := by
    simpa [prefixWord, tailWord_2124910, baseEnd_2124910] using wordTrace_append hprefix tailTrace_2124910
  have hstable : (prefixWord ++ tailWord_2124910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124910).length < 2 ^ (prefixWord ++ tailWord_2124910).sum := by decide
  have hdescent : baseEnd_2124910 < baseStart_2124910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124933 : List Nat := [1, 3, 1, 1, 7, 1, 9]
def baseStart_2124933 : Nat := 118140960795 + 2124933 * 2 ^ 59
def prefixEnd_2124933 : Nat := 4983230072969 + 3 ^ 40 * 2124933 * 2
def baseEnd_2124933 : Nat := 13470518365437529920557

theorem tailTrace_2124933 : CollatzResearch.WordTrace tailWord_2124933 prefixEnd_2124933 13470518365437529920557 := by
  unfold tailWord_2124933
  simp only [CollatzResearch.WordTrace]
  refine ⟨77502673610738125508795453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51668449073825417005863635 77502673610738125508795453)
  ·
    refine ⟨29063502604026797065798295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77502673610738125508795453 29063502604026797065798295)
    ·
      refine ⟨43595253906040195598697443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29063502604026797065798295 43595253906040195598697443)
      ·
        refine ⟨65392880859060293398046165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43595253906040195598697443 65392880859060293398046165)
        ·
          refine ⟨1532645645134225626516707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 65392880859060293398046165 1532645645134225626516707)
          ·
            refine ⟨2298968467701338439775061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1532645645134225626516707 2298968467701338439775061)
            ·
              refine ⟨13470518365437529920557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2298968467701338439775061 13470518365437529920557)
              ·
                rfl

theorem cell23_2124933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 9].length) (baseStart_2124933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124933 prefixEnd_2124933 := by exact prefixLift 2124933
  have htrace : WordTrace (prefixWord ++ tailWord_2124933) baseStart_2124933 baseEnd_2124933 := by
    simpa [prefixWord, tailWord_2124933, baseEnd_2124933] using wordTrace_append hprefix tailTrace_2124933
  have hstable : (prefixWord ++ tailWord_2124933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124933).length < 2 ^ (prefixWord ++ tailWord_2124933).sum := by decide
  have hdescent : baseEnd_2124933 < baseStart_2124933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2124960 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 2, 1, 3]
def baseStart_2124960 : Nat := 118140960795 + 2124960 * 2 ^ 59
def prefixEnd_2124960 : Nat := 4983230072969 + 3 ^ 40 * 2124960 * 2
def baseEnd_2124960 : Nat := 1091125851578111317927493

theorem tailTrace_2124960 : CollatzResearch.WordTrace tailWord_2124960 prefixEnd_2124960 1091125851578111317927493 := by
  unfold tailWord_2124960
  simp only [CollatzResearch.WordTrace]
  refine ⟨38751829190820154560014167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51669105587760206080018889 38751829190820154560014167)
  ·
    refine ⟨58127743786230231840021251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38751829190820154560014167 58127743786230231840021251)
    ·
      refine ⟨87191615679345347760031877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58127743786230231840021251 87191615679345347760031877)
      ·
        refine ⟨16348427939877252705005977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87191615679345347760031877 16348427939877252705005977)
        ·
          refine ⟨12261320954907939528754483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16348427939877252705005977 12261320954907939528754483)
          ·
            refine ⟨18391981432361909293131725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12261320954907939528754483 18391981432361909293131725)
            ·
              refine ⟨6896993037135715984924397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18391981432361909293131725 6896993037135715984924397)
              ·
                refine ⟨2586372388925893494346649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6896993037135715984924397 2586372388925893494346649)
                ·
                  refine ⟨1939779291694420120759987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2586372388925893494346649 1939779291694420120759987)
                  ·
                    refine ⟨2909668937541630181139981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1939779291694420120759987 2909668937541630181139981)
                    ·
                      refine ⟨1091125851578111317927493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2909668937541630181139981 1091125851578111317927493)
                      ·
                        rfl

theorem cell23_2124960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_2124960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2124960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2124960 prefixEnd_2124960 := by exact prefixLift 2124960
  have htrace : WordTrace (prefixWord ++ tailWord_2124960) baseStart_2124960 baseEnd_2124960 := by
    simpa [prefixWord, tailWord_2124960, baseEnd_2124960] using wordTrace_append hprefix tailTrace_2124960
  have hstable : (prefixWord ++ tailWord_2124960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2124960).length < 2 ^ (prefixWord ++ tailWord_2124960).sum := by decide
  have hdescent : baseEnd_2124960 < baseStart_2124960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2124960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125000 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 4, 2, 2]
def baseStart_2125000 : Nat := 118140960795 + 2125000 * 2 ^ 59
def prefixEnd_2125000 : Nat := 4983230072969 + 3 ^ 40 * 2125000 * 2
def baseEnd_2125000 : Nat := 1091146390804291161427309

theorem tailTrace_2125000 : CollatzResearch.WordTrace tailWord_2125000 prefixEnd_2125000 1091146390804291161427309 := by
  unfold tailWord_2125000
  simp only [CollatzResearch.WordTrace]
  refine ⟨38752558650747697975742227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51670078200996930634322969 38752558650747697975742227)
  ·
    refine ⟨58128837976121546963613341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38752558650747697975742227 58128837976121546963613341)
    ·
      refine ⟨21798314241045580111355003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58128837976121546963613341 21798314241045580111355003)
      ·
        refine ⟨32697471361568370167032505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21798314241045580111355003 32697471361568370167032505)
        ·
          refine ⟨24523103521176277625274379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32697471361568370167032505 24523103521176277625274379)
          ·
            refine ⟨36784655281764416437911569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24523103521176277625274379 36784655281764416437911569)
            ·
              refine ⟨27588491461323312328433677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36784655281764416437911569 27588491461323312328433677)
              ·
                refine ⟨10345684297996242123162629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27588491461323312328433677 10345684297996242123162629)
                ·
                  refine ⟨1939815805874295398092993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10345684297996242123162629 1939815805874295398092993)
                  ·
                    refine ⟨1454861854405721548569745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1939815805874295398092993 1454861854405721548569745)
                    ·
                      refine ⟨1091146390804291161427309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1454861854405721548569745 1091146390804291161427309)
                      ·
                        rfl

theorem cell23_2125000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_2125000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125000 prefixEnd_2125000 := by exact prefixLift 2125000
  have htrace : WordTrace (prefixWord ++ tailWord_2125000) baseStart_2125000 baseEnd_2125000 := by
    simpa [prefixWord, tailWord_2125000, baseEnd_2125000] using wordTrace_append hprefix tailTrace_2125000
  have hstable : (prefixWord ++ tailWord_2125000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125000).length < 2 ^ (prefixWord ++ tailWord_2125000).sum := by decide
  have hdescent : baseEnd_2125000 < baseStart_2125000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125013 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2125013 : Nat := 118140960795 + 2125013 * 2 ^ 59
def prefixEnd_2125013 : Nat := 4983230072969 + 3 ^ 40 * 2125013 * 2
def baseEnd_2125013 : Nat := 1091153066052799610564749

theorem tailTrace_2125013 : CollatzResearch.WordTrace tailWord_2125013 prefixEnd_2125013 1091153066052799610564749 := by
  unfold tailWord_2125013
  simp only [CollatzResearch.WordTrace]
  refine ⟨77505591450448299171707693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51670394300298866114471795 77505591450448299171707693)
  ·
    refine ⟨29064596793918112189390385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77505591450448299171707693 29064596793918112189390385)
    ·
      refine ⟨21798447595438584142042789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29064596793918112189390385 21798447595438584142042789)
      ·
        refine ⟨4087208924144734526633023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21798447595438584142042789 4087208924144734526633023)
        ·
          refine ⟨6130813386217101789949535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4087208924144734526633023 6130813386217101789949535)
          ·
            refine ⟨9196220079325652684924303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6130813386217101789949535 9196220079325652684924303)
            ·
              refine ⟨13794330118988479027386455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9196220079325652684924303 13794330118988479027386455)
              ·
                refine ⟨20691495178482718541079683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13794330118988479027386455 20691495178482718541079683)
                ·
                  refine ⟨31037242767724077811619525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20691495178482718541079683 31037242767724077811619525)
                  ·
                    refine ⟨5819483018948264589678661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31037242767724077811619525 5819483018948264589678661)
                    ·
                      refine ⟨1091153066052799610564749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5819483018948264589678661 1091153066052799610564749)
                      ·
                        rfl

theorem cell23_2125013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2125013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125013 prefixEnd_2125013 := by exact prefixLift 2125013
  have htrace : WordTrace (prefixWord ++ tailWord_2125013) baseStart_2125013 baseEnd_2125013 := by
    simpa [prefixWord, tailWord_2125013, baseEnd_2125013] using wordTrace_append hprefix tailTrace_2125013
  have hstable : (prefixWord ++ tailWord_2125013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125013).length < 2 ^ (prefixWord ++ tailWord_2125013).sum := by decide
  have hdescent : baseEnd_2125013 < baseStart_2125013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125163 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 4]
def baseStart_2125163 : Nat := 118140960795 + 2125163 * 2 ^ 59
def prefixEnd_2125163 : Nat := 4983230072969 + 3 ^ 40 * 2125163 * 2
def baseEnd_2125163 : Nat := 1091230088150974023689059

theorem tailTrace_2125163 : CollatzResearch.WordTrace tailWord_2125163 prefixEnd_2125163 1091230088150974023689059 := by
  unfold tailWord_2125163
  simp only [CollatzResearch.WordTrace]
  refine ⟨77511062399904874789668143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51674041599936583193112095 77511062399904874789668143)
  ·
    refine ⟨116266593599857312184502215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77511062399904874789668143 116266593599857312184502215)
    ·
      refine ⟨174399890399785968276753323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116266593599857312184502215 174399890399785968276753323)
      ·
        refine ⟨261599835599678952415129985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174399890399785968276753323 261599835599678952415129985)
        ·
          refine ⟨196199876699759214311347489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261599835599678952415129985 196199876699759214311347489)
          ·
            refine ⟨147149907524819410733510617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196199876699759214311347489 147149907524819410733510617)
            ·
              refine ⟨110362430643614558050132963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147149907524819410733510617 110362430643614558050132963)
              ·
                refine ⟨165543645965421837075199445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110362430643614558050132963 165543645965421837075199445)
                ·
                  refine ⟨3879929202314574306449987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 165543645965421837075199445 3879929202314574306449987)
                  ·
                    refine ⟨5819893803471861459674981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3879929202314574306449987 5819893803471861459674981)
                    ·
                      refine ⟨1091230088150974023689059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5819893803471861459674981 1091230088150974023689059)
                      ·
                        rfl

theorem cell23_2125163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 4].length) (baseStart_2125163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125163 prefixEnd_2125163 := by exact prefixLift 2125163
  have htrace : WordTrace (prefixWord ++ tailWord_2125163) baseStart_2125163 baseEnd_2125163 := by
    simpa [prefixWord, tailWord_2125163, baseEnd_2125163] using wordTrace_append hprefix tailTrace_2125163
  have hstable : (prefixWord ++ tailWord_2125163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125163).length < 2 ^ (prefixWord ++ tailWord_2125163).sum := by decide
  have hdescent : baseEnd_2125163 < baseStart_2125163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125183 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 3]
def baseStart_2125183 : Nat := 118140960795 + 2125183 * 2 ^ 59
def prefixEnd_2125183 : Nat := 4983230072969 + 3 ^ 40 * 2125183 * 2
def baseEnd_2125183 : Nat := 1091240357764063945438967

theorem tailTrace_2125183 : CollatzResearch.WordTrace tailWord_2125183 prefixEnd_2125183 1091240357764063945438967 := by
  unfold tailWord_2125183
  simp only [CollatzResearch.WordTrace]
  refine ⟨77511791859832418205396203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51674527906554945470264135 77511791859832418205396203)
  ·
    refine ⟨116267687789748627308094305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77511791859832418205396203 116267687789748627308094305)
    ·
      refine ⟨87200765842311470481070729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116267687789748627308094305 87200765842311470481070729)
      ·
        refine ⟨65400574381733602860803047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87200765842311470481070729 65400574381733602860803047)
        ·
          refine ⟨98100861572600404291204571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65400574381733602860803047 98100861572600404291204571)
          ·
            refine ⟨147151292358900606436806857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98100861572600404291204571 147151292358900606436806857)
            ·
              refine ⟨110363469269175454827605143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147151292358900606436806857 110363469269175454827605143)
              ·
                refine ⟨165545203903763182241407715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110363469269175454827605143 165545203903763182241407715)
                ·
                  refine ⟨248317805855644773362111573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165545203903763182241407715 248317805855644773362111573)
                  ·
                    refine ⟨2909974287370837187837245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 248317805855644773362111573 2909974287370837187837245)
                    ·
                      refine ⟨1091240357764063945438967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2909974287370837187837245 1091240357764063945438967)
                      ·
                        rfl

theorem cell23_2125183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_2125183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125183 prefixEnd_2125183 := by exact prefixLift 2125183
  have htrace : WordTrace (prefixWord ++ tailWord_2125183) baseStart_2125183 baseEnd_2125183 := by
    simpa [prefixWord, tailWord_2125183, baseEnd_2125183] using wordTrace_append hprefix tailTrace_2125183
  have hstable : (prefixWord ++ tailWord_2125183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125183).length < 2 ^ (prefixWord ++ tailWord_2125183).sum := by decide
  have hdescent : baseEnd_2125183 < baseStart_2125183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125210 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2125210 : Nat := 118140960795 + 2125210 * 2 ^ 59
def prefixEnd_2125210 : Nat := 4983230072969 + 3 ^ 40 * 2125210 * 2
def baseEnd_2125210 : Nat := 1091254221741735339801343

theorem tailTrace_2125210 : CollatzResearch.WordTrace tailWord_2125210 prefixEnd_2125210 1091254221741735339801343 := by
  unfold tailWord_2125210
  simp only [CollatzResearch.WordTrace]
  refine ⟨19378194157683650454157271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51675184420489734544419389 19378194157683650454157271)
  ·
    refine ⟨29067291236525475681235907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19378194157683650454157271 29067291236525475681235907)
    ·
      refine ⟨43600936854788213521853861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29067291236525475681235907 43600936854788213521853861)
      ·
        refine ⟨8175175660272790035347599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43600936854788213521853861 8175175660272790035347599)
        ·
          refine ⟨12262763490409185053021399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8175175660272790035347599 12262763490409185053021399)
          ·
            refine ⟨18394145235613777579532099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12262763490409185053021399 18394145235613777579532099)
            ·
              refine ⟨27591217853420666369298149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18394145235613777579532099 27591217853420666369298149)
              ·
                refine ⟨5173353347516374944243403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27591217853420666369298149 5173353347516374944243403)
                ·
                  refine ⟨7760030021274562416365105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5173353347516374944243403 7760030021274562416365105)
                  ·
                    refine ⟨5820022515955921812273829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7760030021274562416365105 5820022515955921812273829)
                    ·
                      refine ⟨1091254221741735339801343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5820022515955921812273829 1091254221741735339801343)
                      ·
                        rfl

theorem cell23_2125210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2125210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125210 prefixEnd_2125210 := by exact prefixLift 2125210
  have htrace : WordTrace (prefixWord ++ tailWord_2125210) baseStart_2125210 baseEnd_2125210 := by
    simpa [prefixWord, tailWord_2125210, baseEnd_2125210] using wordTrace_append hprefix tailTrace_2125210
  have hstable : (prefixWord ++ tailWord_2125210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125210).length < 2 ^ (prefixWord ++ tailWord_2125210).sum := by decide
  have hdescent : baseEnd_2125210 < baseStart_2125210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125224 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2125224 : Nat := 118140960795 + 2125224 * 2 ^ 59
def prefixEnd_2125224 : Nat := 4983230072969 + 3 ^ 40 * 2125224 * 2
def baseEnd_2125224 : Nat := 363753803490299428342093

theorem tailTrace_2125224 : CollatzResearch.WordTrace tailWord_2125224 prefixEnd_2125224 363753803490299428342093 := by
  unfold tailWord_2125224
  simp only [CollatzResearch.WordTrace]
  refine ⟨38756643626341941103819363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51675524835122588138425817 38756643626341941103819363)
  ·
    refine ⟨58134965439512911655729045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38756643626341941103819363 58134965439512911655729045)
    ·
      refine ⟨2725076504977167733862299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58134965439512911655729045 2725076504977167733862299)
      ·
        refine ⟨4087614757465751600793449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2725076504977167733862299 4087614757465751600793449)
        ·
          refine ⟨3065711068099313700595087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4087614757465751600793449 3065711068099313700595087)
          ·
            refine ⟨4598566602148970550892631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3065711068099313700595087 4598566602148970550892631)
            ·
              refine ⟨6897849903223455826338947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4598566602148970550892631 6897849903223455826338947)
              ·
                refine ⟨10346774854835183739508421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6897849903223455826338947 10346774854835183739508421)
                ·
                  refine ⟨1940020285281596951157829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10346774854835183739508421 1940020285281596951157829)
                  ·
                    refine ⟨363753803490299428342093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1940020285281596951157829 363753803490299428342093)
                    ·
                      rfl

theorem cell23_2125224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2125224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125224 prefixEnd_2125224 := by exact prefixLift 2125224
  have htrace : WordTrace (prefixWord ++ tailWord_2125224) baseStart_2125224 baseEnd_2125224 := by
    simpa [prefixWord, tailWord_2125224, baseEnd_2125224] using wordTrace_append hprefix tailTrace_2125224
  have hstable : (prefixWord ++ tailWord_2125224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125224).length < 2 ^ (prefixWord ++ tailWord_2125224).sum := by decide
  have hdescent : baseEnd_2125224 < baseStart_2125224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125244 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2125244 : Nat := 118140960795 + 2125244 * 2 ^ 59
def prefixEnd_2125244 : Nat := 4983230072969 + 3 ^ 40 * 2125244 * 2
def baseEnd_2125244 : Nat := 1091271680083988206776187

theorem tailTrace_2125244 : CollatzResearch.WordTrace tailWord_2125244 prefixEnd_2125244 1091271680083988206776187 := by
  unfold tailWord_2125244
  simp only [CollatzResearch.WordTrace]
  refine ⟨38757008356305712811683393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51676011141740950415577857 38757008356305712811683393)
  ·
    refine ⟨29067756267229284608762545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38757008356305712811683393 29067756267229284608762545)
    ·
      refine ⟨21800817200421963456571909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29067756267229284608762545 21800817200421963456571909)
      ·
        refine ⟨4087653225079118148107233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21800817200421963456571909 4087653225079118148107233)
        ·
          refine ⟨3065739918809338611080425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4087653225079118148107233 3065739918809338611080425)
          ·
            refine ⟨2299304939107003958310319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3065739918809338611080425 2299304939107003958310319)
            ·
              refine ⟨3448957408660505937465479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2299304939107003958310319 3448957408660505937465479)
              ·
                refine ⟨5173436112990758906198219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3448957408660505937465479 5173436112990758906198219)
                ·
                  refine ⟨7760154169486138359297329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5173436112990758906198219 7760154169486138359297329)
                  ·
                    refine ⟨5820115627114603769472997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7760154169486138359297329 5820115627114603769472997)
                    ·
                      refine ⟨1091271680083988206776187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5820115627114603769472997 1091271680083988206776187)
                      ·
                        rfl

theorem cell23_2125244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2125244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125244 prefixEnd_2125244 := by exact prefixLift 2125244
  have htrace : WordTrace (prefixWord ++ tailWord_2125244) baseStart_2125244 baseEnd_2125244 := by
    simpa [prefixWord, tailWord_2125244, baseEnd_2125244] using wordTrace_append hprefix tailTrace_2125244
  have hstable : (prefixWord ++ tailWord_2125244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125244).length < 2 ^ (prefixWord ++ tailWord_2125244).sum := by decide
  have hdescent : baseEnd_2125244 < baseStart_2125244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125247 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 2, 1, 3]
def baseStart_2125247 : Nat := 118140960795 + 2125247 * 2 ^ 59
def prefixEnd_2125247 : Nat := 4983230072969 + 3 ^ 40 * 2125247 * 2
def baseEnd_2125247 : Nat := 1091273220525951695038673

theorem tailTrace_2125247 : CollatzResearch.WordTrace tailWord_2125247 prefixEnd_2125247 1091273220525951695038673 := by
  unfold tailWord_2125247
  simp only [CollatzResearch.WordTrace]
  refine ⟨77514126131600557135725995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51676084087733704757150663 77514126131600557135725995)
  ·
    refine ⟨116271189197400835703588993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77514126131600557135725995 116271189197400835703588993)
    ·
      refine ⟨87203391898050626777691745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116271189197400835703588993 87203391898050626777691745)
      ·
        refine ⟨65402543923537970083268809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87203391898050626777691745 65402543923537970083268809)
        ·
          refine ⟨49051907942653477562451607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65402543923537970083268809 49051907942653477562451607)
          ·
            refine ⟨73577861913980216343677411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49051907942653477562451607 73577861913980216343677411)
            ·
              refine ⟨110366792870970324515516117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73577861913980216343677411 110366792870970324515516117)
              ·
                refine ⟨2586721707913366980832409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 110366792870970324515516117 2586721707913366980832409)
                ·
                  refine ⟨1940041280935025235624307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2586721707913366980832409 1940041280935025235624307)
                  ·
                    refine ⟨2910061921402537853436461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1940041280935025235624307 2910061921402537853436461)
                    ·
                      refine ⟨1091273220525951695038673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2910061921402537853436461 1091273220525951695038673)
                      ·
                        rfl

theorem cell23_2125247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_2125247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125247 prefixEnd_2125247 := by exact prefixLift 2125247
  have htrace : WordTrace (prefixWord ++ tailWord_2125247) baseStart_2125247 baseEnd_2125247 := by
    simpa [prefixWord, tailWord_2125247, baseEnd_2125247] using wordTrace_append hprefix tailTrace_2125247
  have hstable : (prefixWord ++ tailWord_2125247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125247).length < 2 ^ (prefixWord ++ tailWord_2125247).sum := by decide
  have hdescent : baseEnd_2125247 < baseStart_2125247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125260 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2125260 : Nat := 118140960795 + 2125260 * 2 ^ 59
def prefixEnd_2125260 : Nat := 4983230072969 + 3 ^ 40 * 2125260 * 2
def baseEnd_2125260 : Nat := 1091279895774460144176113

theorem tailTrace_2125260 : CollatzResearch.WordTrace tailWord_2125260 prefixEnd_2125260 1091279895774460144176113 := by
  unfold tailWord_2125260
  simp only [CollatzResearch.WordTrace]
  refine ⟨38757300140276730177974617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51676400187035640237299489 38757300140276730177974617)
  ·
    refine ⟨29067975105207547633480963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38757300140276730177974617 29067975105207547633480963)
    ·
      refine ⟨43601962657811321450221445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29067975105207547633480963 43601962657811321450221445)
      ·
        refine ⟨8175367998339622771916521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43601962657811321450221445 8175367998339622771916521)
        ·
          refine ⟨6131525998754717078937391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8175367998339622771916521 6131525998754717078937391)
          ·
            refine ⟨9197288998132075618406087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6131525998754717078937391 9197288998132075618406087)
            ·
              refine ⟨13795933497198113427609131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9197288998132075618406087 13795933497198113427609131)
              ·
                refine ⟨20693900245797170141413697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13795933497198113427609131 20693900245797170141413697)
                ·
                  refine ⟨15520425184347877606060273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20693900245797170141413697 15520425184347877606060273)
                  ·
                    refine ⟨11640318888260908204545205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15520425184347877606060273 11640318888260908204545205)
                    ·
                      refine ⟨1091279895774460144176113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11640318888260908204545205 1091279895774460144176113)
                      ·
                        rfl

theorem cell23_2125260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2125260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125260 prefixEnd_2125260 := by exact prefixLift 2125260
  have htrace : WordTrace (prefixWord ++ tailWord_2125260) baseStart_2125260 baseEnd_2125260 := by
    simpa [prefixWord, tailWord_2125260, baseEnd_2125260] using wordTrace_append hprefix tailTrace_2125260
  have hstable : (prefixWord ++ tailWord_2125260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125260).length < 2 ^ (prefixWord ++ tailWord_2125260).sum := by decide
  have hdescent : baseEnd_2125260 < baseStart_2125260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125263 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 1, 8]
def baseStart_2125263 : Nat := 118140960795 + 2125263 * 2 ^ 59
def prefixEnd_2125263 : Nat := 4983230072969 + 3 ^ 40 * 2125263 * 2
def baseEnd_2125263 : Nat := 363760478738807877479533

theorem tailTrace_2125263 : CollatzResearch.WordTrace tailWord_2125263 prefixEnd_2125263 363760478738807877479533 := by
  unfold tailWord_2125263
  simp only [CollatzResearch.WordTrace]
  refine ⟨77514709699542591868308443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51676473133028394578872295 77514709699542591868308443)
  ·
    refine ⟨116272064549313887802462665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77514709699542591868308443 116272064549313887802462665)
    ·
      refine ⟨87204048411985415851846999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116272064549313887802462665 87204048411985415851846999)
      ·
        refine ⟨130806072617978123777770499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87204048411985415851846999 130806072617978123777770499)
        ·
          refine ⟨196209108926967185666655749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130806072617978123777770499 196209108926967185666655749)
          ·
            refine ⟨36789207923806347312497953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196209108926967185666655749 36789207923806347312497953)
            ·
              refine ⟨27591905942854760484373465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36789207923806347312497953 27591905942854760484373465)
              ·
                refine ⟨20693929457141070363280099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27591905942854760484373465 20693929457141070363280099)
                ·
                  refine ⟨31040894185711605544920149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20693929457141070363280099 31040894185711605544920149)
                  ·
                    refine ⟨363760478738807877479533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31040894185711605544920149 363760478738807877479533)
                    ·
                      rfl

theorem cell23_2125263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_2125263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125263 prefixEnd_2125263 := by exact prefixLift 2125263
  have htrace : WordTrace (prefixWord ++ tailWord_2125263) baseStart_2125263 baseEnd_2125263 := by
    simpa [prefixWord, tailWord_2125263, baseEnd_2125263] using wordTrace_append hprefix tailTrace_2125263
  have hstable : (prefixWord ++ tailWord_2125263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125263).length < 2 ^ (prefixWord ++ tailWord_2125263).sum := by decide
  have hdescent : baseEnd_2125263 < baseStart_2125263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125274 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2]
def baseStart_2125274 : Nat := 118140960795 + 2125274 * 2 ^ 59
def prefixEnd_2125274 : Nat := 4983230072969 + 3 ^ 40 * 2125274 * 2
def baseEnd_2125274 : Nat := 1091287084503623089401049

theorem tailTrace_2125274 : CollatzResearch.WordTrace tailWord_2125274 prefixEnd_2125274 1091287084503623089401049 := by
  unfold tailWord_2125274
  simp only [CollatzResearch.WordTrace]
  refine ⟨19378777725625685186739719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51676740601668493831305917 19378777725625685186739719)
  ·
    refine ⟨29068166588438527780109579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19378777725625685186739719 29068166588438527780109579)
    ·
      refine ⟨43602249882657791670164369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29068166588438527780109579 43602249882657791670164369)
      ·
        refine ⟨32701687411993343752623277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43602249882657791670164369 32701687411993343752623277)
        ·
          refine ⟨12263132779497503907233729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32701687411993343752623277 12263132779497503907233729)
          ·
            refine ⟨9197349584623127930425297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12263132779497503907233729 9197349584623127930425297)
            ·
              refine ⟨6898012188467345947818973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9197349584623127930425297 6898012188467345947818973)
              ·
                refine ⟨2586754570675254730432115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6898012188467345947818973 2586754570675254730432115)
                ·
                  refine ⟨3880131856012882095648173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2586754570675254730432115 3880131856012882095648173)
                  ·
                    refine ⟨1455049446004830785868065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3880131856012882095648173 1455049446004830785868065)
                    ·
                      refine ⟨1091287084503623089401049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1455049446004830785868065 1091287084503623089401049)
                      ·
                        rfl

theorem cell23_2125274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_2125274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125274 prefixEnd_2125274 := by exact prefixLift 2125274
  have htrace : WordTrace (prefixWord ++ tailWord_2125274) baseStart_2125274 baseEnd_2125274 := by
    simpa [prefixWord, tailWord_2125274, baseEnd_2125274] using wordTrace_append hprefix tailTrace_2125274
  have hstable : (prefixWord ++ tailWord_2125274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125274).length < 2 ^ (prefixWord ++ tailWord_2125274).sum := by decide
  have hdescent : baseEnd_2125274 < baseStart_2125274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125298 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 2, 1, 3]
def baseStart_2125298 : Nat := 118140960795 + 2125298 * 2 ^ 59
def prefixEnd_2125298 : Nat := 4983230072969 + 3 ^ 40 * 2125298 * 2
def baseEnd_2125298 : Nat := 1091299408039330995500939

theorem tailTrace_2125298 : CollatzResearch.WordTrace tailWord_2125298 prefixEnd_2125298 1091299408039330995500939 := by
  unfold tailWord_2125298
  simp only [CollatzResearch.WordTrace]
  refine ⟨19378996563603948211458137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51677324169610528563888365 19378996563603948211458137)
  ·
    refine ⟨14534247422702961158593603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19378996563603948211458137 14534247422702961158593603)
    ·
      refine ⟨21801371134054441737890405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14534247422702961158593603 21801371134054441737890405)
      ·
        refine ⟨4087757087635207825854451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21801371134054441737890405 4087757087635207825854451)
        ·
          refine ⟨6131635631452811738781677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4087757087635207825854451 6131635631452811738781677)
          ·
            refine ⟨2299363361794804402043129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6131635631452811738781677 2299363361794804402043129)
            ·
              refine ⟨1724522521346103301532347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2299363361794804402043129 1724522521346103301532347)
              ·
                refine ⟨2586783782019154952298521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724522521346103301532347 2586783782019154952298521)
                ·
                  refine ⟨1940087836514366214223891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2586783782019154952298521 1940087836514366214223891)
                  ·
                    refine ⟨2910131754771549321335837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1940087836514366214223891 2910131754771549321335837)
                    ·
                      refine ⟨1091299408039330995500939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2910131754771549321335837 1091299408039330995500939)
                      ·
                        rfl

theorem cell23_2125298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_2125298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125298 prefixEnd_2125298 := by exact prefixLift 2125298
  have htrace : WordTrace (prefixWord ++ tailWord_2125298) baseStart_2125298 baseEnd_2125298 := by
    simpa [prefixWord, tailWord_2125298, baseEnd_2125298] using wordTrace_append hprefix tailTrace_2125298
  have hstable : (prefixWord ++ tailWord_2125298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125298).length < 2 ^ (prefixWord ++ tailWord_2125298).sum := by decide
  have hdescent : baseEnd_2125298 < baseStart_2125298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125344 : List Nat := [2, 1, 1, 6, 1, 2, 1, 4, 5]
def baseStart_2125344 : Nat := 118140960795 + 2125344 * 2 ^ 59
def prefixEnd_2125344 : Nat := 4983230072969 + 3 ^ 40 * 2125344 * 2
def baseEnd_2125344 : Nat := 121258114238826423947303

theorem tailTrace_2125344 : CollatzResearch.WordTrace tailWord_2125344 prefixEnd_2125344 121258114238826423947303 := by
  unfold tailWord_2125344
  simp only [CollatzResearch.WordTrace]
  refine ⟨38758832006124571351003543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51678442674832761801338057 38758832006124571351003543)
  ·
    refine ⟨58138248009186857026505315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38758832006124571351003543 58138248009186857026505315)
    ·
      refine ⟨87207372013780285539757973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58138248009186857026505315 87207372013780285539757973)
      ·
        refine ⟨4087845563145950884676155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 87207372013780285539757973 4087845563145950884676155)
        ·
          refine ⟨6131768344718926327014233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4087845563145950884676155 6131768344718926327014233)
          ·
            refine ⟨4598826258539194745260675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6131768344718926327014233 4598826258539194745260675)
            ·
              refine ⟨6898239387808792117891013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4598826258539194745260675 6898239387808792117891013)
              ·
                refine ⟨1293419885214148522104565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6898239387808792117891013 1293419885214148522104565)
                ·
                  refine ⟨121258114238826423947303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1293419885214148522104565 121258114238826423947303)
                  ·
                    rfl

theorem cell23_2125344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 5].length) (baseStart_2125344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125344 prefixEnd_2125344 := by exact prefixLift 2125344
  have htrace : WordTrace (prefixWord ++ tailWord_2125344) baseStart_2125344 baseEnd_2125344 := by
    simpa [prefixWord, tailWord_2125344, baseEnd_2125344] using wordTrace_append hprefix tailTrace_2125344
  have hstable : (prefixWord ++ tailWord_2125344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125344).length < 2 ^ (prefixWord ++ tailWord_2125344).sum := by decide
  have hdescent : baseEnd_2125344 < baseStart_2125344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125360 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 4]
def baseStart_2125360 : Nat := 118140960795 + 2125360 * 2 ^ 59
def prefixEnd_2125360 : Nat := 4983230072969 + 3 ^ 40 * 2125360 * 2
def baseEnd_2125360 : Nat := 1091331243839909752925653

theorem tailTrace_2125360 : CollatzResearch.WordTrace tailWord_2125360 prefixEnd_2125360 1091331243839909752925653 := by
  unfold tailWord_2125360
  simp only [CollatzResearch.WordTrace]
  refine ⟨38759123790095588717294767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51678831720127451623059689 38759123790095588717294767)
  ·
    refine ⟨58138685685143383075942151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38759123790095588717294767 58138685685143383075942151)
    ·
      refine ⟨87208028527715074613913227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58138685685143383075942151 87208028527715074613913227)
      ·
        refine ⟨130812042791572611920869841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87208028527715074613913227 130812042791572611920869841)
        ·
          refine ⟨98109032093679458940652381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130812042791572611920869841 98109032093679458940652381)
          ·
            refine ⟨36790887035129797102744643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98109032093679458940652381 36790887035129797102744643)
            ·
              refine ⟨55186330552694695654116965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36790887035129797102744643 55186330552694695654116965)
              ·
                refine ⟨10347436978630255435146931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55186330552694695654116965 10347436978630255435146931)
                ·
                  refine ⟨15521155467945383152720397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10347436978630255435146931 15521155467945383152720397)
                  ·
                    refine ⟨5820433300479518682270149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15521155467945383152720397 5820433300479518682270149)
                    ·
                      refine ⟨1091331243839909752925653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5820433300479518682270149 1091331243839909752925653)
                      ·
                        rfl

theorem cell23_2125360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_2125360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125360 prefixEnd_2125360 := by exact prefixLift 2125360
  have htrace : WordTrace (prefixWord ++ tailWord_2125360) baseStart_2125360 baseEnd_2125360 := by
    simpa [prefixWord, tailWord_2125360, baseEnd_2125360] using wordTrace_append hprefix tailTrace_2125360
  have hstable : (prefixWord ++ tailWord_2125360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125360).length < 2 ^ (prefixWord ++ tailWord_2125360).sum := by decide
  have hdescent : baseEnd_2125360 < baseStart_2125360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125377 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2125377 : Nat := 118140960795 + 2125377 * 2 ^ 59
def prefixEnd_2125377 : Nat := 4983230072969 + 3 ^ 40 * 2125377 * 2
def baseEnd_2125377 : Nat := 1091339973011036186413075

theorem tailTrace_2125377 : CollatzResearch.WordTrace tailWord_2125377 prefixEnd_2125377 1091339973011036186413075 := by
  unfold tailWord_2125377
  simp only [CollatzResearch.WordTrace]
  refine ⟨77518867621129589337958385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51679245080753059558638923 77518867621129589337958385)
  ·
    refine ⟨58139150715847192003468789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77518867621129589337958385 58139150715847192003468789)
    ·
      refine ⟨5450545379610674250325199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58139150715847192003468789 5450545379610674250325199)
      ·
        refine ⟨8175818069416011375487799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5450545379610674250325199 8175818069416011375487799)
        ·
          refine ⟨12263727104124017063231699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8175818069416011375487799 12263727104124017063231699)
          ·
            refine ⟨18395590656186025594847549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12263727104124017063231699 18395590656186025594847549)
            ·
              refine ⟨6898346496069759598067831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18395590656186025594847549 6898346496069759598067831)
              ·
                refine ⟨10347519744104639397101747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6898346496069759598067831 10347519744104639397101747)
                ·
                  refine ⟨15521279616156959095652621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10347519744104639397101747 15521279616156959095652621)
                  ·
                    refine ⟨5820479856058859660869733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15521279616156959095652621 5820479856058859660869733)
                    ·
                      refine ⟨1091339973011036186413075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5820479856058859660869733 1091339973011036186413075)
                      ·
                        rfl

theorem cell23_2125377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2125377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125377 prefixEnd_2125377 := by exact prefixLift 2125377
  have htrace : WordTrace (prefixWord ++ tailWord_2125377) baseStart_2125377 baseEnd_2125377 := by
    simpa [prefixWord, tailWord_2125377, baseEnd_2125377] using wordTrace_append hprefix tailTrace_2125377
  have hstable : (prefixWord ++ tailWord_2125377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125377).length < 2 ^ (prefixWord ++ tailWord_2125377).sum := by decide
  have hdescent : baseEnd_2125377 < baseStart_2125377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125394 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_2125394 : Nat := 118140960795 + 2125394 * 2 ^ 59
def prefixEnd_2125394 : Nat := 4983230072969 + 3 ^ 40 * 2125394 * 2
def baseEnd_2125394 : Nat := 1091348702182162619900497

theorem tailTrace_2125394 : CollatzResearch.WordTrace tailWord_2125394 prefixEnd_2125394 1091348702182162619900497 := by
  unfold tailWord_2125394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19379871915517000310331809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51679658441378667494218157 19379871915517000310331809)
  ·
    refine ⟨14534903936637750232748857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19379871915517000310331809 14534903936637750232748857)
    ·
      refine ⟨10901177952478312674561643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14534903936637750232748857 10901177952478312674561643)
      ·
        refine ⟨16351766928717469011842465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10901177952478312674561643 16351766928717469011842465)
        ·
          refine ⟨12263825196538101758881849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16351766928717469011842465 12263825196538101758881849)
          ·
            refine ⟨9197868897403576319161387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12263825196538101758881849 9197868897403576319161387)
            ·
              refine ⟨13796803346105364478742081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9197868897403576319161387 13796803346105364478742081)
              ·
                refine ⟨10347602509579023359056561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13796803346105364478742081 10347602509579023359056561)
                ·
                  refine ⟨7760701882184267519292421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10347602509579023359056561 7760701882184267519292421)
                  ·
                    refine ⟨1455131602909550159867329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7760701882184267519292421 1455131602909550159867329)
                    ·
                      refine ⟨1091348702182162619900497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1455131602909550159867329 1091348702182162619900497)
                      ·
                        rfl

theorem cell23_2125394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_2125394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125394 prefixEnd_2125394 := by exact prefixLift 2125394
  have htrace : WordTrace (prefixWord ++ tailWord_2125394) baseStart_2125394 baseEnd_2125394 := by
    simpa [prefixWord, tailWord_2125394, baseEnd_2125394] using wordTrace_append hprefix tailTrace_2125394
  have hstable : (prefixWord ++ tailWord_2125394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125394).length < 2 ^ (prefixWord ++ tailWord_2125394).sum := by decide
  have hdescent : baseEnd_2125394 < baseStart_2125394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125397 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_2125397 : Nat := 118140960795 + 2125397 * 2 ^ 59
def prefixEnd_2125397 : Nat := 4983230072969 + 3 ^ 40 * 2125397 * 2
def baseEnd_2125397 : Nat := 1091350242624126108162983

theorem tailTrace_2125397 : CollatzResearch.WordTrace tailWord_2125397 prefixEnd_2125397 1091350242624126108162983 := by
  unfold tailWord_2125397
  simp only [CollatzResearch.WordTrace]
  refine ⟨77519597081057132753686445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51679731387371421835790963 77519597081057132753686445)
  ·
    refine ⟨29069848905396424782632417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77519597081057132753686445 29069848905396424782632417)
    ·
      refine ⟨21802386679047318586974313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29069848905396424782632417 21802386679047318586974313)
      ·
        refine ⟨16351790009285488940230735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21802386679047318586974313 16351790009285488940230735)
        ·
          refine ⟨24527685013928233410346103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16351790009285488940230735 24527685013928233410346103)
          ·
            refine ⟨36791527520892350115519155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24527685013928233410346103 36791527520892350115519155)
            ·
              refine ⟨55187291281338525173278733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36791527520892350115519155 55187291281338525173278733)
              ·
                refine ⟨20695234230501946939979525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55187291281338525173278733 20695234230501946939979525)
                ·
                  refine ⟨3880356418219115051246161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20695234230501946939979525 3880356418219115051246161)
                  ·
                    refine ⟨2910267313664336288434621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3880356418219115051246161 2910267313664336288434621)
                    ·
                      refine ⟨1091350242624126108162983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2910267313664336288434621 1091350242624126108162983)
                      ·
                        rfl

theorem cell23_2125397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_2125397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125397 prefixEnd_2125397 := by exact prefixLift 2125397
  have htrace : WordTrace (prefixWord ++ tailWord_2125397) baseStart_2125397 baseEnd_2125397 := by
    simpa [prefixWord, tailWord_2125397, baseEnd_2125397] using wordTrace_append hprefix tailTrace_2125397
  have hstable : (prefixWord ++ tailWord_2125397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125397).length < 2 ^ (prefixWord ++ tailWord_2125397).sum := by decide
  have hdescent : baseEnd_2125397 < baseStart_2125397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125404 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 3, 4]
def baseStart_2125404 : Nat := 118140960795 + 2125404 * 2 ^ 59
def prefixEnd_2125404 : Nat := 4983230072969 + 3 ^ 40 * 2125404 * 2
def baseEnd_2125404 : Nat := 363784612329569193591817

theorem tailTrace_2125404 : CollatzResearch.WordTrace tailWord_2125404 prefixEnd_2125404 363784612329569193591817 := by
  unfold tailWord_2125404
  simp only [CollatzResearch.WordTrace]
  refine ⟨38759926196015886474595633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51679901594687848632794177 38759926196015886474595633)
  ·
    refine ⟨29069944647011914855946725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38759926196015886474595633 29069944647011914855946725)
    ·
      refine ⟨5450614621314734035490011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29069944647011914855946725 5450614621314734035490011)
      ·
        refine ⟨8175921931972101053235017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5450614621314734035490011 8175921931972101053235017)
        ·
          refine ⟨6131941448979075789926263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8175921931972101053235017 6131941448979075789926263)
          ·
            refine ⟨9197912173468613684889395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6131941448979075789926263 9197912173468613684889395)
            ·
              refine ⟨13796868260202920527334093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9197912173468613684889395 13796868260202920527334093)
              ·
                refine ⟨5173825597576095197750285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13796868260202920527334093 5173825597576095197750285)
                ·
                  refine ⟨1940184599091035699156357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5173825597576095197750285 1940184599091035699156357)
                  ·
                    refine ⟨363784612329569193591817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1940184599091035699156357 363784612329569193591817)
                    ·
                      rfl

theorem cell23_2125404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_2125404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125404 prefixEnd_2125404 := by exact prefixLift 2125404
  have htrace : WordTrace (prefixWord ++ tailWord_2125404) baseStart_2125404 baseEnd_2125404 := by
    simpa [prefixWord, tailWord_2125404, baseEnd_2125404] using wordTrace_append hprefix tailTrace_2125404
  have hstable : (prefixWord ++ tailWord_2125404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125404).length < 2 ^ (prefixWord ++ tailWord_2125404).sum := by decide
  have hdescent : baseEnd_2125404 < baseStart_2125404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125420 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_2125420 : Nat := 118140960795 + 2125420 * 2 ^ 59
def prefixEnd_2125420 : Nat := 4983230072969 + 3 ^ 40 * 2125420 * 2
def baseEnd_2125420 : Nat := 1091362052679179518175377

theorem tailTrace_2125420 : CollatzResearch.WordTrace tailWord_2125420 prefixEnd_2125420 1091362052679179518175377 := by
  unfold tailWord_2125420
  simp only [CollatzResearch.WordTrace]
  refine ⟨38760217979986903840886857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51680290639982538454515809 38760217979986903840886857)
  ·
    refine ⟨29070163484990177880665143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38760217979986903840886857 29070163484990177880665143)
    ·
      refine ⟨43605245227485266820997715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29070163484990177880665143 43605245227485266820997715)
      ·
        refine ⟨65407867841227900231496573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43605245227485266820997715 65407867841227900231496573)
        ·
          refine ⟨24527950440460462586811215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65407867841227900231496573 24527950440460462586811215)
          ·
            refine ⟨36791925660690693880216823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24527950440460462586811215 36791925660690693880216823)
            ·
              refine ⟨55187888491036040820325235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36791925660690693880216823 55187888491036040820325235)
              ·
                refine ⟨82781832736554061230487853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55187888491036040820325235 82781832736554061230487853)
                ·
                  refine ⟨31043187276207772961432945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82781832736554061230487853 31043187276207772961432945)
                  ·
                    refine ⟨23282390457155829721074709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31043187276207772961432945 23282390457155829721074709)
                    ·
                      refine ⟨1091362052679179518175377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23282390457155829721074709 1091362052679179518175377)
                      ·
                        rfl

theorem cell23_2125420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_2125420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125420 prefixEnd_2125420 := by exact prefixLift 2125420
  have htrace : WordTrace (prefixWord ++ tailWord_2125420) baseStart_2125420 baseEnd_2125420 := by
    simpa [prefixWord, tailWord_2125420, baseEnd_2125420] using wordTrace_append hprefix tailTrace_2125420
  have hstable : (prefixWord ++ tailWord_2125420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125420).length < 2 ^ (prefixWord ++ tailWord_2125420).sum := by decide
  have hdescent : baseEnd_2125420 < baseStart_2125420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125461 : List Nat := [1, 3, 2, 1, 1, 1, 1, 8, 1, 1, 3]
def baseStart_2125461 : Nat := 118140960795 + 2125461 * 2 ^ 59
def prefixEnd_2125461 : Nat := 4983230072969 + 3 ^ 40 * 2125461 * 2
def baseEnd_2125461 : Nat := 1091383105386013857762689

theorem tailTrace_2125461 : CollatzResearch.WordTrace tailWord_2125461 prefixEnd_2125461 1091383105386013857762689 := by
  unfold tailWord_2125461
  simp only [CollatzResearch.WordTrace]
  refine ⟨77521931352825271684016237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51681287568550181122677491 77521931352825271684016237)
  ·
    refine ⟨29070724257309476881506089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77521931352825271684016237 29070724257309476881506089)
    ·
      refine ⟨21803043192982107661129567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29070724257309476881506089 21803043192982107661129567)
      ·
        refine ⟨32704564789473161491694351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21803043192982107661129567 32704564789473161491694351)
        ·
          refine ⟨49056847184209742237541527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32704564789473161491694351 49056847184209742237541527)
          ·
            refine ⟨73585270776314613356312291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49056847184209742237541527 73585270776314613356312291)
            ·
              refine ⟨110377906164471920034468437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73585270776314613356312291 110377906164471920034468437)
              ·
                refine ⟨1293491087864905312903927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 110377906164471920034468437 1293491087864905312903927)
                ·
                  refine ⟨1940236631797357969355891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293491087864905312903927 1940236631797357969355891)
                  ·
                    refine ⟨2910354947696036954033837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1940236631797357969355891 2910354947696036954033837)
                    ·
                      refine ⟨1091383105386013857762689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2910354947696036954033837 1091383105386013857762689)
                      ·
                        rfl

theorem cell23_2125461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_2125461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125461 prefixEnd_2125461 := by exact prefixLift 2125461
  have htrace : WordTrace (prefixWord ++ tailWord_2125461) baseStart_2125461 baseEnd_2125461 := by
    simpa [prefixWord, tailWord_2125461, baseEnd_2125461] using wordTrace_append hprefix tailTrace_2125461
  have hstable : (prefixWord ++ tailWord_2125461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125461).length < 2 ^ (prefixWord ++ tailWord_2125461).sum := by decide
  have hdescent : baseEnd_2125461 < baseStart_2125461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125468 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 6]
def baseStart_2125468 : Nat := 118140960795 + 2125468 * 2 ^ 59
def prefixEnd_2125468 : Nat := 4983230072969 + 3 ^ 40 * 2125468 * 2
def baseEnd_2125468 : Nat := 121265188861177258930573

theorem tailTrace_2125468 : CollatzResearch.WordTrace tailWord_2125468 prefixEnd_2125468 121265188861177258930573 := by
  unfold tailWord_2125468
  simp only [CollatzResearch.WordTrace]
  refine ⟨38761093331899955939760529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51681457775866607919680705 38761093331899955939760529)
  ·
    refine ⟨29070819998924966954820397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38761093331899955939760529 29070819998924966954820397)
    ·
      refine ⟨10901557499596862608057649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29070819998924966954820397 10901557499596862608057649)
      ·
        refine ⟨8176168124697646956043237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10901557499596862608057649 8176168124697646956043237)
        ·
          refine ⟨1533031523380808804258107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8176168124697646956043237 1533031523380808804258107)
          ·
            refine ⟨2299547285071213206387161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533031523380808804258107 2299547285071213206387161)
            ·
              refine ⟨1724660463803409904790371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2299547285071213206387161 1724660463803409904790371)
              ·
                refine ⟨2586990695705114857185557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724660463803409904790371 2586990695705114857185557)
                ·
                  refine ⟨121265188861177258930573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2586990695705114857185557 121265188861177258930573)
                  ·
                    rfl

theorem cell23_2125468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_2125468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125468 prefixEnd_2125468 := by exact prefixLift 2125468
  have htrace : WordTrace (prefixWord ++ tailWord_2125468) baseStart_2125468 baseEnd_2125468 := by
    simpa [prefixWord, tailWord_2125468, baseEnd_2125468] using wordTrace_append hprefix tailTrace_2125468
  have hstable : (prefixWord ++ tailWord_2125468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125468).length < 2 ^ (prefixWord ++ tailWord_2125468).sum := by decide
  have hdescent : baseEnd_2125468 < baseStart_2125468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125497 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2125497 : Nat := 118140960795 + 2125497 * 2 ^ 59
def prefixEnd_2125497 : Nat := 4983230072969 + 3 ^ 40 * 2125497 * 2
def baseEnd_2125497 : Nat := 1091401590689575716912523

theorem tailTrace_2125497 : CollatzResearch.WordTrace tailWord_2125497 prefixEnd_2125497 1091401590689575716912523 := by
  unfold tailWord_2125497
  simp only [CollatzResearch.WordTrace]
  refine ⟨77523244380694849832326745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51682162920463233221551163 77523244380694849832326745)
  ·
    refine ⟨58142433285521137374245059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77523244380694849832326745 58142433285521137374245059)
    ·
      refine ⟨87213649928281706061367589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58142433285521137374245059 87213649928281706061367589)
      ·
        refine ⟨16352559361552819886506423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87213649928281706061367589 16352559361552819886506423)
        ·
          refine ⟨24528839042329229829759635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16352559361552819886506423 24528839042329229829759635)
          ·
            refine ⟨36793258563493844744639453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24528839042329229829759635 36793258563493844744639453)
            ·
              refine ⟨13797471961310191779239795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36793258563493844744639453 13797471961310191779239795)
              ·
                refine ⟨20696207941965287668859693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13797471961310191779239795 20696207941965287668859693)
                ·
                  refine ⟨7761077978236982875822385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20696207941965287668859693 7761077978236982875822385)
                  ·
                    refine ⟨5820808483677737156866789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7761077978236982875822385 5820808483677737156866789)
                    ·
                      refine ⟨1091401590689575716912523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5820808483677737156866789 1091401590689575716912523)
                      ·
                        rfl

theorem cell23_2125497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2125497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125497 prefixEnd_2125497 := by exact prefixLift 2125497
  have htrace : WordTrace (prefixWord ++ tailWord_2125497) baseStart_2125497 baseEnd_2125497 := by
    simpa [prefixWord, tailWord_2125497, baseEnd_2125497] using wordTrace_append hprefix tailTrace_2125497
  have hstable : (prefixWord ++ tailWord_2125497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125497).length < 2 ^ (prefixWord ++ tailWord_2125497).sum := by decide
  have hdescent : baseEnd_2125497 < baseStart_2125497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125501 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 1, 1, 4]
def baseStart_2125501 : Nat := 118140960795 + 2125501 * 2 ^ 59
def prefixEnd_2125501 : Nat := 4983230072969 + 3 ^ 40 * 2125501 * 2
def baseEnd_2125501 : Nat := 1091403644612193701262505

theorem tailTrace_2125501 : CollatzResearch.WordTrace tailWord_2125501 prefixEnd_2125501 1091403644612193701262505 := by
  unfold tailWord_2125501
  simp only [CollatzResearch.WordTrace]
  refine ⟨77523390272680358515472357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51682260181786905676981571 77523390272680358515472357)
  ·
    refine ⟨14535635676127567221651067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77523390272680358515472357 14535635676127567221651067)
    ·
      refine ⟨21803453514191350832476601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14535635676127567221651067 21803453514191350832476601)
      ·
        refine ⟨16352590135643513124357451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21803453514191350832476601 16352590135643513124357451)
        ·
          refine ⟨24528885203465269686536177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16352590135643513124357451 24528885203465269686536177)
          ·
            refine ⟨18396663902598952264902133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24528885203465269686536177 18396663902598952264902133)
            ·
              refine ⟨1724687240868651774834575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18396663902598952264902133 1724687240868651774834575)
              ·
                refine ⟨2587030861302977662251863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1724687240868651774834575 2587030861302977662251863)
                ·
                  refine ⟨3880546291954466493377795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587030861302977662251863 3880546291954466493377795)
                  ·
                    refine ⟨5820819437931699740066693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3880546291954466493377795 5820819437931699740066693)
                    ·
                      refine ⟨1091403644612193701262505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5820819437931699740066693 1091403644612193701262505)
                      ·
                        rfl

theorem cell23_2125501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_2125501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125501 prefixEnd_2125501 := by exact prefixLift 2125501
  have htrace : WordTrace (prefixWord ++ tailWord_2125501) baseStart_2125501 baseEnd_2125501 := by
    simpa [prefixWord, tailWord_2125501, baseEnd_2125501] using wordTrace_append hprefix tailTrace_2125501
  have hstable : (prefixWord ++ tailWord_2125501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125501).length < 2 ^ (prefixWord ++ tailWord_2125501).sum := by decide
  have hdescent : baseEnd_2125501 < baseStart_2125501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125506 : List Nat := [3, 5, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2125506 : Nat := 118140960795 + 2125506 * 2 ^ 59
def prefixEnd_2125506 : Nat := 4983230072969 + 3 ^ 40 * 2125506 * 2
def baseEnd_2125506 : Nat := 363802070671822060566661

theorem tailTrace_2125506 : CollatzResearch.WordTrace tailWord_2125506 prefixEnd_2125506 363802070671822060566661 := by
  unfold tailWord_2125506
  simp only [CollatzResearch.WordTrace]
  refine ⟨19380893159415561092351093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51682381758441496246269581 19380893159415561092351093)
  ·
    refine ⟨1816958733695208852407915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19380893159415561092351093 1816958733695208852407915)
    ·
      refine ⟨2725438100542813278611873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1816958733695208852407915 2725438100542813278611873)
      ·
        refine ⟨2044078575407109958958905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2725438100542813278611873 2044078575407109958958905)
        ·
          refine ⟨1533058931555332469219179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2044078575407109958958905 1533058931555332469219179)
          ·
            refine ⟨2299588397332998703828769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533058931555332469219179 2299588397332998703828769)
            ·
              refine ⟨1724691297999749027871577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2299588397332998703828769 1724691297999749027871577)
              ·
                refine ⟨1293518473499811770903683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1724691297999749027871577 1293518473499811770903683)
                ·
                  refine ⟨1940277710249717656355525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293518473499811770903683 1940277710249717656355525)
                  ·
                    refine ⟨363802070671822060566661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1940277710249717656355525 363802070671822060566661)
                    ·
                      rfl

theorem cell23_2125506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2125506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125506 prefixEnd_2125506 := by exact prefixLift 2125506
  have htrace : WordTrace (prefixWord ++ tailWord_2125506) baseStart_2125506 baseEnd_2125506 := by
    simpa [prefixWord, tailWord_2125506, baseEnd_2125506] using wordTrace_append hprefix tailTrace_2125506
  have hstable : (prefixWord ++ tailWord_2125506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125506).length < 2 ^ (prefixWord ++ tailWord_2125506).sum := by decide
  have hdescent : baseEnd_2125506 < baseStart_2125506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125524 : List Nat := [2, 4, 1, 3, 1, 1, 3, 8]
def baseStart_2125524 : Nat := 118140960795 + 2125524 * 2 ^ 59
def prefixEnd_2125524 : Nat := 4983230072969 + 3 ^ 40 * 2125524 * 2
def baseEnd_2125524 : Nat := 40422794617305448565737

theorem tailTrace_2125524 : CollatzResearch.WordTrace tailWord_2125524 prefixEnd_2125524 40422794617305448565737 := by
  unfold tailWord_2125524
  simp only [CollatzResearch.WordTrace]
  refine ⟨38762114575798516721779813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51682819434398022295706417 38762114575798516721779813)
  ·
    refine ⟨7267896482962221885333715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38762114575798516721779813 7267896482962221885333715)
    ·
      refine ⟨10901844724443332828000573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7267896482962221885333715 10901844724443332828000573)
      ·
        refine ⟨4088191771666249810500215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10901844724443332828000573 4088191771666249810500215)
        ·
          refine ⟨6132287657499374715750323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4088191771666249810500215 6132287657499374715750323)
          ·
            refine ⟨9198431486249062073625485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6132287657499374715750323 9198431486249062073625485)
            ·
              refine ⟨3449411807343398277609557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9198431486249062073625485 3449411807343398277609557)
              ·
                refine ⟨40422794617305448565737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3449411807343398277609557 40422794617305448565737)
                ·
                  rfl

theorem cell23_2125524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 8].length) (baseStart_2125524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125524 prefixEnd_2125524 := by exact prefixLift 2125524
  have htrace : WordTrace (prefixWord ++ tailWord_2125524) baseStart_2125524 baseEnd_2125524 := by
    simpa [prefixWord, tailWord_2125524, baseEnd_2125524] using wordTrace_append hprefix tailTrace_2125524
  have hstable : (prefixWord ++ tailWord_2125524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125524).length < 2 ^ (prefixWord ++ tailWord_2125524).sum := by decide
  have hdescent : baseEnd_2125524 < baseStart_2125524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125567 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 2, 6]
def baseStart_2125567 : Nat := 118140960795 + 2125567 * 2 ^ 59
def prefixEnd_2125567 : Nat := 4983230072969 + 3 ^ 40 * 2125567 * 2
def baseEnd_2125567 : Nat := 363812511445130147679067

theorem tailTrace_2125567 : CollatzResearch.WordTrace tailWord_2125567 prefixEnd_2125567 363812511445130147679067 := by
  unfold tailWord_2125567
  simp only [CollatzResearch.WordTrace]
  refine ⟨77525797490441251787374955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51683864993627501191583303 77525797490441251787374955)
  ·
    refine ⟨116288696235661877681062433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77525797490441251787374955 116288696235661877681062433)
    ·
      refine ⟨87216522176746408260796825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116288696235661877681062433 87216522176746408260796825)
      ·
        refine ⟨65412391632559806195597619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87216522176746408260796825 65412391632559806195597619)
        ·
          refine ⟨98118587448839709293396429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65412391632559806195597619 98118587448839709293396429)
          ·
            refine ⟨36794470293314890985023661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98118587448839709293396429 36794470293314890985023661)
            ·
              refine ⟨13797926359993084119383873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36794470293314890985023661 13797926359993084119383873)
              ·
                refine ⟨10348444769994813089537905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13797926359993084119383873 10348444769994813089537905)
                ·
                  refine ⟨7761333577496109817153429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10348444769994813089537905 7761333577496109817153429)
                  ·
                    refine ⟨363812511445130147679067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7761333577496109817153429 363812511445130147679067)
                    ·
                      rfl

theorem cell23_2125567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_2125567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125567 prefixEnd_2125567 := by exact prefixLift 2125567
  have htrace : WordTrace (prefixWord ++ tailWord_2125567) baseStart_2125567 baseEnd_2125567 := by
    simpa [prefixWord, tailWord_2125567, baseEnd_2125567] using wordTrace_append hprefix tailTrace_2125567
  have hstable : (prefixWord ++ tailWord_2125567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125567).length < 2 ^ (prefixWord ++ tailWord_2125567).sum := by decide
  have hdescent : baseEnd_2125567 < baseStart_2125567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125577 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 5]
def baseStart_2125577 : Nat := 118140960795 + 2125577 * 2 ^ 59
def prefixEnd_2125577 : Nat := 4983230072969 + 3 ^ 40 * 2125577 * 2
def baseEnd_2125577 : Nat := 1091442669141935403912155

theorem tailTrace_2125577 : CollatzResearch.WordTrace tailWord_2125577 prefixEnd_2125577 1091442669141935403912155 := by
  unfold tailWord_2125577
  simp only [CollatzResearch.WordTrace]
  refine ⟨77526162220405023495238985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51684108146936682330159323 77526162220405023495238985)
  ·
    refine ⟨58144621665303767621429239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77526162220405023495238985 58144621665303767621429239)
    ·
      refine ⟨87216932497955651432143859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58144621665303767621429239 87216932497955651432143859)
      ·
        refine ⟨130825398746933477148215789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87216932497955651432143859 130825398746933477148215789)
        ·
          refine ⟨49059524530100053930580921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130825398746933477148215789 49059524530100053930580921)
          ·
            refine ⟨36794643397575040447935691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49059524530100053930580921 36794643397575040447935691)
            ·
              refine ⟨55191965096362560671903537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36794643397575040447935691 55191965096362560671903537)
              ·
                refine ⟨41393973822271920503927653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55191965096362560671903537 41393973822271920503927653)
                ·
                  refine ⟨7761370091675985094486435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41393973822271920503927653 7761370091675985094486435)
                  ·
                    refine ⟨11642055137513977641729653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7761370091675985094486435 11642055137513977641729653)
                    ·
                      refine ⟨1091442669141935403912155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11642055137513977641729653 1091442669141935403912155)
                      ·
                        rfl

theorem cell23_2125577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_2125577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125577 prefixEnd_2125577 := by exact prefixLift 2125577
  have htrace : WordTrace (prefixWord ++ tailWord_2125577) baseStart_2125577 baseEnd_2125577 := by
    simpa [prefixWord, tailWord_2125577, baseEnd_2125577] using wordTrace_append hprefix tailTrace_2125577
  have hstable : (prefixWord ++ tailWord_2125577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125577).length < 2 ^ (prefixWord ++ tailWord_2125577).sum := by decide
  have hdescent : baseEnd_2125577 < baseStart_2125577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125587 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 4]
def baseStart_2125587 : Nat := 118140960795 + 2125587 * 2 ^ 59
def prefixEnd_2125587 : Nat := 4983230072969 + 3 ^ 40 * 2125587 * 2
def baseEnd_2125587 : Nat := 1091447803948480364787109

theorem tailTrace_2125587 : CollatzResearch.WordTrace tailWord_2125587 prefixEnd_2125587 1091447803948480364787109 := by
  unfold tailWord_2125587
  simp only [CollatzResearch.WordTrace]
  refine ⟨77526526950368795203103015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51684351300245863468735343 77526526950368795203103015)
  ·
    refine ⟨116289790425553192804654523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77526526950368795203103015 116289790425553192804654523)
    ·
      refine ⟨174434685638329789206981785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116289790425553192804654523 174434685638329789206981785)
      ·
        refine ⟨130826014228747341905236339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174434685638329789206981785 130826014228747341905236339)
        ·
          refine ⟨196239021343121012857854509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130826014228747341905236339 196239021343121012857854509)
          ·
            refine ⟨73589633003670379821695441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 196239021343121012857854509 73589633003670379821695441)
            ·
              refine ⟨55192224752752784866271581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73589633003670379821695441 55192224752752784866271581)
              ·
                refine ⟨20697084282282294324851843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55192224752752784866271581 20697084282282294324851843)
                ·
                  refine ⟨31045626423423441487277765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20697084282282294324851843 31045626423423441487277765)
                  ·
                    refine ⟨5821054954391895278864581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31045626423423441487277765 5821054954391895278864581)
                    ·
                      refine ⟨1091447803948480364787109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5821054954391895278864581 1091447803948480364787109)
                      ·
                        rfl

theorem cell23_2125587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_2125587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125587 prefixEnd_2125587 := by exact prefixLift 2125587
  have htrace : WordTrace (prefixWord ++ tailWord_2125587) baseStart_2125587 baseEnd_2125587 := by
    simpa [prefixWord, tailWord_2125587, baseEnd_2125587] using wordTrace_append hprefix tailTrace_2125587
  have hstable : (prefixWord ++ tailWord_2125587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125587).length < 2 ^ (prefixWord ++ tailWord_2125587).sum := by decide
  have hdescent : baseEnd_2125587 < baseStart_2125587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125608 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_2125608 : Nat := 118140960795 + 2125608 * 2 ^ 59
def prefixEnd_2125608 : Nat := 4983230072969 + 3 ^ 40 * 2125608 * 2
def baseEnd_2125608 : Nat := 1091458587042224782624513

theorem tailTrace_2125608 : CollatzResearch.WordTrace tailWord_2125608 prefixEnd_2125608 1091458587042224782624513 := by
  unfold tailWord_2125608
  simp only [CollatzResearch.WordTrace]
  refine ⟨38763646441646357894808739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51684861922195143859744985 38763646441646357894808739)
  ·
    refine ⟨58145469662469536842213109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38763646441646357894808739 58145469662469536842213109)
    ·
      refine ⟨5451137780856519078957479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58145469662469536842213109 5451137780856519078957479)
      ·
        refine ⟨8176706671284778618436219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5451137780856519078957479 8176706671284778618436219)
        ·
          refine ⟨12265060006927167927654329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8176706671284778618436219 12265060006927167927654329)
          ·
            refine ⟨9198795005195375945740747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12265060006927167927654329 9198795005195375945740747)
            ·
              refine ⟨13798192507793063918611121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9198795005195375945740747 13798192507793063918611121)
              ·
                refine ⟨10348644380844797938958341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13798192507793063918611121 10348644380844797938958341)
                ·
                  refine ⟨1940370821408399613554689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10348644380844797938958341 1940370821408399613554689)
                  ·
                    refine ⟨1455278116056299710166017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1940370821408399613554689 1455278116056299710166017)
                    ·
                      refine ⟨1091458587042224782624513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1455278116056299710166017 1091458587042224782624513)
                      ·
                        rfl

theorem cell23_2125608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_2125608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125608 prefixEnd_2125608 := by exact prefixLift 2125608
  have htrace : WordTrace (prefixWord ++ tailWord_2125608) baseStart_2125608 baseEnd_2125608 := by
    simpa [prefixWord, tailWord_2125608, baseEnd_2125608] using wordTrace_append hprefix tailTrace_2125608
  have hstable : (prefixWord ++ tailWord_2125608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125608).length < 2 ^ (prefixWord ++ tailWord_2125608).sum := by decide
  have hdescent : baseEnd_2125608 < baseStart_2125608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125631 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 7]
def baseStart_2125631 : Nat := 118140960795 + 2125631 * 2 ^ 59
def prefixEnd_2125631 : Nat := 4983230072969 + 3 ^ 40 * 2125631 * 2
def baseEnd_2125631 : Nat := 121274488566364243626323

theorem tailTrace_2125631 : CollatzResearch.WordTrace tailWord_2125631 prefixEnd_2125631 121274488566364243626323 := by
  unfold tailWord_2125631
  simp only [CollatzResearch.WordTrace]
  refine ⟨77528131762209390717704747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51685421174806260478469831 77528131762209390717704747)
  ·
    refine ⟨116292197643314086076557121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77528131762209390717704747 116292197643314086076557121)
    ·
      refine ⟨87219148232485564557417841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116292197643314086076557121 87219148232485564557417841)
      ·
        refine ⟨65414361174364173418063381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87219148232485564557417841 65414361174364173418063381)
        ·
          refine ⟨3066298180048320628971721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65414361174364173418063381 3066298180048320628971721)
          ·
            refine ⟨2299723635036240471728791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3066298180048320628971721 2299723635036240471728791)
            ·
              refine ⟨3449585452554360707593187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2299723635036240471728791 3449585452554360707593187)
              ·
                refine ⟨5174378178831541061389781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3449585452554360707593187 5174378178831541061389781)
                ·
                  refine ⟨121274488566364243626323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5174378178831541061389781 121274488566364243626323)
                  ·
                    rfl

theorem cell23_2125631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 7].length) (baseStart_2125631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125631 prefixEnd_2125631 := by exact prefixLift 2125631
  have htrace : WordTrace (prefixWord ++ tailWord_2125631) baseStart_2125631 baseEnd_2125631 := by
    simpa [prefixWord, tailWord_2125631, baseEnd_2125631] using wordTrace_append hprefix tailTrace_2125631
  have hstable : (prefixWord ++ tailWord_2125631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125631).length < 2 ^ (prefixWord ++ tailWord_2125631).sum := by decide
  have hdescent : baseEnd_2125631 < baseStart_2125631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125681 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 2, 4, 2]
def baseStart_2125681 : Nat := 118140960795 + 2125681 * 2 ^ 59
def prefixEnd_2125681 : Nat := 4983230072969 + 3 ^ 40 * 2125681 * 2
def baseEnd_2125681 : Nat := 1091496071130002997011677

theorem tailTrace_2125681 : CollatzResearch.WordTrace tailWord_2125681 prefixEnd_2125681 1091496071130002997011677 := by
  unfold tailWord_2125681
  simp only [CollatzResearch.WordTrace]
  refine ⟨77529955412028249257024897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51686636941352166171349931 77529955412028249257024897)
  ·
    refine ⟨58147466559021186942768673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77529955412028249257024897 58147466559021186942768673)
    ·
      refine ⟨43610599919265890207076505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58147466559021186942768673 43610599919265890207076505)
      ·
        refine ⟨32707949939449417655307379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43610599919265890207076505 32707949939449417655307379)
        ·
          refine ⟨49061924909174126482961069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32707949939449417655307379 49061924909174126482961069)
          ·
            refine ⟨18398221840940297431110401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49061924909174126482961069 18398221840940297431110401)
            ·
              refine ⟨13798666380705223073332801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18398221840940297431110401 13798666380705223073332801)
              ·
                refine ⟨10348999785528917304999601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13798666380705223073332801 10348999785528917304999601)
                ·
                  refine ⟨7761749839146687978749701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10348999785528917304999601 7761749839146687978749701)
                  ·
                    refine ⟨1455328094840003996015569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7761749839146687978749701 1455328094840003996015569)
                    ·
                      refine ⟨1091496071130002997011677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1455328094840003996015569 1091496071130002997011677)
                      ·
                        rfl

theorem cell23_2125681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_2125681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125681 prefixEnd_2125681 := by exact prefixLift 2125681
  have htrace : WordTrace (prefixWord ++ tailWord_2125681) baseStart_2125681 baseEnd_2125681 := by
    simpa [prefixWord, tailWord_2125681, baseEnd_2125681] using wordTrace_append hprefix tailTrace_2125681
  have hstable : (prefixWord ++ tailWord_2125681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125681).length < 2 ^ (prefixWord ++ tailWord_2125681).sum := by decide
  have hdescent : baseEnd_2125681 < baseStart_2125681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125725 : List Nat := [1, 4, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_2125725 : Nat := 118140960795 + 2125725 * 2 ^ 59
def prefixEnd_2125725 : Nat := 4983230072969 + 3 ^ 40 * 2125725 * 2
def baseEnd_2125725 : Nat := 363839554759600274953825

theorem tailTrace_2125725 : CollatzResearch.WordTrace tailWord_2125725 prefixEnd_2125725 363839554759600274953825 := by
  unfold tailWord_2125725
  simp only [CollatzResearch.WordTrace]
  refine ⟨77531560223868844771626629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51687706815912563181084419 77531560223868844771626629)
  ·
    refine ⟨14537167541975408394679993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77531560223868844771626629 14537167541975408394679993)
    ·
      refine ⟨10902875656481556296009995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14537167541975408394679993 10902875656481556296009995)
      ·
        refine ⟨16354313484722334444014993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10902875656481556296009995 16354313484722334444014993)
        ·
          refine ⟨12265735113541750833011245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16354313484722334444014993 12265735113541750833011245)
          ·
            refine ⟨4599650667578156562379217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12265735113541750833011245 4599650667578156562379217)
            ·
              refine ⟨3449738000683617421784413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4599650667578156562379217 3449738000683617421784413)
              ·
                refine ⟨1293651750256356533169155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3449738000683617421784413 1293651750256356533169155)
                ·
                  refine ⟨1940477625384534799753733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293651750256356533169155 1940477625384534799753733)
                  ·
                    refine ⟨363839554759600274953825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1940477625384534799753733 363839554759600274953825)
                    ·
                      rfl

theorem cell23_2125725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_2125725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125725 prefixEnd_2125725 := by exact prefixLift 2125725
  have htrace : WordTrace (prefixWord ++ tailWord_2125725) baseStart_2125725 baseEnd_2125725 := by
    simpa [prefixWord, tailWord_2125725, baseEnd_2125725] using wordTrace_append hprefix tailTrace_2125725
  have hstable : (prefixWord ++ tailWord_2125725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125725).length < 2 ^ (prefixWord ++ tailWord_2125725).sum := by decide
  have hdescent : baseEnd_2125725 < baseStart_2125725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125731 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 7, 1, 3]
def baseStart_2125731 : Nat := 118140960795 + 2125731 * 2 ^ 59
def prefixEnd_2125731 : Nat := 4983230072969 + 3 ^ 40 * 2125731 * 2
def baseEnd_2125731 : Nat := 1091521745162727801386447

theorem tailTrace_2125731 : CollatzResearch.WordTrace tailWord_2125731 prefixEnd_2125731 1091521745162727801386447 := by
  unfold tailWord_2125731
  simp only [CollatzResearch.WordTrace]
  refine ⟨77531779061847107796345047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51687852707898071864230031 77531779061847107796345047)
  ·
    refine ⟨116297668592770661694517571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77531779061847107796345047 116297668592770661694517571)
    ·
      refine ⟨174446502889155992541776357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116297668592770661694517571 174446502889155992541776357)
      ·
        refine ⟨32708719291716748601583067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174446502889155992541776357 32708719291716748601583067)
        ·
          refine ⟨49063078937575122902374601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32708719291716748601583067 49063078937575122902374601)
          ·
            refine ⟨36797309203181342176780951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49063078937575122902374601 36797309203181342176780951)
            ·
              refine ⟨55195963804772013265171427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36797309203181342176780951 55195963804772013265171427)
              ·
                refine ⟨82793945707158019897757141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55195963804772013265171427 82793945707158019897757141)
                ·
                  refine ⟨1940483102511516091353683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 82793945707158019897757141 1940483102511516091353683)
                  ·
                    refine ⟨2910724653767274137030525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1940483102511516091353683 2910724653767274137030525)
                    ·
                      refine ⟨1091521745162727801386447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2910724653767274137030525 1091521745162727801386447)
                      ·
                        rfl

theorem cell23_2125731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_2125731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125731 prefixEnd_2125731 := by exact prefixLift 2125731
  have htrace : WordTrace (prefixWord ++ tailWord_2125731) baseStart_2125731 baseEnd_2125731 := by
    simpa [prefixWord, tailWord_2125731, baseEnd_2125731] using wordTrace_append hprefix tailTrace_2125731
  have hstable : (prefixWord ++ tailWord_2125731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125731).length < 2 ^ (prefixWord ++ tailWord_2125731).sum := by decide
  have hdescent : baseEnd_2125731 < baseStart_2125731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125754 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_2125754 : Nat := 118140960795 + 2125754 * 2 ^ 59
def prefixEnd_2125754 : Nat := 4983230072969 + 3 ^ 40 * 2125754 * 2
def baseEnd_2125754 : Nat := 1091533555217781211398841

theorem tailTrace_2125754 : CollatzResearch.WordTrace tailWord_2125754 prefixEnd_2125754 1091533555217781211398841 := by
  unfold tailWord_2125754
  simp only [CollatzResearch.WordTrace]
  refine ⟨19383154485190945681108079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51688411960509188482954877 19383154485190945681108079)
  ·
    refine ⟨29074731727786418521662119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19383154485190945681108079 29074731727786418521662119)
    ·
      refine ⟨43612097591679627782493179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29074731727786418521662119 43612097591679627782493179)
      ·
        refine ⟨65418146387519441673739769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43612097591679627782493179 65418146387519441673739769)
        ·
          refine ⟨49063609790639581255304827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65418146387519441673739769 49063609790639581255304827)
          ·
            refine ⟨73595414685959371882957241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49063609790639581255304827 73595414685959371882957241)
            ·
              refine ⟨55196561014469528912217931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73595414685959371882957241 55196561014469528912217931)
              ·
                refine ⟨82794841521704293368326897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55196561014469528912217931 82794841521704293368326897)
                ·
                  refine ⟨62096131141278220026245173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82794841521704293368326897 62096131141278220026245173)
                  ·
                    refine ⟨5821512294494833127460485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62096131141278220026245173 5821512294494833127460485)
                    ·
                      refine ⟨1091533555217781211398841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5821512294494833127460485 1091533555217781211398841)
                      ·
                        rfl

theorem cell23_2125754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_2125754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125754 prefixEnd_2125754 := by exact prefixLift 2125754
  have htrace : WordTrace (prefixWord ++ tailWord_2125754) baseStart_2125754 baseEnd_2125754 := by
    simpa [prefixWord, tailWord_2125754, baseEnd_2125754] using wordTrace_append hprefix tailTrace_2125754
  have hstable : (prefixWord ++ tailWord_2125754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125754).length < 2 ^ (prefixWord ++ tailWord_2125754).sum := by decide
  have hdescent : baseEnd_2125754 < baseStart_2125754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125758 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_2125758 : Nat := 118140960795 + 2125758 * 2 ^ 59
def prefixEnd_2125758 : Nat := 4983230072969 + 3 ^ 40 * 2125758 * 2
def baseEnd_2125758 : Nat := 1091535609140399195748823

theorem tailTrace_2125758 : CollatzResearch.WordTrace tailWord_2125758 prefixEnd_2125758 1091535609140399195748823 := by
  unfold tailWord_2125758
  simp only [CollatzResearch.WordTrace]
  refine ⟨9691595479093661425947241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51688509221832860938385285 9691595479093661425947241)
  ·
    refine ⟨7268696609320246069460431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9691595479093661425947241 7268696609320246069460431)
    ·
      refine ⟨10903044913980369104190647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7268696609320246069460431 10903044913980369104190647)
      ·
        refine ⟨16354567370970553656285971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10903044913980369104190647 16354567370970553656285971)
        ·
          refine ⟨24531851056455830484428957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16354567370970553656285971 24531851056455830484428957)
          ·
            refine ⟨9199444146170936431660859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24531851056455830484428957 9199444146170936431660859)
            ·
              refine ⟨13799166219256404647491289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9199444146170936431660859 13799166219256404647491289)
              ·
                refine ⟨10349374664442303485618467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13799166219256404647491289 10349374664442303485618467)
                ·
                  refine ⟨15524061996663455228427701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10349374664442303485618467 15524061996663455228427701)
                  ·
                    refine ⟨1455380812187198927665097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15524061996663455228427701 1455380812187198927665097)
                    ·
                      refine ⟨1091535609140399195748823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1455380812187198927665097 1091535609140399195748823)
                      ·
                        rfl

theorem cell23_2125758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_2125758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125758 prefixEnd_2125758 := by exact prefixLift 2125758
  have htrace : WordTrace (prefixWord ++ tailWord_2125758) baseStart_2125758 baseEnd_2125758 := by
    simpa [prefixWord, tailWord_2125758, baseEnd_2125758] using wordTrace_append hprefix tailTrace_2125758
  have hstable : (prefixWord ++ tailWord_2125758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125758).length < 2 ^ (prefixWord ++ tailWord_2125758).sum := by decide
  have hdescent : baseEnd_2125758 < baseStart_2125758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125768 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 1, 5]
def baseStart_2125768 : Nat := 118140960795 + 2125768 * 2 ^ 59
def prefixEnd_2125768 : Nat := 4983230072969 + 3 ^ 40 * 2125768 * 2
def baseEnd_2125768 : Nat := 363846914648981385541259

theorem tailTrace_2125768 : CollatzResearch.WordTrace tailWord_2125768 prefixEnd_2125768 363846914648981385541259 := by
  unfold tailWord_2125768
  simp only [CollatzResearch.WordTrace]
  refine ⟨38766564281356531557720979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51688752375142042076961305 38766564281356531557720979)
  ·
    refine ⟨58149846422034797336581469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38766564281356531557720979 58149846422034797336581469)
    ·
      refine ⟨21806192408263049001218051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58149846422034797336581469 21806192408263049001218051)
      ·
        refine ⟨32709288612394573501827077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21806192408263049001218051 32709288612394573501827077)
        ·
          refine ⟨6132991614823982531592577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32709288612394573501827077 6132991614823982531592577)
          ·
            refine ⟨4599743711117986898694433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6132991614823982531592577 4599743711117986898694433)
            ·
              refine ⟨3449807783338490174020825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4599743711117986898694433 3449807783338490174020825)
              ·
                refine ⟨2587355837503867630515619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3449807783338490174020825 2587355837503867630515619)
                ·
                  refine ⟨3881033756255801445773429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587355837503867630515619 3881033756255801445773429)
                  ·
                    refine ⟨363846914648981385541259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3881033756255801445773429 363846914648981385541259)
                    ·
                      rfl

theorem cell23_2125768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_2125768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125768 prefixEnd_2125768 := by exact prefixLift 2125768
  have htrace : WordTrace (prefixWord ++ tailWord_2125768) baseStart_2125768 baseEnd_2125768 := by
    simpa [prefixWord, tailWord_2125768, baseEnd_2125768] using wordTrace_append hprefix tailTrace_2125768
  have hstable : (prefixWord ++ tailWord_2125768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125768).length < 2 ^ (prefixWord ++ tailWord_2125768).sum := by decide
  have hdescent : baseEnd_2125768 < baseStart_2125768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125771 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 2, 6, 2]
def baseStart_2125771 : Nat := 118140960795 + 2125771 * 2 ^ 59
def prefixEnd_2125771 : Nat := 4983230072969 + 3 ^ 40 * 2125771 * 2
def baseEnd_2125771 : Nat := 1091542284388907644886263

theorem tailTrace_2125771 : CollatzResearch.WordTrace tailWord_2125771 prefixEnd_2125771 1091542284388907644886263 := by
  unfold tailWord_2125771
  simp only [CollatzResearch.WordTrace]
  refine ⟨77533237981702194627801167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51688825321134796418534111 77533237981702194627801167)
  ·
    refine ⟨116299856972553291941701751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77533237981702194627801167 116299856972553291941701751)
    ·
      refine ⟨174449785458829937912552627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116299856972553291941701751 174449785458829937912552627)
      ·
        refine ⟨261674678188244906868828941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174449785458829937912552627 261674678188244906868828941)
        ·
          refine ⟨98128004320591840075810853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 261674678188244906868828941 98128004320591840075810853)
          ·
            refine ⟨18399000810110970014214535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98128004320591840075810853 18399000810110970014214535)
            ·
              refine ⟨27598501215166455021321803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18399000810110970014214535 27598501215166455021321803)
              ·
                refine ⟨41397751822749682531982705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27598501215166455021321803 41397751822749682531982705)
                ·
                  refine ⟨31048313867062261898987029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41397751822749682531982705 31048313867062261898987029)
                  ·
                    refine ⟨1455389712518543526515017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31048313867062261898987029 1455389712518543526515017)
                    ·
                      refine ⟨1091542284388907644886263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1455389712518543526515017 1091542284388907644886263)
                      ·
                        rfl

theorem cell23_2125771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 6, 2].length) (baseStart_2125771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125771 prefixEnd_2125771 := by exact prefixLift 2125771
  have htrace : WordTrace (prefixWord ++ tailWord_2125771) baseStart_2125771 baseEnd_2125771 := by
    simpa [prefixWord, tailWord_2125771, baseEnd_2125771] using wordTrace_append hprefix tailTrace_2125771
  have hstable : (prefixWord ++ tailWord_2125771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125771).length < 2 ^ (prefixWord ++ tailWord_2125771).sum := by decide
  have hdescent : baseEnd_2125771 < baseStart_2125771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125791 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 5]
def baseStart_2125791 : Nat := 118140960795 + 2125791 * 2 ^ 59
def prefixEnd_2125791 : Nat := 4983230072969 + 3 ^ 40 * 2125791 * 2
def baseEnd_2125791 : Nat := 1091552554001997566636171

theorem tailTrace_2125791 : CollatzResearch.WordTrace tailWord_2125791 prefixEnd_2125791 1091552554001997566636171 := by
  unfold tailWord_2125791
  simp only [CollatzResearch.WordTrace]
  refine ⟨77533967441629738043529227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51689311627753158695686151 77533967441629738043529227)
  ·
    refine ⟨116300951162444607065293841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77533967441629738043529227 116300951162444607065293841)
    ·
      refine ⟨87225713371833455298970381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116300951162444607065293841 87225713371833455298970381)
      ·
        refine ⟨32709642514437545737113893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87225713371833455298970381 32709642514437545737113893)
        ·
          refine ⟨6133057971457039825708855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32709642514437545737113893 6133057971457039825708855)
          ·
            refine ⟨9199586957185559738563283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6133057971457039825708855 9199586957185559738563283)
            ·
              refine ⟨13799380435778339607844925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9199586957185559738563283 13799380435778339607844925)
              ·
                refine ⟨5174767663416877352941847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13799380435778339607844925 5174767663416877352941847)
                ·
                  refine ⟨7762151495125316029412771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5174767663416877352941847 7762151495125316029412771)
                  ·
                    refine ⟨11643227242687974044119157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7762151495125316029412771 11643227242687974044119157)
                    ·
                      refine ⟨1091552554001997566636171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11643227242687974044119157 1091552554001997566636171)
                      ·
                        rfl

theorem cell23_2125791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_2125791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125791 prefixEnd_2125791 := by exact prefixLift 2125791
  have htrace : WordTrace (prefixWord ++ tailWord_2125791) baseStart_2125791 baseEnd_2125791 := by
    simpa [prefixWord, tailWord_2125791, baseEnd_2125791] using wordTrace_append hprefix tailTrace_2125791
  have hstable : (prefixWord ++ tailWord_2125791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125791).length < 2 ^ (prefixWord ++ tailWord_2125791).sum := by decide
  have hdescent : baseEnd_2125791 < baseStart_2125791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125799 : List Nat := [1, 1, 5, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_2125799 : Nat := 118140960795 + 2125799 * 2 ^ 59
def prefixEnd_2125799 : Nat := 4983230072969 + 3 ^ 40 * 2125799 * 2
def baseEnd_2125799 : Nat := 1091556661847233535336135

theorem tailTrace_2125799 : CollatzResearch.WordTrace tailWord_2125799 prefixEnd_2125799 1091556661847233535336135 := by
  unfold tailWord_2125799
  simp only [CollatzResearch.WordTrace]
  refine ⟨77534259225600755409820451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51689506150400503606546967 77534259225600755409820451)
  ·
    refine ⟨116301388838401133114730677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77534259225600755409820451 116301388838401133114730677)
    ·
      refine ⟨10903255203600106229506001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116301388838401133114730677 10903255203600106229506001)
      ·
        refine ⟨8177441402700079672129501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10903255203600106229506001 8177441402700079672129501)
        ·
          refine ⟨3066540526012529877048563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8177441402700079672129501 3066540526012529877048563)
          ·
            refine ⟨4599810789018794815572845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3066540526012529877048563 4599810789018794815572845)
            ·
              refine ⟨1724929045882048055839817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4599810789018794815572845 1724929045882048055839817)
              ·
                refine ⟨1293696784411536041879863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1724929045882048055839817 1293696784411536041879863)
                ·
                  refine ⟨1940545176617304062819795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1293696784411536041879863 1940545176617304062819795)
                  ·
                    refine ⟨2910817764925956094229693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1940545176617304062819795 2910817764925956094229693)
                    ·
                      refine ⟨1091556661847233535336135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2910817764925956094229693 1091556661847233535336135)
                      ·
                        rfl

theorem cell23_2125799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_2125799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125799 prefixEnd_2125799 := by exact prefixLift 2125799
  have htrace : WordTrace (prefixWord ++ tailWord_2125799) baseStart_2125799 baseEnd_2125799 := by
    simpa [prefixWord, tailWord_2125799, baseEnd_2125799] using wordTrace_append hprefix tailTrace_2125799
  have hstable : (prefixWord ++ tailWord_2125799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125799).length < 2 ^ (prefixWord ++ tailWord_2125799).sum := by decide
  have hdescent : baseEnd_2125799 < baseStart_2125799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125822 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2125822 : Nat := 118140960795 + 2125822 * 2 ^ 59
def prefixEnd_2125822 : Nat := 4983230072969 + 3 ^ 40 * 2125822 * 2
def baseEnd_2125822 : Nat := 1091568471902286945348529

theorem tailTrace_2125822 : CollatzResearch.WordTrace tailWord_2125822 prefixEnd_2125822 1091568471902286945348529 := by
  unfold tailWord_2125822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9691887263064678792238465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51690065403011620225271813 9691887263064678792238465)
  ·
    refine ⟨7268915447298509094178849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9691887263064678792238465 7268915447298509094178849)
    ·
      refine ⟨5451686585473881820634137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7268915447298509094178849 5451686585473881820634137)
      ·
        refine ⟨4088764939105411365475603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5451686585473881820634137 4088764939105411365475603)
        ·
          refine ⟨6133147408658117048213405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4088764939105411365475603 6133147408658117048213405)
          ·
            refine ⟨2299930278246793893080027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6133147408658117048213405 2299930278246793893080027)
            ·
              refine ⟨3449895417370190839620041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2299930278246793893080027 3449895417370190839620041)
              ·
                refine ⟨2587421563027643129715031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3449895417370190839620041 2587421563027643129715031)
                ·
                  refine ⟨3881132344541464694572547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587421563027643129715031 3881132344541464694572547)
                  ·
                    refine ⟨5821698516812197041858821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3881132344541464694572547 5821698516812197041858821)
                    ·
                      refine ⟨1091568471902286945348529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5821698516812197041858821 1091568471902286945348529)
                      ·
                        rfl

theorem cell23_2125822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2125822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125822 prefixEnd_2125822 := by exact prefixLift 2125822
  have htrace : WordTrace (prefixWord ++ tailWord_2125822) baseStart_2125822 baseEnd_2125822 := by
    simpa [prefixWord, tailWord_2125822, baseEnd_2125822] using wordTrace_append hprefix tailTrace_2125822
  have hstable : (prefixWord ++ tailWord_2125822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125822).length < 2 ^ (prefixWord ++ tailWord_2125822).sum := by decide
  have hdescent : baseEnd_2125822 < baseStart_2125822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125824 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 4, 7]
def baseStart_2125824 : Nat := 118140960795 + 2125824 * 2 ^ 59
def prefixEnd_2125824 : Nat := 4983230072969 + 3 ^ 40 * 2125824 * 2
def baseEnd_2125824 : Nat := 363856499621198645841173

theorem tailTrace_2125824 : CollatzResearch.WordTrace tailWord_2125824 prefixEnd_2125824 363856499621198645841173 := by
  unfold tailWord_2125824
  simp only [CollatzResearch.WordTrace]
  refine ⟨38767585525255092339740263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51690114033673456452987017 38767585525255092339740263)
  ·
    refine ⟨58151378287882638509610395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38767585525255092339740263 58151378287882638509610395)
    ·
      refine ⟨87227067431823957764415593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58151378287882638509610395 87227067431823957764415593)
      ·
        refine ⟨65420300573867968323311695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87227067431823957764415593 65420300573867968323311695)
        ·
          refine ⟨98130450860801952484967543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65420300573867968323311695 98130450860801952484967543)
          ·
            refine ⟨147195676291202928727451315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98130450860801952484967543 147195676291202928727451315)
            ·
              refine ⟨220793514436804393091176973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147195676291202928727451315 220793514436804393091176973)
              ·
                refine ⟨82797567913801647409191365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220793514436804393091176973 82797567913801647409191365)
                ·
                  refine ⟨15524543983837808889223381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82797567913801647409191365 15524543983837808889223381)
                  ·
                    refine ⟨363856499621198645841173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15524543983837808889223381 363856499621198645841173)
                    ·
                      rfl

theorem cell23_2125824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_2125824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125824 prefixEnd_2125824 := by exact prefixLift 2125824
  have htrace : WordTrace (prefixWord ++ tailWord_2125824) baseStart_2125824 baseEnd_2125824 := by
    simpa [prefixWord, tailWord_2125824, baseEnd_2125824] using wordTrace_append hprefix tailTrace_2125824
  have hstable : (prefixWord ++ tailWord_2125824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125824).length < 2 ^ (prefixWord ++ tailWord_2125824).sum := by decide
  have hdescent : baseEnd_2125824 < baseStart_2125824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125838 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_2125838 : Nat := 118140960795 + 2125838 * 2 ^ 59
def prefixEnd_2125838 : Nat := 4983230072969 + 3 ^ 40 * 2125838 * 2
def baseEnd_2125838 : Nat := 1091576687592758882748455

theorem tailTrace_2125838 : CollatzResearch.WordTrace tailWord_2125838 prefixEnd_2125838 1091576687592758882748455 := by
  unfold tailWord_2125838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9691960209057433133811271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51690454448306310046993445 9691960209057433133811271)
  ·
    refine ⟨14537940313586149700716907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9691960209057433133811271 14537940313586149700716907)
    ·
      refine ⟨21806910470379224551075361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14537940313586149700716907 21806910470379224551075361)
      ·
        refine ⟨16355182852784418413306521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21806910470379224551075361 16355182852784418413306521)
        ·
          refine ⟨12266387139588313809979891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16355182852784418413306521 12266387139588313809979891)
          ·
            refine ⟨18399580709382470714969837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12266387139588313809979891 18399580709382470714969837)
            ·
              refine ⟨6899842766018426518113689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18399580709382470714969837 6899842766018426518113689)
              ·
                refine ⟨5174882074513819888585267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6899842766018426518113689 5174882074513819888585267)
                ·
                  refine ⟨7762323111770729832877901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5174882074513819888585267 7762323111770729832877901)
                  ·
                    refine ⟨2910871166914023687329213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7762323111770729832877901 2910871166914023687329213)
                    ·
                      refine ⟨1091576687592758882748455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2910871166914023687329213 1091576687592758882748455)
                      ·
                        rfl

theorem cell23_2125838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_2125838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125838 prefixEnd_2125838 := by exact prefixLift 2125838
  have htrace : WordTrace (prefixWord ++ tailWord_2125838) baseStart_2125838 baseEnd_2125838 := by
    simpa [prefixWord, tailWord_2125838, baseEnd_2125838] using wordTrace_append hprefix tailTrace_2125838
  have hstable : (prefixWord ++ tailWord_2125838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125838).length < 2 ^ (prefixWord ++ tailWord_2125838).sum := by decide
  have hdescent : baseEnd_2125838 < baseStart_2125838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125855 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 2, 1, 3]
def baseStart_2125855 : Nat := 118140960795 + 2125855 * 2 ^ 59
def prefixEnd_2125855 : Nat := 4983230072969 + 3 ^ 40 * 2125855 * 2
def baseEnd_2125855 : Nat := 1091585416763885316235877

theorem tailTrace_2125855 : CollatzResearch.WordTrace tailWord_2125855 prefixEnd_2125855 1091585416763885316235877 := by
  unfold tailWord_2125855
  simp only [CollatzResearch.WordTrace]
  refine ⟨77536301713397876973859019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51690867808931917982572679 77536301713397876973859019)
  ·
    refine ⟨116304452570096815460788529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77536301713397876973859019 116304452570096815460788529)
    ·
      refine ⟨87228339427572611595591397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116304452570096815460788529 87228339427572611595591397)
      ·
        refine ⟨16355313642669864674173387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87228339427572611595591397 16355313642669864674173387)
        ·
          refine ⟨24532970464004797011260081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16355313642669864674173387 24532970464004797011260081)
          ·
            refine ⟨18399727848003597758445061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24532970464004797011260081 18399727848003597758445061)
            ·
              refine ⟨3449948971500674579708449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18399727848003597758445061 3449948971500674579708449)
              ·
                refine ⟨2587461728625505934781337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3449948971500674579708449 2587461728625505934781337)
                ·
                  refine ⟨1940596296469129451086003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2587461728625505934781337 1940596296469129451086003)
                  ·
                    refine ⟨2910894444703694176629005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1940596296469129451086003 2910894444703694176629005)
                    ·
                      refine ⟨1091585416763885316235877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2910894444703694176629005 1091585416763885316235877)
                      ·
                        rfl

theorem cell23_2125855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_2125855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125855 prefixEnd_2125855 := by exact prefixLift 2125855
  have htrace : WordTrace (prefixWord ++ tailWord_2125855) baseStart_2125855 baseEnd_2125855 := by
    simpa [prefixWord, tailWord_2125855, baseEnd_2125855] using wordTrace_append hprefix tailTrace_2125855
  have hstable : (prefixWord ++ tailWord_2125855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125855).length < 2 ^ (prefixWord ++ tailWord_2125855).sum := by decide
  have hdescent : baseEnd_2125855 < baseStart_2125855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125861 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_2125861 : Nat := 118140960795 + 2125861 * 2 ^ 59
def prefixEnd_2125861 : Nat := 4983230072969 + 3 ^ 40 * 2125861 * 2
def baseEnd_2125861 : Nat := 1091588497647812292760849

theorem tailTrace_2125861 : CollatzResearch.WordTrace tailWord_2125861 prefixEnd_2125861 1091588497647812292760849 := by
  unfold tailWord_2125861
  simp only [CollatzResearch.WordTrace]
  refine ⟨77536520551376139998577437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51691013700917426665718291 77536520551376139998577437)
  ·
    refine ⟨29076195206766052499466539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77536520551376139998577437 29076195206766052499466539)
    ·
      refine ⟨43614292810149078749199809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29076195206766052499466539 43614292810149078749199809)
      ·
        refine ⟨32710719607611809061899857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43614292810149078749199809 32710719607611809061899857)
        ·
          refine ⟨24533039705708856796424893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32710719607611809061899857 24533039705708856796424893)
          ·
            refine ⟨9199889889640821298659335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24533039705708856796424893 9199889889640821298659335)
            ·
              refine ⟨13799834834461231947989003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9199889889640821298659335 13799834834461231947989003)
              ·
                refine ⟨20699752251691847921983505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13799834834461231947989003 20699752251691847921983505)
                ·
                  refine ⟨15524814188768885941487629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20699752251691847921983505 15524814188768885941487629)
                  ·
                    refine ⟨5821805320788332228057861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15524814188768885941487629 5821805320788332228057861)
                    ·
                      refine ⟨1091588497647812292760849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5821805320788332228057861 1091588497647812292760849)
                      ·
                        rfl

theorem cell23_2125861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_2125861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125861 prefixEnd_2125861 := by exact prefixLift 2125861
  have htrace : WordTrace (prefixWord ++ tailWord_2125861) baseStart_2125861 baseEnd_2125861 := by
    simpa [prefixWord, tailWord_2125861, baseEnd_2125861] using wordTrace_append hprefix tailTrace_2125861
  have hstable : (prefixWord ++ tailWord_2125861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125861).length < 2 ^ (prefixWord ++ tailWord_2125861).sum := by decide
  have hdescent : baseEnd_2125861 < baseStart_2125861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125878 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2125878 : Nat := 118140960795 + 2125878 * 2 ^ 59
def prefixEnd_2125878 : Nat := 4983230072969 + 3 ^ 40 * 2125878 * 2
def baseEnd_2125878 : Nat := 1091597226818938726248271

theorem tailTrace_2125878 : CollatzResearch.WordTrace tailWord_2125878 prefixEnd_2125878 1091597226818938726248271 := by
  unfold tailWord_2125878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846071287019659493871643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51691427061543034601297525 4846071287019659493871643)
  ·
    refine ⟨7269106930529489240807465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4846071287019659493871643 7269106930529489240807465)
    ·
      refine ⟨5451830197897116930605599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7269106930529489240807465 5451830197897116930605599)
      ·
        refine ⟨8177745296845675395908399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5451830197897116930605599 8177745296845675395908399)
        ·
          refine ⟨12266617945268513093862599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8177745296845675395908399 12266617945268513093862599)
          ·
            refine ⟨18399926917902769640793899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12266617945268513093862599 18399926917902769640793899)
            ·
              refine ⟨27599890376854154461190849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18399926917902769640793899 27599890376854154461190849)
              ·
                refine ⟨20699917782640615845893137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27599890376854154461190849 20699917782640615845893137)
                ·
                  refine ⟨15524938336980461884419853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20699917782640615845893137 15524938336980461884419853)
                  ·
                    refine ⟨5821851876367673206657445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15524938336980461884419853 5821851876367673206657445)
                    ·
                      refine ⟨1091597226818938726248271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5821851876367673206657445 1091597226818938726248271)
                      ·
                        rfl

theorem cell23_2125878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2125878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125878 prefixEnd_2125878 := by exact prefixLift 2125878
  have htrace : WordTrace (prefixWord ++ tailWord_2125878) baseStart_2125878 baseEnd_2125878 := by
    simpa [prefixWord, tailWord_2125878, baseEnd_2125878] using wordTrace_append hprefix tailTrace_2125878
  have hstable : (prefixWord ++ tailWord_2125878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125878).length < 2 ^ (prefixWord ++ tailWord_2125878).sum := by decide
  have hdescent : baseEnd_2125878 < baseStart_2125878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125895 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 4, 2, 2]
def baseStart_2125895 : Nat := 118140960795 + 2125895 * 2 ^ 59
def prefixEnd_2125895 : Nat := 4983230072969 + 3 ^ 40 * 2125895 * 2
def baseEnd_2125895 : Nat := 1091605955990065159735693

theorem tailTrace_2125895 : CollatzResearch.WordTrace tailWord_2125895 prefixEnd_2125895 1091605955990065159735693 := by
  unfold tailWord_2125895
  simp only [CollatzResearch.WordTrace]
  refine ⟨77537760633252963805315139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51691840422168642536876759 77537760633252963805315139)
  ·
    refine ⟨116306640949879445707972709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77537760633252963805315139 116306640949879445707972709)
    ·
      refine ⟨21807495178102396070244883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116306640949879445707972709 21807495178102396070244883)
      ·
        refine ⟨32711242767153594105367325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21807495178102396070244883 32711242767153594105367325)
        ·
          refine ⟨12266716037682597789512747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32711242767153594105367325 12266716037682597789512747)
          ·
            refine ⟨18400074056523896684269121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12266716037682597789512747 18400074056523896684269121)
            ·
              refine ⟨13800055542392922513201841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18400074056523896684269121 13800055542392922513201841)
              ·
                refine ⟨10350041656794691884901381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13800055542392922513201841 10350041656794691884901381)
                ·
                  refine ⟨1940632810649004728419009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10350041656794691884901381 1940632810649004728419009)
                  ·
                    refine ⟨1455474607986753546314257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1940632810649004728419009 1455474607986753546314257)
                    ·
                      refine ⟨1091605955990065159735693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1455474607986753546314257 1091605955990065159735693)
                      ·
                        rfl

theorem cell23_2125895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_2125895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125895 prefixEnd_2125895 := by exact prefixLift 2125895
  have htrace : WordTrace (prefixWord ++ tailWord_2125895) baseStart_2125895 baseEnd_2125895 := by
    simpa [prefixWord, tailWord_2125895, baseEnd_2125895] using wordTrace_append hprefix tailTrace_2125895
  have hstable : (prefixWord ++ tailWord_2125895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125895).length < 2 ^ (prefixWord ++ tailWord_2125895).sum := by decide
  have hdescent : baseEnd_2125895 < baseStart_2125895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125912 : List Nat := [2, 1, 2, 2, 1, 4, 3, 2, 2, 2, 2]
def baseStart_2125912 : Nat := 118140960795 + 2125912 * 2 ^ 59
def prefixEnd_2125912 : Nat := 4983230072969 + 3 ^ 40 * 2125912 * 2
def baseEnd_2125912 : Nat := 1091614685161191593223115

theorem tailTrace_2125912 : CollatzResearch.WordTrace tailWord_2125912 prefixEnd_2125912 1091614685161191593223115 := by
  unfold tailWord_2125912
  simp only [CollatzResearch.WordTrace]
  refine ⟨38769190337095687854341995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51692253782794250472455993 38769190337095687854341995)
  ·
    refine ⟨58153785505643531781512993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38769190337095687854341995 58153785505643531781512993)
    ·
      refine ⟨43615339129232648836134745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58153785505643531781512993 43615339129232648836134745)
      ·
        refine ⟨32711504346924486627101059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43615339129232648836134745 32711504346924486627101059)
        ·
          refine ⟨49067256520386729940651589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32711504346924486627101059 49067256520386729940651589)
          ·
            refine ⟨9200110597572511863872173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49067256520386729940651589 9200110597572511863872173)
            ·
              refine ⟨3450041474089691948952065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9200110597572511863872173 3450041474089691948952065)
              ·
                refine ⟨2587531105567268961714049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3450041474089691948952065 2587531105567268961714049)
                ·
                  refine ⟨1940648329175451721285537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2587531105567268961714049 1940648329175451721285537)
                  ·
                    refine ⟨1455486246881588790964153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1940648329175451721285537 1455486246881588790964153)
                    ·
                      refine ⟨1091614685161191593223115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1455486246881588790964153 1091614685161191593223115)
                      ·
                        rfl

theorem cell23_2125912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_2125912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125912 prefixEnd_2125912 := by exact prefixLift 2125912
  have htrace : WordTrace (prefixWord ++ tailWord_2125912) baseStart_2125912 baseEnd_2125912 := by
    simpa [prefixWord, tailWord_2125912, baseEnd_2125912] using wordTrace_append hprefix tailTrace_2125912
  have hstable : (prefixWord ++ tailWord_2125912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125912).length < 2 ^ (prefixWord ++ tailWord_2125912).sum := by decide
  have hdescent : baseEnd_2125912 < baseStart_2125912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2125968 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 4]
def baseStart_2125968 : Nat := 118140960795 + 2125968 * 2 ^ 59
def prefixEnd_2125968 : Nat := 4983230072969 + 3 ^ 40 * 2125968 * 2
def baseEnd_2125968 : Nat := 1091643440077843374122857

theorem tailTrace_2125968 : CollatzResearch.WordTrace tailWord_2125968 prefixEnd_2125968 1091643440077843374122857 := by
  unfold tailWord_2125968
  simp only [CollatzResearch.WordTrace]
  refine ⟨38770211580994248636361279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51693615441325664848481705 38770211580994248636361279)
  ·
    refine ⟨58155317371491372954541919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38770211580994248636361279 58155317371491372954541919)
    ·
      refine ⟨87232976057237059431812879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58155317371491372954541919 87232976057237059431812879)
      ·
        refine ⟨130849464085855589147719319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87232976057237059431812879 130849464085855589147719319)
        ·
          refine ⟨196274196128783383721578979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130849464085855589147719319 196274196128783383721578979)
          ·
            refine ⟨294411294193175075582368469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196274196128783383721578979 294411294193175075582368469)
            ·
              refine ⟨6900264707652540833961761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 294411294193175075582368469 6900264707652540833961761)
              ·
                refine ⟨5175198530739405625471321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6900264707652540833961761 5175198530739405625471321)
                ·
                  refine ⟨3881398898054554219103491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5175198530739405625471321 3881398898054554219103491)
                  ·
                    refine ⟨5822098347081831328655237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3881398898054554219103491 5822098347081831328655237)
                    ·
                      refine ⟨1091643440077843374122857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5822098347081831328655237 1091643440077843374122857)
                      ·
                        rfl

theorem cell23_2125968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_2125968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2125968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2125968 prefixEnd_2125968 := by exact prefixLift 2125968
  have htrace : WordTrace (prefixWord ++ tailWord_2125968) baseStart_2125968 baseEnd_2125968 := by
    simpa [prefixWord, tailWord_2125968, baseEnd_2125968] using wordTrace_append hprefix tailTrace_2125968
  have hstable : (prefixWord ++ tailWord_2125968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2125968).length < 2 ^ (prefixWord ++ tailWord_2125968).sum := by decide
  have hdescent : baseEnd_2125968 < baseStart_2125968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2125968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126055 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 3, 5]
def baseStart_2126055 : Nat := 118140960795 + 2126055 * 2 ^ 59
def prefixEnd_2126055 : Nat := 4983230072969 + 3 ^ 40 * 2126055 * 2
def baseEnd_2126055 : Nat := 363896037631594844578319

theorem tailTrace_2126055 : CollatzResearch.WordTrace tailWord_2126055 prefixEnd_2126055 363896037631594844578319 := by
  unfold tailWord_2126055
  simp only [CollatzResearch.WordTrace]
  refine ⟨77543596312673311131139619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51695730875115540754093079 77543596312673311131139619)
  ·
    refine ⟨116315394469009966696709429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77543596312673311131139619 116315394469009966696709429)
    ·
      refine ⟨10904568231469684377816509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116315394469009966696709429 10904568231469684377816509)
      ·
        refine ⟨4089213086801131641681191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10904568231469684377816509 4089213086801131641681191)
        ·
          refine ⟨6133819630201697462521787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4089213086801131641681191 6133819630201697462521787)
          ·
            refine ⟨9200729445302546193782681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6133819630201697462521787 9200729445302546193782681)
            ·
              refine ⟨6900547083976909645337011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9200729445302546193782681 6900547083976909645337011)
              ·
                refine ⟨10350820625965364468005517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6900547083976909645337011 10350820625965364468005517)
                ·
                  refine ⟨3881557734737011675502069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10350820625965364468005517 3881557734737011675502069)
                  ·
                    refine ⟨363896037631594844578319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3881557734737011675502069 363896037631594844578319)
                    ·
                      rfl

theorem cell23_2126055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_2126055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126055 prefixEnd_2126055 := by exact prefixLift 2126055
  have htrace : WordTrace (prefixWord ++ tailWord_2126055) baseStart_2126055 baseEnd_2126055 := by
    simpa [prefixWord, tailWord_2126055, baseEnd_2126055] using wordTrace_append hprefix tailTrace_2126055
  have hstable : (prefixWord ++ tailWord_2126055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126055).length < 2 ^ (prefixWord ++ tailWord_2126055).sum := by decide
  have hdescent : baseEnd_2126055 < baseStart_2126055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126085 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 2, 4]
def baseStart_2126085 : Nat := 118140960795 + 2126085 * 2 ^ 59
def prefixEnd_2126085 : Nat := 4983230072969 + 3 ^ 40 * 2126085 * 2
def baseEnd_2126085 : Nat := 363901172438139805453273

theorem tailTrace_2126085 : CollatzResearch.WordTrace tailWord_2126085 prefixEnd_2126085 363901172438139805453273 := by
  unfold tailWord_2126085
  simp only [CollatzResearch.WordTrace]
  refine ⟨77544690502564626254731709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51696460335043084169821139 77544690502564626254731709)
  ·
    refine ⟨29079258938461734845524391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77544690502564626254731709 29079258938461734845524391)
    ·
      refine ⟨43618888407692602268286587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29079258938461734845524391 43618888407692602268286587)
      ·
        refine ⟨65428332611538903402429881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43618888407692602268286587 65428332611538903402429881)
        ·
          refine ⟨49071249458654177551822411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65428332611538903402429881 49071249458654177551822411)
          ·
            refine ⟨73606874187981266327733617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49071249458654177551822411 73606874187981266327733617)
            ·
              refine ⟨55205155640985949745800213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73606874187981266327733617 55205155640985949745800213)
              ·
                refine ⟨2587741670671216394334385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55205155640985949745800213 2587741670671216394334385)
                ·
                  refine ⟨1940806253003412295750789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2587741670671216394334385 1940806253003412295750789)
                  ·
                    refine ⟨363901172438139805453273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1940806253003412295750789 363901172438139805453273)
                    ·
                      rfl

theorem cell23_2126085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_2126085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126085 prefixEnd_2126085 := by exact prefixLift 2126085
  have htrace : WordTrace (prefixWord ++ tailWord_2126085) baseStart_2126085 baseEnd_2126085 := by
    simpa [prefixWord, tailWord_2126085, baseEnd_2126085] using wordTrace_append hprefix tailTrace_2126085
  have hstable : (prefixWord ++ tailWord_2126085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126085).length < 2 ^ (prefixWord ++ tailWord_2126085).sum := by decide
  have hdescent : baseEnd_2126085 < baseStart_2126085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126109 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2126109 : Nat := 118140960795 + 2126109 * 2 ^ 59
def prefixEnd_2126109 : Nat := 4983230072969 + 3 ^ 40 * 2126109 * 2
def baseEnd_2126109 : Nat := 1091715840850127322459709

theorem tailTrace_2126109 : CollatzResearch.WordTrace tailWord_2126109 prefixEnd_2126109 1091715840850127322459709 := by
  unfold tailWord_2126109
  simp only [CollatzResearch.WordTrace]
  refine ⟨77545565854477678353605381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51697043902985118902403587 77545565854477678353605381)
  ·
    refine ⟨14539793597714564691301009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77545565854477678353605381 14539793597714564691301009)
    ·
      refine ⟨10904845198285923518475757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14539793597714564691301009 10904845198285923518475757)
      ·
        refine ⟨4089316949357221319428409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10904845198285923518475757 4089316949357221319428409)
        ·
          refine ⟨3066987712017915989571307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4089316949357221319428409 3066987712017915989571307)
          ·
            refine ⟨4600481568026873984356961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3066987712017915989571307 4600481568026873984356961)
            ·
              refine ⟨3450361176020155488267721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4600481568026873984356961 3450361176020155488267721)
              ·
                refine ⟨2587770882015116616200791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3450361176020155488267721 2587770882015116616200791)
                ·
                  refine ⟨3881656323022674924301187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587770882015116616200791 3881656323022674924301187)
                  ·
                    refine ⟨5822484484534012386451781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3881656323022674924301187 5822484484534012386451781)
                    ·
                      refine ⟨1091715840850127322459709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5822484484534012386451781 1091715840850127322459709)
                      ·
                        rfl

theorem cell23_2126109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2126109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126109 prefixEnd_2126109 := by exact prefixLift 2126109
  have htrace : WordTrace (prefixWord ++ tailWord_2126109) baseStart_2126109 baseEnd_2126109 := by
    simpa [prefixWord, tailWord_2126109, baseEnd_2126109] using wordTrace_append hprefix tailTrace_2126109
  have hstable : (prefixWord ++ tailWord_2126109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126109).length < 2 ^ (prefixWord ++ tailWord_2126109).sum := by decide
  have hdescent : baseEnd_2126109 < baseStart_2126109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126112 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2126112 : Nat := 118140960795 + 2126112 * 2 ^ 59
def prefixEnd_2126112 : Nat := 4983230072969 + 3 ^ 40 * 2126112 * 2
def baseEnd_2126112 : Nat := 1091717381292090810722195

theorem tailTrace_2126112 : CollatzResearch.WordTrace tailWord_2126112 prefixEnd_2126112 1091717381292090810722195 := by
  unfold tailWord_2126112
  simp only [CollatzResearch.WordTrace]
  refine ⟨38772837636733404932982295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51697116848977873243976393 38772837636733404932982295)
  ·
    refine ⟨58159256455100107399473443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38772837636733404932982295 58159256455100107399473443)
    ·
      refine ⟨87238884682650161099210165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58159256455100107399473443 87238884682650161099210165)
      ·
        refine ⟨8178645438998452603050953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87238884682650161099210165 8178645438998452603050953)
        ·
          refine ⟨6133984079248839452288215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8178645438998452603050953 6133984079248839452288215)
          ·
            refine ⟨9200976118873259178432323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6133984079248839452288215 9200976118873259178432323)
            ·
              refine ⟨13801464178309888767648485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9200976118873259178432323 13801464178309888767648485)
              ·
                refine ⟨2587774533433104143934091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13801464178309888767648485 2587774533433104143934091)
                ·
                  refine ⟨3881661800149656215901137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2587774533433104143934091 3881661800149656215901137)
                  ·
                    refine ⟨2911246350112242161925853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3881661800149656215901137 2911246350112242161925853)
                    ·
                      refine ⟨1091717381292090810722195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2911246350112242161925853 1091717381292090810722195)
                      ·
                        rfl

theorem cell23_2126112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2126112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126112 prefixEnd_2126112 := by exact prefixLift 2126112
  have htrace : WordTrace (prefixWord ++ tailWord_2126112) baseStart_2126112 baseEnd_2126112 := by
    simpa [prefixWord, tailWord_2126112, baseEnd_2126112] using wordTrace_append hprefix tailTrace_2126112
  have hstable : (prefixWord ++ tailWord_2126112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126112).length < 2 ^ (prefixWord ++ tailWord_2126112).sum := by decide
  have hdescent : baseEnd_2126112 < baseStart_2126112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126208 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_2126208 : Nat := 118140960795 + 2126208 * 2 ^ 59
def prefixEnd_2126208 : Nat := 4983230072969 + 3 ^ 40 * 2126208 * 2
def baseEnd_2126208 : Nat := 1091766675434922435121753

theorem tailTrace_2126208 : CollatzResearch.WordTrace tailWord_2126208 prefixEnd_2126208 1091766675434922435121753 := by
  unfold tailWord_2126208
  simp only [CollatzResearch.WordTrace]
  refine ⟨38774588340559509130729639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51699451120746012174306185 38774588340559509130729639)
  ·
    refine ⟨58161882510839263696094459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38774588340559509130729639 58161882510839263696094459)
    ·
      refine ⟨87242823766258895544141689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58161882510839263696094459 87242823766258895544141689)
      ·
        refine ⟨65432117824694171658106267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87242823766258895544141689 65432117824694171658106267)
        ·
          refine ⟨98148176737041257487159401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65432117824694171658106267 98148176737041257487159401)
          ·
            refine ⟨73611132552780943115369551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98148176737041257487159401 73611132552780943115369551)
            ·
              refine ⟨110416698829171414673054327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73611132552780943115369551 110416698829171414673054327)
              ·
                refine ⟨165625048243757122009581491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110416698829171414673054327 165625048243757122009581491)
                ·
                  refine ⟨248437572365635683014372237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165625048243757122009581491 248437572365635683014372237)
                  ·
                    refine ⟨93164089637113381130389589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 248437572365635683014372237 93164089637113381130389589)
                    ·
                      refine ⟨1091766675434922435121753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 93164089637113381130389589 1091766675434922435121753)
                      ·
                        rfl

theorem cell23_2126208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_2126208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126208 prefixEnd_2126208 := by exact prefixLift 2126208
  have htrace : WordTrace (prefixWord ++ tailWord_2126208) baseStart_2126208 baseEnd_2126208 := by
    simpa [prefixWord, tailWord_2126208, baseEnd_2126208] using wordTrace_append hprefix tailTrace_2126208
  have hstable : (prefixWord ++ tailWord_2126208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126208).length < 2 ^ (prefixWord ++ tailWord_2126208).sum := by decide
  have hdescent : baseEnd_2126208 < baseStart_2126208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126222 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_2126222 : Nat := 118140960795 + 2126222 * 2 ^ 59
def prefixEnd_2126222 : Nat := 4983230072969 + 3 ^ 40 * 2126222 * 2
def baseEnd_2126222 : Nat := 121308207129342820038521

theorem tailTrace_2126222 : CollatzResearch.WordTrace tailWord_2126222 prefixEnd_2126222 121308207129342820038521 := by
  unfold tailWord_2126222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9693710912883537331558615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51699791535378865768312613 9693710912883537331558615)
  ·
    refine ⟨14540566369325305997337923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9693710912883537331558615 14540566369325305997337923)
    ·
      refine ⟨21810849553987958996006885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14540566369325305997337923 21810849553987958996006885)
      ·
        refine ⟨4089534291372742311751291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21810849553987958996006885 4089534291372742311751291)
        ·
          refine ⟨6134301437059113467626937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4089534291372742311751291 6134301437059113467626937)
          ·
            refine ⟨4600726077794335100720203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6134301437059113467626937 4600726077794335100720203)
            ·
              refine ⟨6901089116691502651080305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4600726077794335100720203 6901089116691502651080305)
              ·
                refine ⟨5175816837518626988310229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6901089116691502651080305 5175816837518626988310229)
                ·
                  refine ⟨121308207129342820038521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5175816837518626988310229 121308207129342820038521)
                  ·
                    rfl

theorem cell23_2126222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_2126222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126222 prefixEnd_2126222 := by exact prefixLift 2126222
  have htrace : WordTrace (prefixWord ++ tailWord_2126222) baseStart_2126222 baseEnd_2126222 := by
    simpa [prefixWord, tailWord_2126222, baseEnd_2126222] using wordTrace_append hprefix tailTrace_2126222
  have hstable : (prefixWord ++ tailWord_2126222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126222).length < 2 ^ (prefixWord ++ tailWord_2126222).sum := by decide
  have hdescent : baseEnd_2126222 < baseStart_2126222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126250 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2126250 : Nat := 118140960795 + 2126250 * 2 ^ 59
def prefixEnd_2126250 : Nat := 4983230072969 + 3 ^ 40 * 2126250 * 2
def baseEnd_2126250 : Nat := 1091788241622411270796561

theorem tailTrace_2126250 : CollatzResearch.WordTrace tailWord_2126250 prefixEnd_2126250 1091788241622411270796561 := by
  unfold tailWord_2126250
  simp only [CollatzResearch.WordTrace]
  refine ⟨19387677136741714858622051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51700472364644572956325469 19387677136741714858622051)
  ·
    refine ⟨29081515705112572287933077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19387677136741714858622051 29081515705112572287933077)
    ·
      refine ⟨1363196048677151825996863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29081515705112572287933077 1363196048677151825996863)
      ·
        refine ⟨2044794073015727738995295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1363196048677151825996863 2044794073015727738995295)
        ·
          refine ⟨3067191109523591608492943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2044794073015727738995295 3067191109523591608492943)
          ·
            refine ⟨4600786664285387412739415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3067191109523591608492943 4600786664285387412739415)
            ·
              refine ⟨6901179996428081119109123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4600786664285387412739415 6901179996428081119109123)
              ·
                refine ⟨10351769994642121678663685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6901179996428081119109123 10351769994642121678663685)
                ·
                  refine ⟨1940956873995397814749441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10351769994642121678663685 1940956873995397814749441)
                  ·
                    refine ⟨1455717655496548361062081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1940956873995397814749441 1455717655496548361062081)
                    ·
                      refine ⟨1091788241622411270796561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1455717655496548361062081 1091788241622411270796561)
                      ·
                        rfl

theorem cell23_2126250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2126250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126250 prefixEnd_2126250 := by exact prefixLift 2126250
  have htrace : WordTrace (prefixWord ++ tailWord_2126250) baseStart_2126250 baseEnd_2126250 := by
    simpa [prefixWord, tailWord_2126250, baseEnd_2126250] using wordTrace_append hprefix tailTrace_2126250
  have hstable : (prefixWord ++ tailWord_2126250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126250).length < 2 ^ (prefixWord ++ tailWord_2126250).sum := by decide
  have hdescent : baseEnd_2126250 < baseStart_2126250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126282 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 3, 4]
def baseStart_2126282 : Nat := 118140960795 + 2126282 * 2 ^ 59
def prefixEnd_2126282 : Nat := 4983230072969 + 3 ^ 40 * 2126282 * 2
def baseEnd_2126282 : Nat := 363934891001118381865471

theorem tailTrace_2126282 : CollatzResearch.WordTrace tailWord_2126282 prefixEnd_2126282 363934891001118381865471 := by
  unfold tailWord_2126282
  simp only [CollatzResearch.WordTrace]
  refine ⟨19387968920712732224913275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51701250455233952599768733 19387968920712732224913275)
  ·
    refine ⟨29081953381069098337369913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19387968920712732224913275 29081953381069098337369913)
    ·
      refine ⟨21811465035801823753027435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29081953381069098337369913 21811465035801823753027435)
      ·
        refine ⟨32717197553702735629541153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21811465035801823753027435 32717197553702735629541153)
        ·
          refine ⟨24537898165277051722155865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32717197553702735629541153 24537898165277051722155865)
          ·
            refine ⟨18403423623957788791616899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24537898165277051722155865 18403423623957788791616899)
            ·
              refine ⟨27605135435936683187425349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18403423623957788791616899 27605135435936683187425349)
              ·
                refine ⟨5175962894238128097642253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27605135435936683187425349 5175962894238128097642253)
                ·
                  refine ⟨1940986085339298036615845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5175962894238128097642253 1940986085339298036615845)
                  ·
                    refine ⟨363934891001118381865471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1940986085339298036615845 363934891001118381865471)
                    ·
                      rfl

theorem cell23_2126282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_2126282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126282 prefixEnd_2126282 := by exact prefixLift 2126282
  have htrace : WordTrace (prefixWord ++ tailWord_2126282) baseStart_2126282 baseEnd_2126282 := by
    simpa [prefixWord, tailWord_2126282, baseEnd_2126282] using wordTrace_append hprefix tailTrace_2126282
  have hstable : (prefixWord ++ tailWord_2126282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126282).length < 2 ^ (prefixWord ++ tailWord_2126282).sum := by decide
  have hdescent : baseEnd_2126282 < baseStart_2126282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126316 : List Nat := [2, 2, 1, 1, 2, 1, 7, 2, 1, 4]
def baseStart_2126316 : Nat := 118140960795 + 2126316 * 2 ^ 59
def prefixEnd_2126316 : Nat := 4983230072969 + 3 ^ 40 * 2126316 * 2
def baseEnd_2126316 : Nat := 363940710448536004190419

theorem tailTrace_2126316 : CollatzResearch.WordTrace tailWord_2126316 prefixEnd_2126316 363940710448536004190419 := by
  unfold tailWord_2126316
  simp only [CollatzResearch.WordTrace]
  refine ⟨38776557882363876353195401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51702077176485168470927201 38776557882363876353195401)
  ·
    refine ⟨29082418411772907264896551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38776557882363876353195401 29082418411772907264896551)
    ·
      refine ⟨43623627617659360897344827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29082418411772907264896551 43623627617659360897344827)
      ·
        refine ⟨65435441426489041346017241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43623627617659360897344827 65435441426489041346017241)
        ·
          refine ⟨49076581069866781009512931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65435441426489041346017241 49076581069866781009512931)
          ·
            refine ⟨73614871604800171514269397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49076581069866781009512931 73614871604800171514269397)
            ·
              refine ⟨1725348553237504019865689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 73614871604800171514269397 1725348553237504019865689)
              ·
                refine ⟨1294011414928128014899267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725348553237504019865689 1294011414928128014899267)
                ·
                  refine ⟨1941017122392192022348901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294011414928128014899267 1941017122392192022348901)
                  ·
                    refine ⟨363940710448536004190419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1941017122392192022348901 363940710448536004190419)
                    ·
                      rfl

theorem cell23_2126316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_2126316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126316 prefixEnd_2126316 := by exact prefixLift 2126316
  have htrace : WordTrace (prefixWord ++ tailWord_2126316) baseStart_2126316 baseEnd_2126316 := by
    simpa [prefixWord, tailWord_2126316, baseEnd_2126316] using wordTrace_append hprefix tailTrace_2126316
  have hstable : (prefixWord ++ tailWord_2126316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126316).length < 2 ^ (prefixWord ++ tailWord_2126316).sum := by decide
  have hdescent : baseEnd_2126316 < baseStart_2126316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126373 : List Nat := [1, 3, 1, 2, 2, 1, 6, 2, 1, 1, 3]
def baseStart_2126373 : Nat := 118140960795 + 2126373 * 2 ^ 59
def prefixEnd_2126373 : Nat := 4983230072969 + 3 ^ 40 * 2126373 * 2
def baseEnd_2126373 : Nat := 1091851399742914289558495

theorem tailTrace_2126373 : CollatzResearch.WordTrace tailWord_2126373 prefixEnd_2126373 1091851399742914289558495 := by
  unfold tailWord_2126373
  simp only [CollatzResearch.WordTrace]
  refine ⟨77555194725521251441215773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51703463150347500960810515 77555194725521251441215773)
  ·
    refine ⟨29083198022070469290455915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77555194725521251441215773 29083198022070469290455915)
    ·
      refine ⟨43624797033105703935683873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29083198022070469290455915 43624797033105703935683873)
      ·
        refine ⟨32718597774829277951762905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43624797033105703935683873 32718597774829277951762905)
        ·
          refine ⟨24538948331121958463822179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32718597774829277951762905 24538948331121958463822179)
          ·
            refine ⟨36808422496682937695733269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24538948331121958463822179 36808422496682937695733269)
            ·
              refine ⟨1725394804532012704487497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36808422496682937695733269 1725394804532012704487497)
              ·
                refine ⟨1294046103399009528365623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1725394804532012704487497 1294046103399009528365623)
                ·
                  refine ⟨1941069155098514292548435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294046103399009528365623 1941069155098514292548435)
                  ·
                    refine ⟨2911603732647771438822653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1941069155098514292548435 2911603732647771438822653)
                    ·
                      refine ⟨1091851399742914289558495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2911603732647771438822653 1091851399742914289558495)
                      ·
                        rfl

theorem cell23_2126373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_2126373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126373 prefixEnd_2126373 := by exact prefixLift 2126373
  have htrace : WordTrace (prefixWord ++ tailWord_2126373) baseStart_2126373 baseEnd_2126373 := by
    simpa [prefixWord, tailWord_2126373, baseEnd_2126373] using wordTrace_append hprefix tailTrace_2126373
  have hstable : (prefixWord ++ tailWord_2126373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126373).length < 2 ^ (prefixWord ++ tailWord_2126373).sum := by decide
  have hdescent : baseEnd_2126373 < baseStart_2126373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126379 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 7, 2, 2]
def baseStart_2126379 : Nat := 118140960795 + 2126379 * 2 ^ 59
def prefixEnd_2126379 : Nat := 4983230072969 + 3 ^ 40 * 2126379 * 2
def baseEnd_2126379 : Nat := 1091854480626841266083467

theorem tailTrace_2126379 : CollatzResearch.WordTrace tailWord_2126379 prefixEnd_2126379 1091854480626841266083467 := by
  unfold tailWord_2126379
  simp only [CollatzResearch.WordTrace]
  refine ⟨77555413563499514465934191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51703609042333009643956127 77555413563499514465934191)
  ·
    refine ⟨116333120345249271698901287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77555413563499514465934191 116333120345249271698901287)
    ·
      refine ⟨174499680517873907548351931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116333120345249271698901287 174499680517873907548351931)
      ·
        refine ⟨261749520776810861322527897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174499680517873907548351931 261749520776810861322527897)
        ·
          refine ⟨196312140582608145991895923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261749520776810861322527897 196312140582608145991895923)
          ·
            refine ⟨294468210873912218987843885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196312140582608145991895923 294468210873912218987843885)
            ·
              refine ⟨110425579077717082120441457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 294468210873912218987843885 110425579077717082120441457)
              ·
                refine ⟨82819184308287811590331093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110425579077717082120441457 82819184308287811590331093)
                ·
                  refine ⟨1941074632225495584148385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 82819184308287811590331093 1941074632225495584148385)
                  ·
                    refine ⟨1455805974169121688111289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1941074632225495584148385 1455805974169121688111289)
                    ·
                      refine ⟨1091854480626841266083467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1455805974169121688111289 1091854480626841266083467)
                      ·
                        rfl

theorem cell23_2126379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 2, 2].length) (baseStart_2126379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126379 prefixEnd_2126379 := by exact prefixLift 2126379
  have htrace : WordTrace (prefixWord ++ tailWord_2126379) baseStart_2126379 baseEnd_2126379 := by
    simpa [prefixWord, tailWord_2126379, baseEnd_2126379] using wordTrace_append hprefix tailTrace_2126379
  have hstable : (prefixWord ++ tailWord_2126379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126379).length < 2 ^ (prefixWord ++ tailWord_2126379).sum := by decide
  have hdescent : baseEnd_2126379 < baseStart_2126379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126389 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 2, 4]
def baseStart_2126389 : Nat := 118140960795 + 2126389 * 2 ^ 59
def prefixEnd_2126389 : Nat := 4983230072969 + 3 ^ 40 * 2126389 * 2
def baseEnd_2126389 : Nat := 363953205144462075652807

theorem tailTrace_2126389 : CollatzResearch.WordTrace tailWord_2126389 prefixEnd_2126389 363953205144462075652807 := by
  unfold tailWord_2126389
  simp only [CollatzResearch.WordTrace]
  refine ⟨77555778293463286173798221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51703852195642190782532147 77555778293463286173798221)
  ·
    refine ⟨29083416860048732315174333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77555778293463286173798221 29083416860048732315174333)
    ·
      refine ⟨10906281322518274618190375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29083416860048732315174333 10906281322518274618190375)
      ·
        refine ⟨16359421983777411927285563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10906281322518274618190375 16359421983777411927285563)
        ·
          refine ⟨24539132975666117890928345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16359421983777411927285563 24539132975666117890928345)
          ·
            refine ⟨18404349731749588418196259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24539132975666117890928345 18404349731749588418196259)
            ·
              refine ⟨27606524597624382627294389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18404349731749588418196259 27606524597624382627294389)
              ·
                refine ⟨2588111681027285871308849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27606524597624382627294389 2588111681027285871308849)
                ·
                  refine ⟨1941083760770464403481637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2588111681027285871308849 1941083760770464403481637)
                  ·
                    refine ⟨363953205144462075652807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1941083760770464403481637 363953205144462075652807)
                    ·
                      rfl

theorem cell23_2126389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_2126389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126389 prefixEnd_2126389 := by exact prefixLift 2126389
  have htrace : WordTrace (prefixWord ++ tailWord_2126389) baseStart_2126389 baseEnd_2126389 := by
    simpa [prefixWord, tailWord_2126389, baseEnd_2126389] using wordTrace_append hprefix tailTrace_2126389
  have hstable : (prefixWord ++ tailWord_2126389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126389).length < 2 ^ (prefixWord ++ tailWord_2126389).sum := by decide
  have hdescent : baseEnd_2126389 < baseStart_2126389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126396 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 5, 2, 2]
def baseStart_2126396 : Nat := 118140960795 + 2126396 * 2 ^ 59
def prefixEnd_2126396 : Nat := 4983230072969 + 3 ^ 40 * 2126396 * 2
def baseEnd_2126396 : Nat := 1091863209797967699570889

theorem tailTrace_2126396 : CollatzResearch.WordTrace tailWord_2126396 prefixEnd_2126396 1091863209797967699570889 := by
  unfold tailWord_2126396
  simp only [CollatzResearch.WordTrace]
  refine ⟨38778016802218963184651521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51704022402958617579535361 38778016802218963184651521)
  ·
    refine ⟨29083512601664222388488641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38778016802218963184651521 29083512601664222388488641)
    ·
      refine ⟨21812634451248166791366481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29083512601664222388488641 21812634451248166791366481)
      ·
        refine ⟨16359475838436125093524861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21812634451248166791366481 16359475838436125093524861)
        ·
          refine ⟨6134803439413546910071823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16359475838436125093524861 6134803439413546910071823)
          ·
            refine ⟨9202205159120320365107735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6134803439413546910071823 9202205159120320365107735)
            ·
              refine ⟨13803307738680480547661603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9202205159120320365107735 13803307738680480547661603)
              ·
                refine ⟨20704961608020720821492405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13803307738680480547661603 20704961608020720821492405)
                ·
                  refine ⟨1941090150751942577014913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20704961608020720821492405 1941090150751942577014913)
                  ·
                    refine ⟨1455817613063956932761185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1941090150751942577014913 1455817613063956932761185)
                    ·
                      refine ⟨1091863209797967699570889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1455817613063956932761185 1091863209797967699570889)
                      ·
                        rfl

theorem cell23_2126396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_2126396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126396 prefixEnd_2126396 := by exact prefixLift 2126396
  have htrace : WordTrace (prefixWord ++ tailWord_2126396) baseStart_2126396 baseEnd_2126396 := by
    simpa [prefixWord, tailWord_2126396, baseEnd_2126396] using wordTrace_append hprefix tailTrace_2126396
  have hstable : (prefixWord ++ tailWord_2126396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126396).length < 2 ^ (prefixWord ++ tailWord_2126396).sum := by decide
  have hdescent : baseEnd_2126396 < baseStart_2126396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126399 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 1, 2, 3]
def baseStart_2126399 : Nat := 118140960795 + 2126399 * 2 ^ 59
def prefixEnd_2126399 : Nat := 4983230072969 + 3 ^ 40 * 2126399 * 2
def baseEnd_2126399 : Nat := 1091864750239931187833375

theorem tailTrace_2126399 : CollatzResearch.WordTrace tailWord_2126399 prefixEnd_2126399 1091864750239931187833375 := by
  unfold tailWord_2126399
  simp only [CollatzResearch.WordTrace]
  refine ⟨77556143023427057881662251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51704095348951371921108167 77556143023427057881662251)
  ·
    refine ⟨116334214535140586822493377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77556143023427057881662251 116334214535140586822493377)
    ·
      refine ⟨87250660901355440116870033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116334214535140586822493377 87250660901355440116870033)
      ·
        refine ⟨65437995676016580087652525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87250660901355440116870033 65437995676016580087652525)
        ·
          refine ⟨24539248378506217532869697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65437995676016580087652525 24539248378506217532869697)
          ·
            refine ⟨18404436283879663149652273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24539248378506217532869697 18404436283879663149652273)
            ·
              refine ⟨13803327212909747362239205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18404436283879663149652273 13803327212909747362239205)
              ·
                refine ⟨2588123852420577630419851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13803327212909747362239205 2588123852420577630419851)
                ·
                  refine ⟨3882185778630866445629777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588123852420577630419851 3882185778630866445629777)
                  ·
                    refine ⟨2911639333973149834222333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3882185778630866445629777 2911639333973149834222333)
                    ·
                      refine ⟨1091864750239931187833375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2911639333973149834222333 1091864750239931187833375)
                      ·
                        rfl

theorem cell23_2126399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_2126399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126399 prefixEnd_2126399 := by exact prefixLift 2126399
  have htrace : WordTrace (prefixWord ++ tailWord_2126399) baseStart_2126399 baseEnd_2126399 := by
    simpa [prefixWord, tailWord_2126399, baseEnd_2126399] using wordTrace_append hprefix tailTrace_2126399
  have hstable : (prefixWord ++ tailWord_2126399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126399).length < 2 ^ (prefixWord ++ tailWord_2126399).sum := by decide
  have hdescent : baseEnd_2126399 < baseStart_2126399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126406 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_2126406 : Nat := 118140960795 + 2126406 * 2 ^ 59
def prefixEnd_2126406 : Nat := 4983230072969 + 3 ^ 40 * 2126406 * 2
def baseEnd_2126406 : Nat := 363956114868170886815281

theorem tailTrace_2126406 : CollatzResearch.WordTrace tailWord_2126406 prefixEnd_2126406 363956114868170886815281 := by
  unfold tailWord_2126406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423637447950053064911471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51704265556267798718111381 2423637447950053064911471)
  ·
    refine ⟨3635456171925079597367207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2423637447950053064911471 3635456171925079597367207)
    ·
      refine ⟨5453184257887619396050811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3635456171925079597367207 5453184257887619396050811)
      ·
        refine ⟨8179776386831429094076217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5453184257887619396050811 8179776386831429094076217)
        ·
          refine ⟨6134832290123571820557163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8179776386831429094076217 6134832290123571820557163)
          ·
            refine ⟨9202248435185357730835745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6134832290123571820557163 9202248435185357730835745)
            ·
              refine ⟨6901686326389018298126809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9202248435185357730835745 6901686326389018298126809)
              ·
                refine ⟨5176264744791763723595107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6901686326389018298126809 5176264744791763723595107)
                ·
                  refine ⟨7764397117187645585392661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5176264744791763723595107 7764397117187645585392661)
                  ·
                    refine ⟨363956114868170886815281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7764397117187645585392661 363956114868170886815281)
                    ·
                      rfl

theorem cell23_2126406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_2126406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126406 prefixEnd_2126406 := by exact prefixLift 2126406
  have htrace : WordTrace (prefixWord ++ tailWord_2126406) baseStart_2126406 baseEnd_2126406 := by
    simpa [prefixWord, tailWord_2126406, baseEnd_2126406] using wordTrace_append hprefix tailTrace_2126406
  have hstable : (prefixWord ++ tailWord_2126406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126406).length < 2 ^ (prefixWord ++ tailWord_2126406).sum := by decide
  have hdescent : baseEnd_2126406 < baseStart_2126406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126413 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_2126413 : Nat := 118140960795 + 2126413 * 2 ^ 59
def prefixEnd_2126413 : Nat := 4983230072969 + 3 ^ 40 * 2126413 * 2
def baseEnd_2126413 : Nat := 1091871938969094133058311

theorem tailTrace_2126413 : CollatzResearch.WordTrace tailWord_2126413 prefixEnd_2126413 1091871938969094133058311 := by
  unfold tailWord_2126413
  simp only [CollatzResearch.WordTrace]
  refine ⟨77556653645376338272671893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51704435763584225515114595 77556653645376338272671893)
  ·
    refine ⟨3635468139627015856531495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77556653645376338272671893 3635468139627015856531495)
    ·
      refine ⟨5453202209440523784797243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3635468139627015856531495 5453202209440523784797243)
      ·
        refine ⟨8179803314160785677195865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5453202209440523784797243 8179803314160785677195865)
        ·
          refine ⟨6134852485620589257896899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8179803314160785677195865 6134852485620589257896899)
          ·
            refine ⟨9202278728430883886845349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6134852485620589257896899 9202278728430883886845349)
            ·
              refine ⟨1725427261580790728783503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9202278728430883886845349 1725427261580790728783503)
              ·
                refine ⟨2588140892371186093175255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1725427261580790728783503 2588140892371186093175255)
                ·
                  refine ⟨3882211338556779139762883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588140892371186093175255 3882211338556779139762883)
                  ·
                    refine ⟨5823317007835168709644325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3882211338556779139762883 5823317007835168709644325)
                    ·
                      refine ⟨1091871938969094133058311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5823317007835168709644325 1091871938969094133058311)
                      ·
                        rfl

theorem cell23_2126413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_2126413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126413 prefixEnd_2126413 := by exact prefixLift 2126413
  have htrace : WordTrace (prefixWord ++ tailWord_2126413) baseStart_2126413 baseEnd_2126413 := by
    simpa [prefixWord, tailWord_2126413, baseEnd_2126413] using wordTrace_append hprefix tailTrace_2126413
  have hstable : (prefixWord ++ tailWord_2126413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126413).length < 2 ^ (prefixWord ++ tailWord_2126413).sum := by decide
  have hdescent : baseEnd_2126413 < baseStart_2126413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126446 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_2126446 : Nat := 118140960795 + 2126446 * 2 ^ 59
def prefixEnd_2126446 : Nat := 4983230072969 + 3 ^ 40 * 2126446 * 2
def baseEnd_2126446 : Nat := 1091888883830692503945659

theorem tailTrace_2126446 : CollatzResearch.WordTrace tailWord_2126446 prefixEnd_2126446 1091888883830692503945659 := by
  unfold tailWord_2126446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9694732156782098113577899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51705238169504523272415461 9694732156782098113577899)
  ·
    refine ⟨14542098235173147170366849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9694732156782098113577899 14542098235173147170366849)
    ·
      refine ⟨10906573676379860377775137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14542098235173147170366849 10906573676379860377775137)
      ·
        refine ⟨8179930257284895283331353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10906573676379860377775137 8179930257284895283331353)
        ·
          refine ⟨6134947692963671462498515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8179930257284895283331353 6134947692963671462498515)
          ·
            refine ⟨9202421539445507193747773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6134947692963671462498515 9202421539445507193747773)
            ·
              refine ⟨3450908077292065197655415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9202421539445507193747773 3450908077292065197655415)
              ·
                refine ⟨5176362115938097796483123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3450908077292065197655415 5176362115938097796483123)
                ·
                  refine ⟨7764543173907146694724685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5176362115938097796483123 7764543173907146694724685)
                  ·
                    refine ⟨2911703690215180010521757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7764543173907146694724685 2911703690215180010521757)
                    ·
                      refine ⟨1091888883830692503945659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2911703690215180010521757 1091888883830692503945659)
                      ·
                        rfl

theorem cell23_2126446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_2126446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126446 prefixEnd_2126446 := by exact prefixLift 2126446
  have htrace : WordTrace (prefixWord ++ tailWord_2126446) baseStart_2126446 baseEnd_2126446 := by
    simpa [prefixWord, tailWord_2126446, baseEnd_2126446] using wordTrace_append hprefix tailTrace_2126446
  have hstable : (prefixWord ++ tailWord_2126446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126446).length < 2 ^ (prefixWord ++ tailWord_2126446).sum := by decide
  have hdescent : baseEnd_2126446 < baseStart_2126446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126453 : List Nat := [1, 3, 4, 2, 3, 1, 2, 7]
def baseStart_2126453 : Nat := 118140960795 + 2126453 * 2 ^ 59
def prefixEnd_2126453 : Nat := 4983230072969 + 3 ^ 40 * 2126453 * 2
def baseEnd_2126453 : Nat := 40440462155380517650301

theorem tailTrace_2126453 : CollatzResearch.WordTrace tailWord_2126453 prefixEnd_2126453 40440462155380517650301 := by
  unfold tailWord_2126453
  simp only [CollatzResearch.WordTrace]
  refine ⟨77558112565231425104128013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51705408376820950069418675 77558112565231425104128013)
  ·
    refine ⟨29084292211961784414048005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77558112565231425104128013 29084292211961784414048005)
    ·
      refine ⟨5453304789742834577634001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29084292211961784414048005 5453304789742834577634001)
      ·
        refine ⟨4089978592307125933225501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5453304789742834577634001 4089978592307125933225501)
        ·
          refine ⟨1533741972115172224959563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4089978592307125933225501 1533741972115172224959563)
          ·
            refine ⟨2300612958172758337439345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533741972115172224959563 2300612958172758337439345)
            ·
              refine ⟨1725459718629568753079509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2300612958172758337439345 1725459718629568753079509)
              ·
                refine ⟨40440462155380517650301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1725459718629568753079509 40440462155380517650301)
                ·
                  rfl

theorem cell23_2126453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 7].length) (baseStart_2126453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126453 prefixEnd_2126453 := by exact prefixLift 2126453
  have htrace : WordTrace (prefixWord ++ tailWord_2126453) baseStart_2126453 baseEnd_2126453 := by
    simpa [prefixWord, tailWord_2126453, baseEnd_2126453] using wordTrace_append hprefix tailTrace_2126453
  have hstable : (prefixWord ++ tailWord_2126453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126453).length < 2 ^ (prefixWord ++ tailWord_2126453).sum := by decide
  have hdescent : baseEnd_2126453 < baseStart_2126453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126497 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 2, 1, 3]
def baseStart_2126497 : Nat := 118140960795 + 2126497 * 2 ^ 59
def prefixEnd_2126497 : Nat := 4983230072969 + 3 ^ 40 * 2126497 * 2
def baseEnd_2126497 : Nat := 1091915071344071804407925

theorem tailTrace_2126497 : CollatzResearch.WordTrace tailWord_2126497 prefixEnd_2126497 1091915071344071804407925 := by
  unfold tailWord_2126497
  simp only [CollatzResearch.WordTrace]
  refine ⟨77559717377072020618729745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51706478251381347079153163 77559717377072020618729745)
  ·
    refine ⟨58169788032804015464047309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77559717377072020618729745 58169788032804015464047309)
    ·
      refine ⟨21813670512301505799017741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58169788032804015464047309 21813670512301505799017741)
      ·
        refine ⟨8180126442113064674631653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21813670512301505799017741 8180126442113064674631653)
        ·
          refine ⟨1533773707896199626493435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8180126442113064674631653 1533773707896199626493435)
          ·
            refine ⟨2300660561844299439740153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1533773707896199626493435 2300660561844299439740153)
            ·
              refine ⟨1725495421383224579805115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2300660561844299439740153 1725495421383224579805115)
              ·
                refine ⟨2588243132074836869707673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1725495421383224579805115 2588243132074836869707673)
                ·
                  refine ⟨1941182349056127652280755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2588243132074836869707673 1941182349056127652280755)
                  ·
                    refine ⟨2911773523584191478421133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1941182349056127652280755 2911773523584191478421133)
                    ·
                      refine ⟨1091915071344071804407925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2911773523584191478421133 1091915071344071804407925)
                      ·
                        rfl

theorem cell23_2126497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_2126497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126497 prefixEnd_2126497 := by exact prefixLift 2126497
  have htrace : WordTrace (prefixWord ++ tailWord_2126497) baseStart_2126497 baseEnd_2126497 := by
    simpa [prefixWord, tailWord_2126497, baseEnd_2126497] using wordTrace_append hprefix tailTrace_2126497
  have hstable : (prefixWord ++ tailWord_2126497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126497).length < 2 ^ (prefixWord ++ tailWord_2126497).sum := by decide
  have hdescent : baseEnd_2126497 < baseStart_2126497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126526 : List Nat := [4, 2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_2126526 : Nat := 118140960795 + 2126526 * 2 ^ 59
def prefixEnd_2126526 : Nat := 4983230072969 + 3 ^ 40 * 2126526 * 2
def baseEnd_2126526 : Nat := 121325551364783576771699

theorem tailTrace_2126526 : CollatzResearch.WordTrace tailWord_2126526 prefixEnd_2126526 121325551364783576771699 := by
  unfold tailWord_2126526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9695096886745869821441929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51707183395977972381023621 9695096886745869821441929)
  ·
    refine ⟨7271322665059402366081447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9695096886745869821441929 7271322665059402366081447)
    ·
      refine ⟨10906983997589103549122171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7271322665059402366081447 10906983997589103549122171)
      ·
        refine ⟨16360475996383655323683257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10906983997589103549122171 16360475996383655323683257)
        ·
          refine ⟨12270356997287741492762443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16360475996383655323683257 12270356997287741492762443)
          ·
            refine ⟨18405535495931612239143665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12270356997287741492762443 18405535495931612239143665)
            ·
              refine ⟨13804151621948709179357749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18405535495931612239143665 13804151621948709179357749)
              ·
                refine ⟨1294139214557691485564789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13804151621948709179357749 1294139214557691485564789)
                ·
                  refine ⟨121325551364783576771699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1294139214557691485564789 121325551364783576771699)
                  ·
                    rfl

theorem cell23_2126526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_2126526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126526 prefixEnd_2126526 := by exact prefixLift 2126526
  have htrace : WordTrace (prefixWord ++ tailWord_2126526) baseStart_2126526 baseEnd_2126526 := by
    simpa [prefixWord, tailWord_2126526, baseEnd_2126526] using wordTrace_append hprefix tailTrace_2126526
  have hstable : (prefixWord ++ tailWord_2126526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126526).length < 2 ^ (prefixWord ++ tailWord_2126526).sum := by decide
  have hdescent : baseEnd_2126526 < baseStart_2126526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126569 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 5, 4]
def baseStart_2126569 : Nat := 118140960795 + 2126569 * 2 ^ 59
def prefixEnd_2126569 : Nat := 4983230072969 + 3 ^ 40 * 2126569 * 2
def baseEnd_2126569 : Nat := 363984013983731840902531

theorem tailTrace_2126569 : CollatzResearch.WordTrace tailWord_2126569 prefixEnd_2126569 363984013983731840902531 := by
  unfold tailWord_2126569
  simp only [CollatzResearch.WordTrace]
  refine ⟨77562343432811176915350761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51708228955207451276900507 77562343432811176915350761)
  ·
    refine ⟨58171757574608382686513071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77562343432811176915350761 58171757574608382686513071)
    ·
      refine ⟨87257636361912574029769607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58171757574608382686513071 87257636361912574029769607)
      ·
        refine ⟨130886454542868861044654411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87257636361912574029769607 130886454542868861044654411)
        ·
          refine ⟨196329681814303291566981617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130886454542868861044654411 196329681814303291566981617)
          ·
            refine ⟨147247261360727468675236213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196329681814303291566981617 147247261360727468675236213)
            ·
              refine ⟨13804430752568200188303395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147247261360727468675236213 13804430752568200188303395)
              ·
                refine ⟨20706646128852300282455093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13804430752568200188303395 20706646128852300282455093)
                ·
                  refine ⟨1941248074579903151480165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20706646128852300282455093 1941248074579903151480165)
                  ·
                    refine ⟨363984013983731840902531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1941248074579903151480165 363984013983731840902531)
                    ·
                      rfl

theorem cell23_2126569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 4].length) (baseStart_2126569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126569 prefixEnd_2126569 := by exact prefixLift 2126569
  have htrace : WordTrace (prefixWord ++ tailWord_2126569) baseStart_2126569 baseEnd_2126569 := by
    simpa [prefixWord, tailWord_2126569, baseEnd_2126569] using wordTrace_append hprefix tailTrace_2126569
  have hstable : (prefixWord ++ tailWord_2126569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126569).length < 2 ^ (prefixWord ++ tailWord_2126569).sum := by decide
  have hdescent : baseEnd_2126569 < baseStart_2126569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126596 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_2126596 : Nat := 118140960795 + 2126596 * 2 ^ 59
def prefixEnd_2126596 : Nat := 4983230072969 + 3 ^ 40 * 2126596 * 2
def baseEnd_2126596 : Nat := 1091965905928866917069969

theorem tailTrace_2126596 : CollatzResearch.WordTrace tailWord_2126596 prefixEnd_2126596 1091965905928866917069969 := by
  unfold tailWord_2126596
  simp only [CollatzResearch.WordTrace]
  refine ⟨38781664101856680263291821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51708885469142240351055761 38781664101856680263291821)
  ·
    refine ⟨14543124038196255098734433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38781664101856680263291821 14543124038196255098734433)
    ·
      refine ⟨10907343028647191324050825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14543124038196255098734433 10907343028647191324050825)
      ·
        refine ⟨8180507271485393493038119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10907343028647191324050825 8180507271485393493038119)
        ·
          refine ⟨12270760907228090239557179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8180507271485393493038119 12270760907228090239557179)
          ·
            refine ⟨18406141360842135359335769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12270760907228090239557179 18406141360842135359335769)
            ·
              refine ⟨13804606020631601519501827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18406141360842135359335769 13804606020631601519501827)
              ·
                refine ⟨20706909030947402279252741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13804606020631601519501827 20706909030947402279252741)
                ·
                  refine ⟨3882545443302637927359889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20706909030947402279252741 3882545443302637927359889)
                  ·
                    refine ⟨2911909082476978445519917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3882545443302637927359889 2911909082476978445519917)
                    ·
                      refine ⟨1091965905928866917069969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2911909082476978445519917 1091965905928866917069969)
                      ·
                        rfl

theorem cell23_2126596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_2126596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126596 prefixEnd_2126596 := by exact prefixLift 2126596
  have htrace : WordTrace (prefixWord ++ tailWord_2126596) baseStart_2126596 baseEnd_2126596 := by
    simpa [prefixWord, tailWord_2126596, baseEnd_2126596] using wordTrace_append hprefix tailTrace_2126596
  have hstable : (prefixWord ++ tailWord_2126596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126596).length < 2 ^ (prefixWord ++ tailWord_2126596).sum := by decide
  have hdescent : baseEnd_2126596 < baseStart_2126596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126636 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 1, 5, 2]
def baseStart_2126636 : Nat := 118140960795 + 2126636 * 2 ^ 59
def prefixEnd_2126636 : Nat := 4983230072969 + 3 ^ 40 * 2126636 * 2
def baseEnd_2126636 : Nat := 1091986445155046760569785

theorem tailTrace_2126636 : CollatzResearch.WordTrace tailWord_2126636 prefixEnd_2126636 1091986445155046760569785 := by
  unfold tailWord_2126636
  simp only [CollatzResearch.WordTrace]
  refine ⟨38782393561784223679019881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51709858082378964905359841 38782393561784223679019881)
  ·
    refine ⟨29086795171338167759264911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38782393561784223679019881 29086795171338167759264911)
    ·
      refine ⟨43630192757007251638897367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29086795171338167759264911 43630192757007251638897367)
      ·
        refine ⟨65445289135510877458346051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43630192757007251638897367 65445289135510877458346051)
        ·
          refine ⟨98167933703266316187519077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65445289135510877458346051 98167933703266316187519077)
          ·
            refine ⟨18406487569362434285159827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98167933703266316187519077 18406487569362434285159827)
            ·
              refine ⟨27609731354043651427739741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18406487569362434285159827 27609731354043651427739741)
              ·
                refine ⟨10353649257766369285402403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27609731354043651427739741 10353649257766369285402403)
                ·
                  refine ⟨15530473886649553928103605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10353649257766369285402403 15530473886649553928103605)
                  ·
                    refine ⟨1455981926873395680759713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15530473886649553928103605 1455981926873395680759713)
                    ·
                      refine ⟨1091986445155046760569785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1455981926873395680759713 1091986445155046760569785)
                      ·
                        rfl

theorem cell23_2126636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 5, 2].length) (baseStart_2126636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126636 prefixEnd_2126636 := by exact prefixLift 2126636
  have htrace : WordTrace (prefixWord ++ tailWord_2126636) baseStart_2126636 baseEnd_2126636 := by
    simpa [prefixWord, tailWord_2126636, baseEnd_2126636] using wordTrace_append hprefix tailTrace_2126636
  have hstable : (prefixWord ++ tailWord_2126636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126636).length < 2 ^ (prefixWord ++ tailWord_2126636).sum := by decide
  have hdescent : baseEnd_2126636 < baseStart_2126636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126666 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2]
def baseStart_2126666 : Nat := 118140960795 + 2126666 * 2 ^ 59
def prefixEnd_2126666 : Nat := 4983230072969 + 3 ^ 40 * 2126666 * 2
def baseEnd_2126666 : Nat := 1092001849574681643194647

theorem tailTrace_2126666 : CollatzResearch.WordTrace tailWord_2126666 prefixEnd_2126666 1092001849574681643194647 := by
  unfold tailWord_2126666
  simp only [CollatzResearch.WordTrace]
  refine ⟨19391470328364940620407963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51710587542306508321087901 19391470328364940620407963)
  ·
    refine ⟨29087205492547410930611945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19391470328364940620407963 29087205492547410930611945)
    ·
      refine ⟨21815404119410558197958959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29087205492547410930611945 21815404119410558197958959)
      ·
        refine ⟨32723106179115837296938439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21815404119410558197958959 32723106179115837296938439)
        ·
          refine ⟨49084659268673755945407659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32723106179115837296938439 49084659268673755945407659)
          ·
            refine ⟨73626988903010633918111489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49084659268673755945407659 73626988903010633918111489)
            ·
              refine ⟨55220241677257975438583617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73626988903010633918111489 55220241677257975438583617)
              ·
                refine ⟨41415181257943481578937713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55220241677257975438583617 41415181257943481578937713)
                ·
                  refine ⟨31061385943457611184203285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41415181257943481578937713 31061385943457611184203285)
                  ·
                    refine ⟨1456002466099575524259529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31061385943457611184203285 1456002466099575524259529)
                    ·
                      refine ⟨1092001849574681643194647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456002466099575524259529 1092001849574681643194647)
                      ·
                        rfl

theorem cell23_2126666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_2126666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126666 prefixEnd_2126666 := by exact prefixLift 2126666
  have htrace : WordTrace (prefixWord ++ tailWord_2126666) baseStart_2126666 baseEnd_2126666 := by
    simpa [prefixWord, tailWord_2126666, baseEnd_2126666] using wordTrace_append hprefix tailTrace_2126666
  have hstable : (prefixWord ++ tailWord_2126666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126666).length < 2 ^ (prefixWord ++ tailWord_2126666).sum := by decide
  have hdescent : baseEnd_2126666 < baseStart_2126666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126696 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2126696 : Nat := 118140960795 + 2126696 * 2 ^ 59
def prefixEnd_2126696 : Nat := 4983230072969 + 3 ^ 40 * 2126696 * 2
def baseEnd_2126696 : Nat := 1092017253994316525819509

theorem tailTrace_2126696 : CollatzResearch.WordTrace tailWord_2126696 prefixEnd_2126696 1092017253994316525819509 := by
  unfold tailWord_2126696
  simp only [CollatzResearch.WordTrace]
  refine ⟨38783487751675538802611971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51711317002234051736815961 38783487751675538802611971)
  ·
    refine ⟨58175231627513308203917957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38783487751675538802611971 58175231627513308203917957)
    ·
      refine ⟨10907855930158745288234617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58175231627513308203917957 10907855930158745288234617)
      ·
        refine ⟨8180891947619058966175963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10907855930158745288234617 8180891947619058966175963)
        ·
          refine ⟨12271337921428588449263945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8180891947619058966175963 12271337921428588449263945)
          ·
            refine ⟨9203503441071441336947959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12271337921428588449263945 9203503441071441336947959)
            ·
              refine ⟨13805255161607162005421939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9203503441071441336947959 13805255161607162005421939)
              ·
                refine ⟨20707882742410743008132909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13805255161607162005421939 20707882742410743008132909)
                ·
                  refine ⟨7765456028404028628049841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20707882742410743008132909 7765456028404028628049841)
                  ·
                    refine ⟨5824092021303021471037381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7765456028404028628049841 5824092021303021471037381)
                    ·
                      refine ⟨1092017253994316525819509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5824092021303021471037381 1092017253994316525819509)
                      ·
                        rfl

theorem cell23_2126696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2126696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126696 prefixEnd_2126696 := by exact prefixLift 2126696
  have htrace : WordTrace (prefixWord ++ tailWord_2126696) baseStart_2126696 baseEnd_2126696 := by
    simpa [prefixWord, tailWord_2126696, baseEnd_2126696] using wordTrace_append hprefix tailTrace_2126696
  have hstable : (prefixWord ++ tailWord_2126696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126696).length < 2 ^ (prefixWord ++ tailWord_2126696).sum := by decide
  have hdescent : baseEnd_2126696 < baseStart_2126696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126710 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_2126710 : Nat := 118140960795 + 2126710 * 2 ^ 59
def prefixEnd_2126710 : Nat := 4983230072969 + 3 ^ 40 * 2126710 * 2
def baseEnd_2126710 : Nat := 364008147574493157014815

theorem tailTrace_2126710 : CollatzResearch.WordTrace tailWord_2126710 prefixEnd_2126710 364008147574493157014815 := by
  unfold tailWord_2126710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4847967882831272374764599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51711657416866905330822389 4847967882831272374764599)
  ·
    refine ⟨7271951824246908562146899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4847967882831272374764599 7271951824246908562146899)
    ·
      refine ⟨10907927736370362843220349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7271951824246908562146899 10907927736370362843220349)
      ·
        refine ⟨4090472901138886066207631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10907927736370362843220349 4090472901138886066207631)
        ·
          refine ⟨6135709351708329099311447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4090472901138886066207631 6135709351708329099311447)
          ·
            refine ⟨9203564027562493648967171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6135709351708329099311447 9203564027562493648967171)
            ·
              refine ⟨13805346041343740473450757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9203564027562493648967171 13805346041343740473450757)
              ·
                refine ⟨2588502382751951338772017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13805346041343740473450757 2588502382751951338772017)
                ·
                  refine ⟨1941376787063963504079013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2588502382751951338772017 1941376787063963504079013)
                  ·
                    refine ⟨364008147574493157014815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1941376787063963504079013 364008147574493157014815)
                    ·
                      rfl

theorem cell23_2126710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_2126710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126710 prefixEnd_2126710 := by exact prefixLift 2126710
  have htrace : WordTrace (prefixWord ++ tailWord_2126710) baseStart_2126710 baseEnd_2126710 := by
    simpa [prefixWord, tailWord_2126710, baseEnd_2126710] using wordTrace_append hprefix tailTrace_2126710
  have hstable : (prefixWord ++ tailWord_2126710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126710).length < 2 ^ (prefixWord ++ tailWord_2126710).sum := by decide
  have hdescent : baseEnd_2126710 < baseStart_2126710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126719 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 2, 7]
def baseStart_2126719 : Nat := 118140960795 + 2126719 * 2 ^ 59
def prefixEnd_2126719 : Nat := 4983230072969 + 3 ^ 40 * 2126719 * 2
def baseEnd_2126719 : Nat := 364009688016456645277301

theorem tailTrace_2126719 : CollatzResearch.WordTrace tailWord_2126719 prefixEnd_2126719 364009688016456645277301 := by
  unfold tailWord_2126719
  simp only [CollatzResearch.WordTrace]
  refine ⟨77567814382267752533311211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51711876254845168355540807 77567814382267752533311211)
  ·
    refine ⟨116351721573401628799966817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77567814382267752533311211 116351721573401628799966817)
    ·
      refine ⟨87263791180051221599975113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116351721573401628799966817 87263791180051221599975113)
      ·
        refine ⟨65447843385038416199981335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87263791180051221599975113 65447843385038416199981335)
        ·
          refine ⟨98171765077557624299972003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65447843385038416199981335 98171765077557624299972003)
          ·
            refine ⟨147257647616336436449958005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98171765077557624299972003 147257647616336436449958005)
            ·
              refine ⟨13805404464031540917183563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 147257647616336436449958005 13805404464031540917183563)
              ·
                refine ⟨20708106696047311375775345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13805404464031540917183563 20708106696047311375775345)
                ·
                  refine ⟨15531080022035483531831509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20708106696047311375775345 15531080022035483531831509)
                  ·
                    refine ⟨364009688016456645277301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15531080022035483531831509 364009688016456645277301)
                    ·
                      rfl

theorem cell23_2126719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_2126719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126719 prefixEnd_2126719 := by exact prefixLift 2126719
  have htrace : WordTrace (prefixWord ++ tailWord_2126719) baseStart_2126719 baseEnd_2126719 := by
    simpa [prefixWord, tailWord_2126719, baseEnd_2126719] using wordTrace_append hprefix tailTrace_2126719
  have hstable : (prefixWord ++ tailWord_2126719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126719).length < 2 ^ (prefixWord ++ tailWord_2126719).sum := by decide
  have hdescent : baseEnd_2126719 < baseStart_2126719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126743 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 3, 3, 2]
def baseStart_2126743 : Nat := 118140960795 + 2126743 * 2 ^ 59
def prefixEnd_2126743 : Nat := 4983230072969 + 3 ^ 40 * 2126743 * 2
def baseEnd_2126743 : Nat := 1092041387585077841931793

theorem tailTrace_2126743 : CollatzResearch.WordTrace tailWord_2126743 prefixEnd_2126743 1092041387585077841931793 := by
  unfold tailWord_2126743
  simp only [CollatzResearch.WordTrace]
  refine ⟨77568689734180804632184883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51712459822787203088123255 77568689734180804632184883)
  ·
    refine ⟨116353034601271206948277325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77568689734180804632184883 116353034601271206948277325)
    ·
      refine ⟨43632387975476702605603997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116353034601271206948277325 43632387975476702605603997)
      ·
        refine ⟨16362145490803763477101499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43632387975476702605603997 16362145490803763477101499)
        ·
          refine ⟨24543218236205645215652249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16362145490803763477101499 24543218236205645215652249)
          ·
            refine ⟨18407413677154233911739187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24543218236205645215652249 18407413677154233911739187)
            ·
              refine ⟨27611120515731350867608781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18407413677154233911739187 27611120515731350867608781)
              ·
                refine ⟨10354170193399256575353293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27611120515731350867608781 10354170193399256575353293)
                ·
                  refine ⟨3882813822524721215757485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10354170193399256575353293 3882813822524721215757485)
                  ·
                    refine ⟨1456055183446770455909057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3882813822524721215757485 1456055183446770455909057)
                    ·
                      refine ⟨1092041387585077841931793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456055183446770455909057 1092041387585077841931793)
                      ·
                        rfl

theorem cell23_2126743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_2126743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126743 prefixEnd_2126743 := by exact prefixLift 2126743
  have htrace : WordTrace (prefixWord ++ tailWord_2126743) baseStart_2126743 baseEnd_2126743 := by
    simpa [prefixWord, tailWord_2126743, baseEnd_2126743] using wordTrace_append hprefix tailTrace_2126743
  have hstable : (prefixWord ++ tailWord_2126743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126743).length < 2 ^ (prefixWord ++ tailWord_2126743).sum := by decide
  have hdescent : baseEnd_2126743 < baseStart_2126743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126796 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 7]
def baseStart_2126796 : Nat := 118140960795 + 2126796 * 2 ^ 59
def prefixEnd_2126796 : Nat := 4983230072969 + 3 ^ 40 * 2126796 * 2
def baseEnd_2126796 : Nat := 121340955784418459396561

theorem tailTrace_2126796 : CollatzResearch.WordTrace tailWord_2126796 prefixEnd_2126796 121340955784418459396561 := by
  unfold tailWord_2126796
  simp only [CollatzResearch.WordTrace]
  refine ⟨38785311401494397341932121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51713748535325863122576161 38785311401494397341932121)
  ·
    refine ⟨29088983551120798006449091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38785311401494397341932121 29088983551120798006449091)
    ·
      refine ⟨43633475326681197009673637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29088983551120798006449091 43633475326681197009673637)
      ·
        refine ⟨8181276623752724439313807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43633475326681197009673637 8181276623752724439313807)
        ·
          refine ⟨12271914935629086658970711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8181276623752724439313807 12271914935629086658970711)
          ·
            refine ⟨18407872403443629988456067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12271914935629086658970711 18407872403443629988456067)
            ·
              refine ⟨27611808605165444982684101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18407872403443629988456067 27611808605165444982684101)
              ·
                refine ⟨5177214113468520934253269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27611808605165444982684101 5177214113468520934253269)
                ·
                  refine ⟨121340955784418459396561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5177214113468520934253269 121340955784418459396561)
                  ·
                    rfl

theorem cell23_2126796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_2126796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126796 prefixEnd_2126796 := by exact prefixLift 2126796
  have htrace : WordTrace (prefixWord ++ tailWord_2126796) baseStart_2126796 baseEnd_2126796 := by
    simpa [prefixWord, tailWord_2126796, baseEnd_2126796] using wordTrace_append hprefix tailTrace_2126796
  have hstable : (prefixWord ++ tailWord_2126796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126796).length < 2 ^ (prefixWord ++ tailWord_2126796).sum := by decide
  have hdescent : baseEnd_2126796 < baseStart_2126796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126830 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_2126830 : Nat := 118140960795 + 2126830 * 2 ^ 59
def prefixEnd_2126830 : Nat := 4983230072969 + 3 ^ 40 * 2126830 * 2
def baseEnd_2126830 : Nat := 121342895600224333504877

theorem tailTrace_2126830 : CollatzResearch.WordTrace tailWord_2126830 prefixEnd_2126830 121342895600224333504877 := by
  unfold tailWord_2126830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9696482860608202311325243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51714575256577078993734629 9696482860608202311325243)
  ·
    refine ⟨14544724290912303466987865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9696482860608202311325243 14544724290912303466987865)
    ·
      refine ⟨10908543218184227600240899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14544724290912303466987865 10908543218184227600240899)
      ·
        refine ⟨16362814827276341400361349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10908543218184227600240899 16362814827276341400361349)
        ·
          refine ⟨3068027780114314012567753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16362814827276341400361349 3068027780114314012567753)
          ·
            refine ⟨2301020835085735509425815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3068027780114314012567753 2301020835085735509425815)
            ·
              refine ⟨3451531252628603264138723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301020835085735509425815 3451531252628603264138723)
              ·
                refine ⟨5177296878942904896208085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3451531252628603264138723 5177296878942904896208085)
                ·
                  refine ⟨121342895600224333504877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5177296878942904896208085 121342895600224333504877)
                  ·
                    rfl

theorem cell23_2126830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_2126830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126830 prefixEnd_2126830 := by exact prefixLift 2126830
  have htrace : WordTrace (prefixWord ++ tailWord_2126830) baseStart_2126830 baseEnd_2126830 := by
    simpa [prefixWord, tailWord_2126830, baseEnd_2126830] using wordTrace_append hprefix tailTrace_2126830
  have hstable : (prefixWord ++ tailWord_2126830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126830).length < 2 ^ (prefixWord ++ tailWord_2126830).sum := by decide
  have hdescent : baseEnd_2126830 < baseStart_2126830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126973 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_2126973 : Nat := 118140960795 + 2126973 * 2 ^ 59
def prefixEnd_2126973 : Nat := 4983230072969 + 3 ^ 40 * 2126973 * 2
def baseEnd_2126973 : Nat := 1092159488135611942055735

theorem tailTrace_2126973 : CollatzResearch.WordTrace tailWord_2126973 prefixEnd_2126973 1092159488135611942055735 := by
  unfold tailWord_2126973
  simp only [CollatzResearch.WordTrace]
  refine ⟨77577078523347553913057573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51718052348898369275371715 77577078523347553913057573)
  ·
    refine ⟨14545702223127666358698295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77577078523347553913057573 14545702223127666358698295)
    ·
      refine ⟨21818553334691499538047443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14545702223127666358698295 21818553334691499538047443)
      ·
        refine ⟨32727830002037249307071165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21818553334691499538047443 32727830002037249307071165)
        ·
          refine ⟨12272936250763968490151687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32727830002037249307071165 12272936250763968490151687)
          ·
            refine ⟨18409404376145952735227531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12272936250763968490151687 18409404376145952735227531)
            ·
              refine ⟨27614106564218929102841297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18409404376145952735227531 27614106564218929102841297)
              ·
                refine ⟨20710579923164196827130973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27614106564218929102841297 20710579923164196827130973)
                ·
                  refine ⟨7766467471186573810174115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20710579923164196827130973 7766467471186573810174115)
                  ·
                    refine ⟨11649701206779860715261173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7766467471186573810174115 11649701206779860715261173)
                    ·
                      refine ⟨1092159488135611942055735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11649701206779860715261173 1092159488135611942055735)
                      ·
                        rfl

theorem cell23_2126973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_2126973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126973 prefixEnd_2126973 := by exact prefixLift 2126973
  have htrace : WordTrace (prefixWord ++ tailWord_2126973) baseStart_2126973 baseEnd_2126973 := by
    simpa [prefixWord, tailWord_2126973, baseEnd_2126973] using wordTrace_append hprefix tailTrace_2126973
  have hstable : (prefixWord ++ tailWord_2126973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126973).length < 2 ^ (prefixWord ++ tailWord_2126973).sum := by decide
  have hdescent : baseEnd_2126973 < baseStart_2126973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126980 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_2126980 : Nat := 118140960795 + 2126980 * 2 ^ 59
def prefixEnd_2126980 : Nat := 4983230072969 + 3 ^ 40 * 2126980 * 2
def baseEnd_2126980 : Nat := 364054360833397804889401

theorem tailTrace_2126980 : CollatzResearch.WordTrace tailWord_2126980 prefixEnd_2126980 364054360833397804889401 := by
  unfold tailWord_2126980
  simp only [CollatzResearch.WordTrace]
  refine ⟨38788666917161097054281197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51718222556214796072374929 38788666917161097054281197)
  ·
    refine ⟨14545750093935411395355449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38788666917161097054281197 14545750093935411395355449)
    ·
      refine ⟨10909312570451558546516587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14545750093935411395355449 10909312570451558546516587)
      ·
        refine ⟨16363968855677337819774881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10909312570451558546516587 16363968855677337819774881)
        ·
          refine ⟨12272976641758003364831161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16363968855677337819774881 12272976641758003364831161)
          ·
            refine ⟨9204732481318502523623371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12272976641758003364831161 9204732481318502523623371)
            ·
              refine ⟨13807098721977753785435057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9204732481318502523623371 13807098721977753785435057)
              ·
                refine ⟨10355324041483315339076293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13807098721977753785435057 10355324041483315339076293)
                ·
                  refine ⟨1941623257778121626076805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10355324041483315339076293 1941623257778121626076805)
                  ·
                    refine ⟨364054360833397804889401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1941623257778121626076805 364054360833397804889401)
                    ·
                      rfl

theorem cell23_2126980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_2126980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126980 prefixEnd_2126980 := by exact prefixLift 2126980
  have htrace : WordTrace (prefixWord ++ tailWord_2126980) baseStart_2126980 baseEnd_2126980 := by
    simpa [prefixWord, tailWord_2126980, baseEnd_2126980] using wordTrace_append hprefix tailTrace_2126980
  have hstable : (prefixWord ++ tailWord_2126980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126980).length < 2 ^ (prefixWord ++ tailWord_2126980).sum := by decide
  have hdescent : baseEnd_2126980 < baseStart_2126980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126981 : List Nat := [1, 3, 1, 1, 6, 2, 1, 3, 1, 1, 3]
def baseStart_2126981 : Nat := 118140960795 + 2126981 * 2 ^ 59
def prefixEnd_2126981 : Nat := 4983230072969 + 3 ^ 40 * 2126981 * 2
def baseEnd_2126981 : Nat := 1092163595980847910755699

theorem tailTrace_2126981 : CollatzResearch.WordTrace tailWord_2126981 prefixEnd_2126981 1092163595980847910755699 := by
  unfold tailWord_2126981
  simp only [CollatzResearch.WordTrace]
  refine ⟨77577370307318571279348797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51718246871545714186232531 77577370307318571279348797)
  ·
    refine ⟨29091513865244464229755799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77577370307318571279348797 29091513865244464229755799)
    ·
      refine ⟨43637270797866696344633699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29091513865244464229755799 43637270797866696344633699)
      ·
        refine ⟨65455906196800044516950549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43637270797866696344633699 65455906196800044516950549)
        ·
          refine ⟨3068245602975002086732057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65455906196800044516950549 3068245602975002086732057)
          ·
            refine ⟨2301184202231251565049043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3068245602975002086732057 2301184202231251565049043)
            ·
              refine ⟨3451776303346877347573565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301184202231251565049043 3451776303346877347573565)
              ·
                refine ⟨1294416113755079005340087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3451776303346877347573565 1294416113755079005340087)
                ·
                  refine ⟨1941624170632618508010131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294416113755079005340087 1941624170632618508010131)
                  ·
                    refine ⟨2912436255948927762015197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1941624170632618508010131 2912436255948927762015197)
                    ·
                      refine ⟨1092163595980847910755699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2912436255948927762015197 1092163595980847910755699)
                      ·
                        rfl

theorem cell23_2126981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 1, 1, 3].length) (baseStart_2126981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126981 prefixEnd_2126981 := by exact prefixLift 2126981
  have htrace : WordTrace (prefixWord ++ tailWord_2126981) baseStart_2126981 baseEnd_2126981 := by
    simpa [prefixWord, tailWord_2126981, baseEnd_2126981] using wordTrace_append hprefix tailTrace_2126981
  have hstable : (prefixWord ++ tailWord_2126981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126981).length < 2 ^ (prefixWord ++ tailWord_2126981).sum := by decide
  have hdescent : baseEnd_2126981 < baseStart_2126981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126983 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_2126983 : Nat := 118140960795 + 2126983 * 2 ^ 59
def prefixEnd_2126983 : Nat := 4983230072969 + 3 ^ 40 * 2126983 * 2
def baseEnd_2126983 : Nat := 1092164622942156902930689

theorem tailTrace_2126983 : CollatzResearch.WordTrace tailWord_2126983 prefixEnd_2126983 1092164622942156902930689 := by
  unfold tailWord_2126983
  simp only [CollatzResearch.WordTrace]
  refine ⟨77577443253311325620921603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51718295502207550413947735 77577443253311325620921603)
  ·
    refine ⟨116366164879966988431382405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77577443253311325620921603 116366164879966988431382405)
    ·
      refine ⟨21818655914993810330884201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116366164879966988431382405 21818655914993810330884201)
      ·
        refine ⟨16363991936245357748163151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21818655914993810330884201 16363991936245357748163151)
        ·
          refine ⟨24545987904368036622244727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16363991936245357748163151 24545987904368036622244727)
          ·
            refine ⟨36818981856552054933367091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24545987904368036622244727 36818981856552054933367091)
            ·
              refine ⟨55228472784828082400050637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36818981856552054933367091 55228472784828082400050637)
              ·
                refine ⟨20710677294310530900018989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55228472784828082400050637 20710677294310530900018989)
                ·
                  refine ⟨7766503985366449087507121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20710677294310530900018989 7766503985366449087507121)
                  ·
                    refine ⟨5824877989024836815630341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7766503985366449087507121 5824877989024836815630341)
                    ·
                      refine ⟨1092164622942156902930689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5824877989024836815630341 1092164622942156902930689)
                      ·
                        rfl

theorem cell23_2126983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_2126983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126983 prefixEnd_2126983 := by exact prefixLift 2126983
  have htrace : WordTrace (prefixWord ++ tailWord_2126983) baseStart_2126983 baseEnd_2126983 := by
    simpa [prefixWord, tailWord_2126983, baseEnd_2126983] using wordTrace_append hprefix tailTrace_2126983
  have hstable : (prefixWord ++ tailWord_2126983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126983).length < 2 ^ (prefixWord ++ tailWord_2126983).sum := by decide
  have hdescent : baseEnd_2126983 < baseStart_2126983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2126990 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2126990 : Nat := 118140960795 + 2126990 * 2 ^ 59
def prefixEnd_2126990 : Nat := 4983230072969 + 3 ^ 40 * 2126990 * 2
def baseEnd_2126990 : Nat := 1092168217306738375543157

theorem tailTrace_2126990 : CollatzResearch.WordTrace tailWord_2126990 prefixEnd_2126990 1092168217306738375543157 := by
  unfold tailWord_2126990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9697212320535745727053303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51718465709523977210950949 9697212320535745727053303)
  ·
    refine ⟨14545818480803618590579955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9697212320535745727053303 14545818480803618590579955)
    ·
      refine ⟨21818727721205427885869933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14545818480803618590579955 21818727721205427885869933)
      ·
        refine ⟨8182022895452035457201225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21818727721205427885869933 8182022895452035457201225)
        ·
          refine ⟨6136517171589026592900919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8182022895452035457201225 6136517171589026592900919)
          ·
            refine ⟨9204775757383539889351379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6136517171589026592900919 9204775757383539889351379)
            ·
              refine ⟨13807163636075309834027069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9204775757383539889351379 13807163636075309834027069)
              ·
                refine ⟨5177686363528241187760151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13807163636075309834027069 5177686363528241187760151)
                ·
                  refine ⟨7766529545292361781640227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5177686363528241187760151 7766529545292361781640227)
                  ·
                    refine ⟨11649794317938542672460341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7766529545292361781640227 11649794317938542672460341)
                    ·
                      refine ⟨1092168217306738375543157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11649794317938542672460341 1092168217306738375543157)
                      ·
                        rfl

theorem cell23_2126990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2126990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2126990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2126990 prefixEnd_2126990 := by exact prefixLift 2126990
  have htrace : WordTrace (prefixWord ++ tailWord_2126990) baseStart_2126990 baseEnd_2126990 := by
    simpa [prefixWord, tailWord_2126990, baseEnd_2126990] using wordTrace_append hprefix tailTrace_2126990
  have hstable : (prefixWord ++ tailWord_2126990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2126990).length < 2 ^ (prefixWord ++ tailWord_2126990).sum := by decide
  have hdescent : baseEnd_2126990 < baseStart_2126990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2126990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127004 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_2127004 : Nat := 118140960795 + 2127004 * 2 ^ 59
def prefixEnd_2127004 : Nat := 4983230072969 + 3 ^ 40 * 2127004 * 2
def baseEnd_2127004 : Nat := 1092175406035901320768093

theorem tailTrace_2127004 : CollatzResearch.WordTrace tailWord_2127004 prefixEnd_2127004 1092175406035901320768093 := by
  unfold tailWord_2127004
  simp only [CollatzResearch.WordTrace]
  refine ⟨38789104593117623103718033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51718806124156830804957377 38789104593117623103718033)
  ·
    refine ⟨29091828444838217327788525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38789104593117623103718033 29091828444838217327788525)
    ·
      refine ⟨10909435666814331497920697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29091828444838217327788525 10909435666814331497920697)
      ·
        refine ⟨8182076750110748623440523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10909435666814331497920697 8182076750110748623440523)
        ·
          refine ⟨12273115125166122935160785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8182076750110748623440523 12273115125166122935160785)
          ·
            refine ⟨9204836343874592201370589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12273115125166122935160785 9204836343874592201370589)
            ·
              refine ⟨3451813628952972075513971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9204836343874592201370589 3451813628952972075513971)
              ·
                refine ⟨5177720443429458113270957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3451813628952972075513971 5177720443429458113270957)
                ·
                  refine ⟨1941645166286046792476609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5177720443429458113270957 1941645166286046792476609)
                  ·
                    refine ⟨1456233874714535094357457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1941645166286046792476609 1456233874714535094357457)
                    ·
                      refine ⟨1092175406035901320768093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456233874714535094357457 1092175406035901320768093)
                      ·
                        rfl

theorem cell23_2127004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_2127004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127004 prefixEnd_2127004 := by exact prefixLift 2127004
  have htrace : WordTrace (prefixWord ++ tailWord_2127004) baseStart_2127004 baseEnd_2127004 := by
    simpa [prefixWord, tailWord_2127004, baseEnd_2127004] using wordTrace_append hprefix tailTrace_2127004
  have hstable : (prefixWord ++ tailWord_2127004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127004).length < 2 ^ (prefixWord ++ tailWord_2127004).sum := by decide
  have hdescent : baseEnd_2127004 < baseStart_2127004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127020 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 3]
def baseStart_2127020 : Nat := 118140960795 + 2127020 * 2 ^ 59
def prefixEnd_2127020 : Nat := 4983230072969 + 3 ^ 40 * 2127020 * 2
def baseEnd_2127020 : Nat := 1092183621726373258168019

theorem tailTrace_2127020 : CollatzResearch.WordTrace tailWord_2127020 prefixEnd_2127020 1092183621726373258168019 := by
  unfold tailWord_2127020
  simp only [CollatzResearch.WordTrace]
  refine ⟨38789396377088640470009257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51719195169451520626679009 38789396377088640470009257)
  ·
    refine ⟨29092047282816480352506943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38789396377088640470009257 29092047282816480352506943)
    ·
      refine ⟨43638070924224720528760415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29092047282816480352506943 43638070924224720528760415)
      ·
        refine ⟨65457106386337080793140623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43638070924224720528760415 65457106386337080793140623)
        ·
          refine ⟨98185659579505621189710935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65457106386337080793140623 98185659579505621189710935)
          ·
            refine ⟨147278489369258431784566403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98185659579505621189710935 147278489369258431784566403)
            ·
              refine ⟨220917734053887647676849605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147278489369258431784566403 220917734053887647676849605)
              ·
                refine ⟨41422075135103933939409301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 220917734053887647676849605 41422075135103933939409301)
                ·
                  refine ⟨1941659771957996903409811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41422075135103933939409301 1941659771957996903409811)
                  ·
                    refine ⟨2912489657936995355114717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1941659771957996903409811 2912489657936995355114717)
                    ·
                      refine ⟨1092183621726373258168019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2912489657936995355114717 1092183621726373258168019)
                      ·
                        rfl

theorem cell23_2127020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_2127020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127020 prefixEnd_2127020 := by exact prefixLift 2127020
  have htrace : WordTrace (prefixWord ++ tailWord_2127020) baseStart_2127020 baseEnd_2127020 := by
    simpa [prefixWord, tailWord_2127020, baseEnd_2127020] using wordTrace_append hprefix tailTrace_2127020
  have hstable : (prefixWord ++ tailWord_2127020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127020).length < 2 ^ (prefixWord ++ tailWord_2127020).sum := by decide
  have hdescent : baseEnd_2127020 < baseStart_2127020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127021 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_2127021 : Nat := 118140960795 + 2127021 * 2 ^ 59
def prefixEnd_2127021 : Nat := 4983230072969 + 3 ^ 40 * 2127021 * 2
def baseEnd_2127021 : Nat := 1092184135207027754255515

theorem tailTrace_2127021 : CollatzResearch.WordTrace tailWord_2127021 prefixEnd_2127021 1092184135207027754255515 := by
  unfold tailWord_2127021
  simp only [CollatzResearch.WordTrace]
  refine ⟨77578829227173658110804917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51719219484782438740536611 77578829227173658110804917)
  ·
    refine ⟨7273015240047530447887961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77578829227173658110804917 7273015240047530447887961)
    ·
      refine ⟨5454761430035647835915971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7273015240047530447887961 5454761430035647835915971)
      ·
        refine ⟨8182142145053471753873957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5454761430035647835915971 8182142145053471753873957)
        ·
          refine ⟨1534151652197525953851367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8182142145053471753873957 1534151652197525953851367)
          ·
            refine ⟨2301227478296288930777051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534151652197525953851367 2301227478296288930777051)
            ·
              refine ⟨3451841217444433396165577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301227478296288930777051 3451841217444433396165577)
              ·
                refine ⟨2588880913083325047124183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3451841217444433396165577 2588880913083325047124183)
                ·
                  refine ⟨3883321369624987570686275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588880913083325047124183 3883321369624987570686275)
                  ·
                    refine ⟨5824982054437481356029413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3883321369624987570686275 5824982054437481356029413)
                    ·
                      refine ⟨1092184135207027754255515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5824982054437481356029413 1092184135207027754255515)
                      ·
                        rfl

theorem cell23_2127021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_2127021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127021 prefixEnd_2127021 := by exact prefixLift 2127021
  have htrace : WordTrace (prefixWord ++ tailWord_2127021) baseStart_2127021 baseEnd_2127021 := by
    simpa [prefixWord, tailWord_2127021, baseEnd_2127021] using wordTrace_append hprefix tailTrace_2127021
  have hstable : (prefixWord ++ tailWord_2127021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127021).length < 2 ^ (prefixWord ++ tailWord_2127021).sum := by decide
  have hdescent : baseEnd_2127021 < baseStart_2127021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127041 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2127041 : Nat := 118140960795 + 2127041 * 2 ^ 59
def prefixEnd_2127041 : Nat := 4983230072969 + 3 ^ 40 * 2127041 * 2
def baseEnd_2127041 : Nat := 1092194404820117676005423

theorem tailTrace_2127041 : CollatzResearch.WordTrace tailWord_2127041 prefixEnd_2127041 1092194404820117676005423 := by
  unfold tailWord_2127041
  simp only [CollatzResearch.WordTrace]
  refine ⟨77579558687101201526532977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51719705791400801017688651 77579558687101201526532977)
  ·
    refine ⟨58184669015325901144899733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77579558687101201526532977 58184669015325901144899733)
    ·
      refine ⟨2727406360093401616167175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58184669015325901144899733 2727406360093401616167175)
      ·
        refine ⟨4091109540140102424250763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2727406360093401616167175 4091109540140102424250763)
        ·
          refine ⟨6136664310210153636376145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4091109540140102424250763 6136664310210153636376145)
          ·
            refine ⟨4602498232657615227282109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6136664310210153636376145 4602498232657615227282109)
            ·
              refine ⟨1725936837246605710230791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4602498232657615227282109 1725936837246605710230791)
              ·
                refine ⟨2588905255869908565346187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1725936837246605710230791 2588905255869908565346187)
                ·
                  refine ⟨3883357883804862848019281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588905255869908565346187 3883357883804862848019281)
                  ·
                    refine ⟨2912518412853647136014461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3883357883804862848019281 2912518412853647136014461)
                    ·
                      refine ⟨1092194404820117676005423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2912518412853647136014461 1092194404820117676005423)
                      ·
                        rfl

theorem cell23_2127041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2127041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127041 prefixEnd_2127041 := by exact prefixLift 2127041
  have htrace : WordTrace (prefixWord ++ tailWord_2127041) baseStart_2127041 baseEnd_2127041 := by
    simpa [prefixWord, tailWord_2127041, baseEnd_2127041] using wordTrace_append hprefix tailTrace_2127041
  have hstable : (prefixWord ++ tailWord_2127041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127041).length < 2 ^ (prefixWord ++ tailWord_2127041).sum := by decide
  have hdescent : baseEnd_2127041 < baseStart_2127041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127047 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 1, 3, 2]
def baseStart_2127047 : Nat := 118140960795 + 2127047 * 2 ^ 59
def prefixEnd_2127047 : Nat := 4983230072969 + 3 ^ 40 * 2127047 * 2
def baseEnd_2127047 : Nat := 1092197485704044652530395

theorem tailTrace_2127047 : CollatzResearch.WordTrace tailWord_2127047 prefixEnd_2127047 1092197485704044652530395 := by
  unfold tailWord_2127047
  simp only [CollatzResearch.WordTrace]
  refine ⟨77579777525079464551251395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51719851683386309700834263 77579777525079464551251395)
  ·
    refine ⟨116369666287619196826877093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77579777525079464551251395 116369666287619196826877093)
    ·
      refine ⟨21819312428928599405039455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116369666287619196826877093 21819312428928599405039455)
      ·
        refine ⟨32728968643392899107559183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21819312428928599405039455 32728968643392899107559183)
        ·
          refine ⟨49093452965089348661338775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32728968643392899107559183 49093452965089348661338775)
          ·
            refine ⟨73640179447634022992008163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49093452965089348661338775 73640179447634022992008163)
            ·
              refine ⟨110460269171451034488012245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73640179447634022992008163 110460269171451034488012245)
              ·
                refine ⟨2588912558705883620812787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 110460269171451034488012245 2588912558705883620812787)
                ·
                  refine ⟨3883368838058825431219181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588912558705883620812787 3883368838058825431219181)
                  ·
                    refine ⟨1456263314272059536707193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3883368838058825431219181 1456263314272059536707193)
                    ·
                      refine ⟨1092197485704044652530395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456263314272059536707193 1092197485704044652530395)
                      ·
                        rfl

theorem cell23_2127047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_2127047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127047 prefixEnd_2127047 := by exact prefixLift 2127047
  have htrace : WordTrace (prefixWord ++ tailWord_2127047) baseStart_2127047 baseEnd_2127047 := by
    simpa [prefixWord, tailWord_2127047, baseEnd_2127047] using wordTrace_append hprefix tailTrace_2127047
  have hstable : (prefixWord ++ tailWord_2127047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127047).length < 2 ^ (prefixWord ++ tailWord_2127047).sum := by decide
  have hdescent : baseEnd_2127047 < baseStart_2127047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127063 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_2127063 : Nat := 118140960795 + 2127063 * 2 ^ 59
def prefixEnd_2127063 : Nat := 4983230072969 + 3 ^ 40 * 2127063 * 2
def baseEnd_2127063 : Nat := 1092205701394516589930321

theorem tailTrace_2127063 : CollatzResearch.WordTrace tailWord_2127063 prefixEnd_2127063 1092205701394516589930321 := by
  unfold tailWord_2127063
  simp only [CollatzResearch.WordTrace]
  refine ⟨77580361093021499283833843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51720240728680999522555895 77580361093021499283833843)
  ·
    refine ⟨116370541639532248925750765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77580361093021499283833843 116370541639532248925750765)
    ·
      refine ⟨43638953114824593347156537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116370541639532248925750765 43638953114824593347156537)
      ·
        refine ⟨32729214836118445010367403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43638953114824593347156537 32729214836118445010367403)
        ·
          refine ⟨49093822254177667515551105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32729214836118445010367403 49093822254177667515551105)
          ·
            refine ⟨36820366690633250636663329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49093822254177667515551105 36820366690633250636663329)
            ·
              refine ⟨27615275017974937977497497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36820366690633250636663329 27615275017974937977497497)
              ·
                refine ⟨20711456263481203483123123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27615275017974937977497497 20711456263481203483123123)
                ·
                  refine ⟨31067184395221805224684685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20711456263481203483123123 31067184395221805224684685)
                  ·
                    refine ⟨11650194148208176959256757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31067184395221805224684685 11650194148208176959256757)
                    ·
                      refine ⟨1092205701394516589930321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11650194148208176959256757 1092205701394516589930321)
                      ·
                        rfl

theorem cell23_2127063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_2127063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127063 prefixEnd_2127063 := by exact prefixLift 2127063
  have htrace : WordTrace (prefixWord ++ tailWord_2127063) baseStart_2127063 baseEnd_2127063 := by
    simpa [prefixWord, tailWord_2127063, baseEnd_2127063] using wordTrace_append hprefix tailTrace_2127063
  have hstable : (prefixWord ++ tailWord_2127063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127063).length < 2 ^ (prefixWord ++ tailWord_2127063).sum := by decide
  have hdescent : baseEnd_2127063 < baseStart_2127063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127080 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_2127080 : Nat := 118140960795 + 2127080 * 2 ^ 59
def prefixEnd_2127080 : Nat := 4983230072969 + 3 ^ 40 * 2127080 * 2
def baseEnd_2127080 : Nat := 1092214430565643023417743

theorem tailTrace_2127080 : CollatzResearch.WordTrace tailWord_2127080 prefixEnd_2127080 1092214430565643023417743 := by
  unfold tailWord_2127080
  simp only [CollatzResearch.WordTrace]
  refine ⟨38790490566979955593601347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51720654089306607458135129 38790490566979955593601347)
  ·
    refine ⟨58185735850469933390402021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38790490566979955593601347 58185735850469933390402021)
    ·
      refine ⟨10909825471963112510700379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58185735850469933390402021 10909825471963112510700379)
      ·
        refine ⟨16364738207944668766050569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10909825471963112510700379 16364738207944668766050569)
        ·
          refine ⟨12273553655958501574537927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16364738207944668766050569 12273553655958501574537927)
          ·
            refine ⟨18410330483937752361806891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12273553655958501574537927 18410330483937752361806891)
            ·
              refine ⟨27615495725906628542710337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18410330483937752361806891 27615495725906628542710337)
              ·
                refine ⟨20711621794429971407032753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27615495725906628542710337 20711621794429971407032753)
                ·
                  refine ⟨15533716345822478555274565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20711621794429971407032753 15533716345822478555274565)
                  ·
                    refine ⟨2912571814841714729113981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15533716345822478555274565 2912571814841714729113981)
                    ·
                      refine ⟨1092214430565643023417743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2912571814841714729113981 1092214430565643023417743)
                      ·
                        rfl

theorem cell23_2127080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_2127080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127080 prefixEnd_2127080 := by exact prefixLift 2127080
  have htrace : WordTrace (prefixWord ++ tailWord_2127080) baseStart_2127080 baseEnd_2127080 := by
    simpa [prefixWord, tailWord_2127080, baseEnd_2127080] using wordTrace_append hprefix tailTrace_2127080
  have hstable : (prefixWord ++ tailWord_2127080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127080).length < 2 ^ (prefixWord ++ tailWord_2127080).sum := by decide
  have hdescent : baseEnd_2127080 < baseStart_2127080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127083 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 9]
def baseStart_2127083 : Nat := 118140960795 + 2127083 * 2 ^ 59
def prefixEnd_2127083 : Nat := 4983230072969 + 3 ^ 40 * 2127083 * 2
def baseEnd_2127083 : Nat := 121357330111956279075581

theorem tailTrace_2127083 : CollatzResearch.WordTrace tailWord_2127083 prefixEnd_2127083 121357330111956279075581 := by
  unfold tailWord_2127083
  simp only [CollatzResearch.WordTrace]
  refine ⟨77581090552949042699561903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51720727035299361799707935 77581090552949042699561903)
  ·
    refine ⟨116371635829423564049342855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77581090552949042699561903 116371635829423564049342855)
    ·
      refine ⟨174557453744135346074014283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116371635829423564049342855 174557453744135346074014283)
      ·
        refine ⟨261836180616203019111021425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174557453744135346074014283 261836180616203019111021425)
        ·
          refine ⟨196377135462152264333266069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261836180616203019111021425 196377135462152264333266069)
          ·
            refine ⟨9205178224788387390621847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 196377135462152264333266069 9205178224788387390621847)
            ·
              refine ⟨13807767337182581085932771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9205178224788387390621847 13807767337182581085932771)
              ·
                refine ⟨20711651005773871628899157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13807767337182581085932771 20711651005773871628899157)
                ·
                  refine ⟨121357330111956279075581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20711651005773871628899157 121357330111956279075581)
                  ·
                    rfl

theorem cell23_2127083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 9].length) (baseStart_2127083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127083 prefixEnd_2127083 := by exact prefixLift 2127083
  have htrace : WordTrace (prefixWord ++ tailWord_2127083) baseStart_2127083 baseEnd_2127083 := by
    simpa [prefixWord, tailWord_2127083, baseEnd_2127083] using wordTrace_append hprefix tailTrace_2127083
  have hstable : (prefixWord ++ tailWord_2127083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127083).length < 2 ^ (prefixWord ++ tailWord_2127083).sum := by decide
  have hdescent : baseEnd_2127083 < baseStart_2127083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127092 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2127092 : Nat := 118140960795 + 2127092 * 2 ^ 59
def prefixEnd_2127092 : Nat := 4983230072969 + 3 ^ 40 * 2127092 * 2
def baseEnd_2127092 : Nat := 1092220592333496976467689

theorem tailTrace_2127092 : CollatzResearch.WordTrace tailWord_2127092 prefixEnd_2127092 1092220592333496976467689 := by
  unfold tailWord_2127092
  simp only [CollatzResearch.WordTrace]
  refine ⟨38790709404958218618319765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51720945873277624824426353 38790709404958218618319765)
  ·
    refine ⟨1818314503357416497733739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38790709404958218618319765 1818314503357416497733739)
    ·
      refine ⟨2727471755036124746600609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818314503357416497733739 2727471755036124746600609)
      ·
        refine ⟨2045603816277093559950457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2727471755036124746600609 2045603816277093559950457)
        ·
          refine ⟨1534202862207820169962843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2045603816277093559950457 1534202862207820169962843)
          ·
            refine ⟨2301304293311730254944265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534202862207820169962843 2301304293311730254944265)
            ·
              refine ⟨1725978219983797691208199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2301304293311730254944265 1725978219983797691208199)
              ·
                refine ⟨2588967329975696536812299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1725978219983797691208199 2588967329975696536812299)
                ·
                  refine ⟨3883450994963544805218449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2588967329975696536812299 3883450994963544805218449)
                  ·
                    refine ⟨2912588246222658603913837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3883450994963544805218449 2912588246222658603913837)
                    ·
                      refine ⟨1092220592333496976467689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2912588246222658603913837 1092220592333496976467689)
                      ·
                        rfl

theorem cell23_2127092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2127092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127092 prefixEnd_2127092 := by exact prefixLift 2127092
  have htrace : WordTrace (prefixWord ++ tailWord_2127092) baseStart_2127092 baseEnd_2127092 := by
    simpa [prefixWord, tailWord_2127092, baseEnd_2127092] using wordTrace_append hprefix tailTrace_2127092
  have hstable : (prefixWord ++ tailWord_2127092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127092).length < 2 ^ (prefixWord ++ tailWord_2127092).sum := by decide
  have hdescent : baseEnd_2127092 < baseStart_2127092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127094 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_2127094 : Nat := 118140960795 + 2127094 * 2 ^ 59
def prefixEnd_2127094 : Nat := 4983230072969 + 3 ^ 40 * 2127094 * 2
def baseEnd_2127094 : Nat := 1092221619294805968642679

theorem tailTrace_2127094 : CollatzResearch.WordTrace tailWord_2127094 prefixEnd_2127094 1092221619294805968642679 := by
  unfold tailWord_2127094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4848843234744324473638271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51720994503939461052141557 4848843234744324473638271)
  ·
    refine ⟨7273264852116486710457407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4848843234744324473638271 7273264852116486710457407)
    ·
      refine ⟨10909897278174730065686111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7273264852116486710457407 10909897278174730065686111)
      ·
        refine ⟨16364845917262095098529167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10909897278174730065686111 16364845917262095098529167)
        ·
          refine ⟨24547268875893142647793751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16364845917262095098529167 24547268875893142647793751)
          ·
            refine ⟨36820903313839713971690627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24547268875893142647793751 36820903313839713971690627)
            ·
              refine ⟨55231354970759570957535941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36820903313839713971690627 55231354970759570957535941)
              ·
                refine ⟨10355879057017419554537989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55231354970759570957535941 10355879057017419554537989)
                ·
                  refine ⟨1941727323190766166475873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10355879057017419554537989 1941727323190766166475873)
                  ·
                    refine ⟨1456295492393074624856905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1941727323190766166475873 1456295492393074624856905)
                    ·
                      refine ⟨1092221619294805968642679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456295492393074624856905 1092221619294805968642679)
                      ·
                        rfl

theorem cell23_2127094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_2127094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127094 prefixEnd_2127094 := by exact prefixLift 2127094
  have htrace : WordTrace (prefixWord ++ tailWord_2127094) baseStart_2127094 baseEnd_2127094 := by
    simpa [prefixWord, tailWord_2127094, baseEnd_2127094] using wordTrace_append hprefix tailTrace_2127094
  have hstable : (prefixWord ++ tailWord_2127094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127094).length < 2 ^ (prefixWord ++ tailWord_2127094).sum := by decide
  have hdescent : baseEnd_2127094 < baseStart_2127094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127130 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_2127130 : Nat := 118140960795 + 2127130 * 2 ^ 59
def prefixEnd_2127130 : Nat := 4983230072969 + 3 ^ 40 * 2127130 * 2
def baseEnd_2127130 : Nat := 364080034866122609264171

theorem tailTrace_2127130 : CollatzResearch.WordTrace tailWord_2127130 prefixEnd_2127130 364080034866122609264171 := by
  unfold tailWord_2127130
  simp only [CollatzResearch.WordTrace]
  refine ⟨19395701195944692431630711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51721869855852513151015229 19395701195944692431630711)
  ·
    refine ⟨29093551793917038647446067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19395701195944692431630711 29093551793917038647446067)
    ·
      refine ⟨43640327690875557971169101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29093551793917038647446067 43640327690875557971169101)
      ·
        refine ⟨16365122884078334239188413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43640327690875557971169101 16365122884078334239188413)
        ·
          refine ⟨6136921081529375339695655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16365122884078334239188413 6136921081529375339695655)
          ·
            refine ⟨9205381622294063009543483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6136921081529375339695655 9205381622294063009543483)
            ·
              refine ⟨13808072433441094514315225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9205381622294063009543483 13808072433441094514315225)
              ·
                refine ⟨10356054325080820885736419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13808072433441094514315225 10356054325080820885736419)
                ·
                  refine ⟨15534081487621231328604629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10356054325080820885736419 15534081487621231328604629)
                  ·
                    refine ⟨364080034866122609264171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15534081487621231328604629 364080034866122609264171)
                    ·
                      rfl

theorem cell23_2127130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_2127130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127130 prefixEnd_2127130 := by exact prefixLift 2127130
  have htrace : WordTrace (prefixWord ++ tailWord_2127130) baseStart_2127130 baseEnd_2127130 := by
    simpa [prefixWord, tailWord_2127130, baseEnd_2127130] using wordTrace_append hprefix tailTrace_2127130
  have hstable : (prefixWord ++ tailWord_2127130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127130).length < 2 ^ (prefixWord ++ tailWord_2127130).sum := by decide
  have hdescent : baseEnd_2127130 < baseStart_2127130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127167 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 4]
def baseStart_2127167 : Nat := 118140960795 + 2127167 * 2 ^ 59
def prefixEnd_2127167 : Nat := 4983230072969 + 3 ^ 40 * 2127167 * 2
def baseEnd_2127167 : Nat := 1092259103382584183029843

theorem tailTrace_2127167 : CollatzResearch.WordTrace tailWord_2127167 prefixEnd_2127167 1092259103382584183029843 := by
  unfold tailWord_2127167
  simp only [CollatzResearch.WordTrace]
  refine ⟨77584154284644725045619755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51722769523096483363746503 77584154284644725045619755)
  ·
    refine ⟨116376231426967087568429633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77584154284644725045619755 116376231426967087568429633)
    ·
      refine ⟨87282173570225315676322225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116376231426967087568429633 87282173570225315676322225)
      ·
        refine ⟨65461630177668986757241669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87282173570225315676322225 65461630177668986757241669)
        ·
          refine ⟨12274055658312935016982813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65461630177668986757241669 12274055658312935016982813)
          ·
            refine ⟨4602770871867350631368555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12274055658312935016982813 4602770871867350631368555)
            ·
              refine ⟨6904156307801025947052833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4602770871867350631368555 6904156307801025947052833)
              ·
                refine ⟨5178117230850769460289625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6904156307801025947052833 5178117230850769460289625)
                ·
                  refine ⟨3883587923138077095217219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5178117230850769460289625 3883587923138077095217219)
                  ·
                    refine ⟨5825381884707115642825829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3883587923138077095217219 5825381884707115642825829)
                    ·
                      refine ⟨1092259103382584183029843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5825381884707115642825829 1092259103382584183029843)
                      ·
                        rfl

theorem cell23_2127167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_2127167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127167 prefixEnd_2127167 := by exact prefixLift 2127167
  have htrace : WordTrace (prefixWord ++ tailWord_2127167) baseStart_2127167 baseEnd_2127167 := by
    simpa [prefixWord, tailWord_2127167, baseEnd_2127167] using wordTrace_append hprefix tailTrace_2127167
  have hstable : (prefixWord ++ tailWord_2127167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127167).length < 2 ^ (prefixWord ++ tailWord_2127167).sum := by decide
  have hdescent : baseEnd_2127167 < baseStart_2127167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127177 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 3, 4]
def baseStart_2127177 : Nat := 118140960795 + 2127177 * 2 ^ 59
def prefixEnd_2127177 : Nat := 4983230072969 + 3 ^ 40 * 2127177 * 2
def baseEnd_2127177 : Nat := 364088079396376381301599

theorem tailTrace_2127177 : CollatzResearch.WordTrace tailWord_2127177 prefixEnd_2127177 364088079396376381301599 := by
  unfold tailWord_2127177
  simp only [CollatzResearch.WordTrace]
  refine ⟨77584519014608496753483785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51723012676405664502322523 77584519014608496753483785)
  ·
    refine ⟨58188389260956372565112839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77584519014608496753483785 58188389260956372565112839)
    ·
      refine ⟨87282583891434558847669259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58188389260956372565112839 87282583891434558847669259)
      ·
        refine ⟨130923875837151838271503889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87282583891434558847669259 130923875837151838271503889)
        ·
          refine ⟨98192906877863878703627917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130923875837151838271503889 98192906877863878703627917)
          ·
            refine ⟨36822340079198954513860469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98192906877863878703627917 36822340079198954513860469)
            ·
              refine ⟨3452094382424901985674419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36822340079198954513860469 3452094382424901985674419)
              ·
                refine ⟨5178141573637352978511629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3452094382424901985674419 5178141573637352978511629)
                ·
                  refine ⟨1941803090114007366941861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5178141573637352978511629 1941803090114007366941861)
                  ·
                    refine ⟨364088079396376381301599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1941803090114007366941861 364088079396376381301599)
                    ·
                      rfl

theorem cell23_2127177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 4].length) (baseStart_2127177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127177 prefixEnd_2127177 := by exact prefixLift 2127177
  have htrace : WordTrace (prefixWord ++ tailWord_2127177) baseStart_2127177 baseEnd_2127177 := by
    simpa [prefixWord, tailWord_2127177, baseEnd_2127177] using wordTrace_append hprefix tailTrace_2127177
  have hstable : (prefixWord ++ tailWord_2127177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127177).length < 2 ^ (prefixWord ++ tailWord_2127177).sum := by decide
  have hdescent : baseEnd_2127177 < baseStart_2127177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127204 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_2127204 : Nat := 118140960795 + 2127204 * 2 ^ 59
def prefixEnd_2127204 : Nat := 4983230072969 + 3 ^ 40 * 2127204 * 2
def baseEnd_2127204 : Nat := 1092278102166800538267173

theorem tailTrace_2127204 : CollatzResearch.WordTrace tailWord_2127204 prefixEnd_2127204 1092278102166800538267173 := by
  unfold tailWord_2127204
  simp only [CollatzResearch.WordTrace]
  refine ⟨38792751892755340182358333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51723669190340453576477777 38792751892755340182358333)
  ·
    refine ⟨14547281959783252568384375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38792751892755340182358333 14547281959783252568384375)
    ·
      refine ⟨21820922939674878852576563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14547281959783252568384375 21820922939674878852576563)
      ·
        refine ⟨32731384409512318278864845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21820922939674878852576563 32731384409512318278864845)
        ·
          refine ⟨12274269153567119354574317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32731384409512318278864845 12274269153567119354574317)
          ·
            refine ⟨4602850932587669757965369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12274269153567119354574317 4602850932587669757965369)
            ·
              refine ⟨3452138199440752318474027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4602850932587669757965369 3452138199440752318474027)
              ·
                refine ⟨5178207299161128477711041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3452138199440752318474027 5178207299161128477711041)
                ·
                  refine ⟨3883655474370846358283281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5178207299161128477711041 3883655474370846358283281)
                  ·
                    refine ⟨2912741605778134768712461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3883655474370846358283281 2912741605778134768712461)
                    ·
                      refine ⟨1092278102166800538267173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2912741605778134768712461 1092278102166800538267173)
                      ·
                        rfl

theorem cell23_2127204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_2127204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127204 prefixEnd_2127204 := by exact prefixLift 2127204
  have htrace : WordTrace (prefixWord ++ tailWord_2127204) baseStart_2127204 baseEnd_2127204 := by
    simpa [prefixWord, tailWord_2127204, baseEnd_2127204] using wordTrace_append hprefix tailTrace_2127204
  have hstable : (prefixWord ++ tailWord_2127204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127204).length < 2 ^ (prefixWord ++ tailWord_2127204).sum := by decide
  have hdescent : baseEnd_2127204 < baseStart_2127204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127257 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 4]
def baseStart_2127257 : Nat := 118140960795 + 2127257 * 2 ^ 59
def prefixEnd_2127257 : Nat := 4983230072969 + 3 ^ 40 * 2127257 * 2
def baseEnd_2127257 : Nat := 1092305316641488830904429

theorem tailTrace_2127257 : CollatzResearch.WordTrace tailWord_2127257 prefixEnd_2127257 1092305316641488830904429 := by
  unfold tailWord_2127257
  simp only [CollatzResearch.WordTrace]
  refine ⟨77587436854318670416396025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51724957902879113610930683 77587436854318670416396025)
  ·
    refine ⟨58190577640739002812297019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77587436854318670416396025 58190577640739002812297019)
    ·
      refine ⟨87285866461108504218445529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58190577640739002812297019 87285866461108504218445529)
      ·
        refine ⟨65464399845831378163834147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87285866461108504218445529 65464399845831378163834147)
        ·
          refine ⟨98196599768747067245751221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65464399845831378163834147 98196599768747067245751221)
          ·
            refine ⟨9205931228320037554289177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98196599768747067245751221 9205931228320037554289177)
            ·
              refine ⟨6904448421240028165716883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9205931228320037554289177 6904448421240028165716883)
              ·
                refine ⟨10356672631860042248575325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6904448421240028165716883 10356672631860042248575325)
                ·
                  refine ⟨3883752236947515843215747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10356672631860042248575325 3883752236947515843215747)
                  ·
                    refine ⟨5825628355421273764823621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3883752236947515843215747 5825628355421273764823621)
                    ·
                      refine ⟨1092305316641488830904429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5825628355421273764823621 1092305316641488830904429)
                      ·
                        rfl

theorem cell23_2127257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_2127257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127257 prefixEnd_2127257 := by exact prefixLift 2127257
  have htrace : WordTrace (prefixWord ++ tailWord_2127257) baseStart_2127257 baseEnd_2127257 := by
    simpa [prefixWord, tailWord_2127257, baseEnd_2127257] using wordTrace_append hprefix tailTrace_2127257
  have hstable : (prefixWord ++ tailWord_2127257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127257).length < 2 ^ (prefixWord ++ tailWord_2127257).sum := by decide
  have hdescent : baseEnd_2127257 < baseStart_2127257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127261 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_2127261 : Nat := 118140960795 + 2127261 * 2 ^ 59
def prefixEnd_2127261 : Nat := 4983230072969 + 3 ^ 40 * 2127261 * 2
def baseEnd_2127261 : Nat := 1092307370564106815254411

theorem tailTrace_2127261 : CollatzResearch.WordTrace tailWord_2127261 prefixEnd_2127261 1092307370564106815254411 := by
  unfold tailWord_2127261
  simp only [CollatzResearch.WordTrace]
  refine ⟨77587582746304179099541637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51725055164202786066361091 77587582746304179099541637)
  ·
    refine ⟨14547671764932033581164057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77587582746304179099541637 14547671764932033581164057)
    ·
      refine ⟨10910753823699025185873043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14547671764932033581164057 10910753823699025185873043)
      ·
        refine ⟨16366130735548537778809565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10910753823699025185873043 16366130735548537778809565)
        ·
          refine ⟨6137299025830701667053587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16366130735548537778809565 6137299025830701667053587)
          ·
            refine ⟨9205948538746052500580381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6137299025830701667053587 9205948538746052500580381)
            ·
              refine ⟨3452230702029769687717643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9205948538746052500580381 3452230702029769687717643)
              ·
                refine ⟨5178346053044654531576465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3452230702029769687717643 5178346053044654531576465)
                ·
                  refine ⟨3883759539783490898682349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5178346053044654531576465 3883759539783490898682349)
                  ·
                    refine ⟨1456409827418809087005881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3883759539783490898682349 1456409827418809087005881)
                    ·
                      refine ⟨1092307370564106815254411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456409827418809087005881 1092307370564106815254411)
                      ·
                        rfl

theorem cell23_2127261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_2127261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127261 prefixEnd_2127261 := by exact prefixLift 2127261
  have htrace : WordTrace (prefixWord ++ tailWord_2127261) baseStart_2127261 baseEnd_2127261 := by
    simpa [prefixWord, tailWord_2127261, baseEnd_2127261] using wordTrace_append hprefix tailTrace_2127261
  have hstable : (prefixWord ++ tailWord_2127261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127261).length < 2 ^ (prefixWord ++ tailWord_2127261).sum := by decide
  have hdescent : baseEnd_2127261 < baseStart_2127261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127267 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 4, 4]
def baseStart_2127267 : Nat := 118140960795 + 2127267 * 2 ^ 59
def prefixEnd_2127267 : Nat := 4983230072969 + 3 ^ 40 * 2127267 * 2
def baseEnd_2127267 : Nat := 364103483816011263926461

theorem tailTrace_2127267 : CollatzResearch.WordTrace tailWord_2127267 prefixEnd_2127267 364103483816011263926461 := by
  unfold tailWord_2127267
  simp only [CollatzResearch.WordTrace]
  refine ⟨77587801584282442124260055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51725201056188294749506703 77587801584282442124260055)
  ·
    refine ⟨116381702376423663186390083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77587801584282442124260055 116381702376423663186390083)
    ·
      refine ⟨174572553564635494779585125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116381702376423663186390083 174572553564635494779585125)
      ·
        refine ⟨32732353793369155271172211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174572553564635494779585125 32732353793369155271172211)
        ·
          refine ⟨49098530690053732906758317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32732353793369155271172211 49098530690053732906758317)
          ·
            refine ⟨18411949008770149840034369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49098530690053732906758317 18411949008770149840034369)
            ·
              refine ⟨13808961756577612380025777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18411949008770149840034369 13808961756577612380025777)
              ·
                refine ⟨10356721317433209285019333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13808961756577612380025777 10356721317433209285019333)
                ·
                  refine ⟨1941885247018726740941125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10356721317433209285019333 1941885247018726740941125)
                  ·
                    refine ⟨364103483816011263926461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1941885247018726740941125 364103483816011263926461)
                    ·
                      rfl

theorem cell23_2127267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 4].length) (baseStart_2127267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127267 prefixEnd_2127267 := by exact prefixLift 2127267
  have htrace : WordTrace (prefixWord ++ tailWord_2127267) baseStart_2127267 baseEnd_2127267 := by
    simpa [prefixWord, tailWord_2127267, baseEnd_2127267] using wordTrace_append hprefix tailTrace_2127267
  have hstable : (prefixWord ++ tailWord_2127267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127267).length < 2 ^ (prefixWord ++ tailWord_2127267).sum := by decide
  have hdescent : baseEnd_2127267 < baseStart_2127267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127290 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_2127290 : Nat := 118140960795 + 2127290 * 2 ^ 59
def prefixEnd_2127290 : Nat := 4983230072969 + 3 ^ 40 * 2127290 * 2
def baseEnd_2127290 : Nat := 1092322261503087201791777

theorem tailTrace_2127290 : CollatzResearch.WordTrace tailWord_2127290 prefixEnd_2127290 1092322261503087201791777 := by
  unfold tailWord_2127290
  simp only [CollatzResearch.WordTrace]
  refine ⟨19397160115799779263086831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51725760308799411368231549 19397160115799779263086831)
  ·
    refine ⟨29095740173699668894630247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19397160115799779263086831 29095740173699668894630247)
    ·
      refine ⟨43643610260549503341945371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29095740173699668894630247 43643610260549503341945371)
      ·
        refine ⟨65465415390824255012918057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43643610260549503341945371 65465415390824255012918057)
        ·
          refine ⟨49099061543118191259688543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65465415390824255012918057 49099061543118191259688543)
          ·
            refine ⟨73648592314677286889532815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49099061543118191259688543 73648592314677286889532815)
            ·
              refine ⟨110472888472015930334299223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73648592314677286889532815 110472888472015930334299223)
              ·
                refine ⟨165709332708023895501448835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110472888472015930334299223 165709332708023895501448835)
                ·
                  refine ⟨248563999062035843252173253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165709332708023895501448835 248563999062035843252173253)
                  ·
                    refine ⟨46605749824131720609782485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248563999062035843252173253 46605749824131720609782485)
                    ·
                      refine ⟨1092322261503087201791777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 46605749824131720609782485 1092322261503087201791777)
                      ·
                        rfl

theorem cell23_2127290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_2127290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127290 prefixEnd_2127290 := by exact prefixLift 2127290
  have htrace : WordTrace (prefixWord ++ tailWord_2127290) baseStart_2127290 baseEnd_2127290 := by
    simpa [prefixWord, tailWord_2127290, baseEnd_2127290] using wordTrace_append hprefix tailTrace_2127290
  have hstable : (prefixWord ++ tailWord_2127290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127290).length < 2 ^ (prefixWord ++ tailWord_2127290).sum := by decide
  have hdescent : baseEnd_2127290 < baseStart_2127290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127325 : List Nat := [1, 4, 3, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_2127325 : Nat := 118140960795 + 2127325 * 2 ^ 59
def prefixEnd_2127325 : Nat := 4983230072969 + 3 ^ 40 * 2127325 * 2
def baseEnd_2127325 : Nat := 1092340233325994564854117

theorem tailTrace_2127325 : CollatzResearch.WordTrace tailWord_2127325 prefixEnd_2127325 1092340233325994564854117 := by
  unfold tailWord_2127325
  simp only [CollatzResearch.WordTrace]
  refine ⟨77589917018072318029871429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51726611345381545353247619 77589917018072318029871429)
  ·
    refine ⟨14548109440888559630600893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77589917018072318029871429 14548109440888559630600893)
    ·
      refine ⟨5455541040333209861475335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14548109440888559630600893 5455541040333209861475335)
      ·
        refine ⟨8183311560499814792213003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5455541040333209861475335 8183311560499814792213003)
        ·
          refine ⟨12274967340749722188319505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8183311560499814792213003 12274967340749722188319505)
          ·
            refine ⟨9206225505562291641239629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12274967340749722188319505 9206225505562291641239629)
            ·
              refine ⟨3452334564585859365464861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9206225505562291641239629 3452334564585859365464861)
              ·
                refine ⟨1294625461719697262049323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3452334564585859365464861 1294625461719697262049323)
                ·
                  refine ⟨1941938192579545893073985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294625461719697262049323 1941938192579545893073985)
                  ·
                    refine ⟨1456453644434659419805489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1941938192579545893073985 1456453644434659419805489)
                    ·
                      refine ⟨1092340233325994564854117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456453644434659419805489 1092340233325994564854117)
                      ·
                        rfl

theorem cell23_2127325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_2127325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127325 prefixEnd_2127325 := by exact prefixLift 2127325
  have htrace : WordTrace (prefixWord ++ tailWord_2127325) baseStart_2127325 baseEnd_2127325 := by
    simpa [prefixWord, tailWord_2127325, baseEnd_2127325] using wordTrace_append hprefix tailTrace_2127325
  have hstable : (prefixWord ++ tailWord_2127325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127325).length < 2 ^ (prefixWord ++ tailWord_2127325).sum := by decide
  have hdescent : baseEnd_2127325 < baseStart_2127325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127381 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 1, 4, 2]
def baseStart_2127381 : Nat := 118140960795 + 2127381 * 2 ^ 59
def prefixEnd_2127381 : Nat := 4983230072969 + 3 ^ 40 * 2127381 * 2
def baseEnd_2127381 : Nat := 1092368988242646345753859

theorem tailTrace_2127381 : CollatzResearch.WordTrace tailWord_2127381 prefixEnd_2127381 1092368988242646345753859 := by
  unfold tailWord_2127381
  simp only [CollatzResearch.WordTrace]
  refine ⟨77591959505869439593909997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51727973003912959729273331 77591959505869439593909997)
  ·
    refine ⟨29096984814701039847716249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77591959505869439593909997 29096984814701039847716249)
    ·
      refine ⟨21822738611025779885787187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29096984814701039847716249 21822738611025779885787187)
      ·
        refine ⟨32734107916538669828680781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21822738611025779885787187 32734107916538669828680781)
        ·
          refine ⟨12275290468702001185755293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32734107916538669828680781 12275290468702001185755293)
          ·
            refine ⟨4603233925763250444658235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12275290468702001185755293 4603233925763250444658235)
            ·
              refine ⟨6904850888644875666987353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4603233925763250444658235 6904850888644875666987353)
              ·
                refine ⟨5178638166483656750240515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6904850888644875666987353 5178638166483656750240515)
                ·
                  refine ⟨7767957249725485125360773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5178638166483656750240515 7767957249725485125360773)
                  ·
                    refine ⟨1456491984323528461005145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7767957249725485125360773 1456491984323528461005145)
                    ·
                      refine ⟨1092368988242646345753859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456491984323528461005145 1092368988242646345753859)
                      ·
                        rfl

theorem cell23_2127381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_2127381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127381 prefixEnd_2127381 := by exact prefixLift 2127381
  have htrace : WordTrace (prefixWord ++ tailWord_2127381) baseStart_2127381 baseEnd_2127381 := by
    simpa [prefixWord, tailWord_2127381, baseEnd_2127381] using wordTrace_append hprefix tailTrace_2127381
  have hstable : (prefixWord ++ tailWord_2127381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127381).length < 2 ^ (prefixWord ++ tailWord_2127381).sum := by decide
  have hdescent : baseEnd_2127381 < baseStart_2127381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127424 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 4, 5, 2]
def baseStart_2127424 : Nat := 118140960795 + 2127424 * 2 ^ 59
def prefixEnd_2127424 : Nat := 4983230072969 + 3 ^ 40 * 2127424 * 2
def baseEnd_2127424 : Nat := 1092391067910789677516161

theorem tailTrace_2127424 : CollatzResearch.WordTrace tailWord_2127424 prefixEnd_2127424 1092391067910789677516161 := by
  unfold tailWord_2127424
  simp only [CollatzResearch.WordTrace]
  refine ⟨38796763922356828968862663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51729018563142438625150217 38796763922356828968862663)
  ·
    refine ⟨58195145883535243453293995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38796763922356828968862663 58195145883535243453293995)
    ·
      refine ⟨87292718825302865179940993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58195145883535243453293995 87292718825302865179940993)
      ·
        refine ⟨65469539118977148884955745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87292718825302865179940993 65469539118977148884955745)
        ·
          refine ⟨49102154339232861663716809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65469539118977148884955745 49102154339232861663716809)
          ·
            refine ⟨36826615754424646247787607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49102154339232861663716809 36826615754424646247787607)
            ·
              refine ⟨55239923631636969371681411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36826615754424646247787607 55239923631636969371681411)
              ·
                refine ⟨82859885447455454057522117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55239923631636969371681411 82859885447455454057522117)
                ·
                  refine ⟨15536228521397897635785397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82859885447455454057522117 15536228521397897635785397)
                  ·
                    refine ⟨1456521423881052903354881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15536228521397897635785397 1456521423881052903354881)
                    ·
                      refine ⟨1092391067910789677516161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456521423881052903354881 1092391067910789677516161)
                      ·
                        rfl

theorem cell23_2127424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 5, 2].length) (baseStart_2127424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127424 prefixEnd_2127424 := by exact prefixLift 2127424
  have htrace : WordTrace (prefixWord ++ tailWord_2127424) baseStart_2127424 baseEnd_2127424 := by
    simpa [prefixWord, tailWord_2127424, baseEnd_2127424] using wordTrace_append hprefix tailTrace_2127424
  have hstable : (prefixWord ++ tailWord_2127424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127424).length < 2 ^ (prefixWord ++ tailWord_2127424).sum := by decide
  have hdescent : baseEnd_2127424 < baseStart_2127424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127548 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 2, 3, 2]
def baseStart_2127548 : Nat := 118140960795 + 2127548 * 2 ^ 59
def prefixEnd_2127548 : Nat := 4983230072969 + 3 ^ 40 * 2127548 * 2
def baseEnd_2127548 : Nat := 1092454739511947192365591

theorem tailTrace_2127548 : CollatzResearch.WordTrace tailWord_2127548 prefixEnd_2127548 1092454739511947192365591 := by
  unfold tailWord_2127548
  simp only [CollatzResearch.WordTrace]
  refine ⟨38799025248132213557619649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51732033664176284743492865 38799025248132213557619649)
  ·
    refine ⟨29099268936099160168214737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38799025248132213557619649 29099268936099160168214737)
    ·
      refine ⟨21824451702074370126161053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29099268936099160168214737 21824451702074370126161053)
      ·
        refine ⟨8184169388277888797310395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21824451702074370126161053 8184169388277888797310395)
        ·
          refine ⟨12276254082416833195965593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8184169388277888797310395 12276254082416833195965593)
          ·
            refine ⟨9207190561812624896974195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12276254082416833195965593 9207190561812624896974195)
            ·
              refine ⟨13810785842718937345461293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9207190561812624896974195 13810785842718937345461293)
              ·
                refine ⟨5179044691019601504547985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13810785842718937345461293 5179044691019601504547985)
                ·
                  refine ⟨3884283518264701128410989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5179044691019601504547985 3884283518264701128410989)
                  ·
                    refine ⟨1456606319349262923154121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3884283518264701128410989 1456606319349262923154121)
                    ·
                      refine ⟨1092454739511947192365591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456606319349262923154121 1092454739511947192365591)
                      ·
                        rfl

theorem cell23_2127548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_2127548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127548 prefixEnd_2127548 := by exact prefixLift 2127548
  have htrace : WordTrace (prefixWord ++ tailWord_2127548) baseStart_2127548 baseEnd_2127548 := by
    simpa [prefixWord, tailWord_2127548, baseEnd_2127548] using wordTrace_append hprefix tailTrace_2127548
  have hstable : (prefixWord ++ tailWord_2127548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127548).length < 2 ^ (prefixWord ++ tailWord_2127548).sum := by decide
  have hdescent : baseEnd_2127548 < baseStart_2127548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127572 : List Nat := [2, 4, 1, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2127572 : Nat := 118140960795 + 2127572 * 2 ^ 59
def prefixEnd_2127572 : Nat := 4983230072969 + 3 ^ 40 * 2127572 * 2
def baseEnd_2127572 : Nat := 1092467063047655098465481

theorem tailTrace_2127572 : CollatzResearch.WordTrace tailWord_2127572 prefixEnd_2127572 1092467063047655098465481 := by
  unfold tailWord_2127572
  simp only [CollatzResearch.WordTrace]
  refine ⟨38799462924088739607056485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51732617232118319476075313 38799462924088739607056485)
  ·
    refine ⟨7274899298266638676323091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38799462924088739607056485 7274899298266638676323091)
    ·
      refine ⟨10912348947399958014484637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7274899298266638676323091 10912348947399958014484637)
      ·
        refine ⟨4092130855274984255431739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10912348947399958014484637 4092130855274984255431739)
        ·
          refine ⟨6138196282912476383147609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4092130855274984255431739 6138196282912476383147609)
          ·
            refine ⟨4603647212184357287360707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6138196282912476383147609 4603647212184357287360707)
            ·
              refine ⟨6905470818276535931041061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4603647212184357287360707 6905470818276535931041061)
              ·
                refine ⟨1294775778426850487070199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6905470818276535931041061 1294775778426850487070199)
                ·
                  refine ⟨1942163667640275730605299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294775778426850487070199 1942163667640275730605299)
                  ·
                    refine ⟨2913245501460413595907949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1942163667640275730605299 2913245501460413595907949)
                    ·
                      refine ⟨1092467063047655098465481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2913245501460413595907949 1092467063047655098465481)
                      ·
                        rfl

theorem cell23_2127572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2127572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127572 prefixEnd_2127572 := by exact prefixLift 2127572
  have htrace : WordTrace (prefixWord ++ tailWord_2127572) baseStart_2127572 baseEnd_2127572 := by
    simpa [prefixWord, tailWord_2127572, baseEnd_2127572] using wordTrace_append hprefix tailTrace_2127572
  have hstable : (prefixWord ++ tailWord_2127572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127572).length < 2 ^ (prefixWord ++ tailWord_2127572).sum := by decide
  have hdescent : baseEnd_2127572 < baseStart_2127572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127584 : List Nat := [2, 1, 1, 3, 1, 2, 5, 8]
def baseStart_2127584 : Nat := 118140960795 + 2127584 * 2 ^ 59
def prefixEnd_2127584 : Nat := 4983230072969 + 3 ^ 40 * 2127584 * 2
def baseEnd_2127584 : Nat := 40461971289463298204275

theorem tailTrace_2127584 : CollatzResearch.WordTrace tailWord_2127584 prefixEnd_2127584 40461971289463298204275 := by
  unfold tailWord_2127584
  simp only [CollatzResearch.WordTrace]
  refine ⟨38799681762067002631774903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51732909016089336842366537 38799681762067002631774903)
  ·
    refine ⟨58199522643100503947662355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38799681762067002631774903 58199522643100503947662355)
    ·
      refine ⟨87299283964650755921493533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58199522643100503947662355 87299283964650755921493533)
      ·
        refine ⟨32737231486744033470560075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87299283964650755921493533 32737231486744033470560075)
        ·
          refine ⟨49105847230116050205840113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32737231486744033470560075 49105847230116050205840113)
          ·
            refine ⟨36829385422587037654380085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49105847230116050205840113 36829385422587037654380085)
            ·
              refine ⟨3452754883367534780098133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36829385422587037654380085 3452754883367534780098133)
              ·
                refine ⟨40461971289463298204275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3452754883367534780098133 40461971289463298204275)
                ·
                  rfl

theorem cell23_2127584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 8].length) (baseStart_2127584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127584 prefixEnd_2127584 := by exact prefixLift 2127584
  have htrace : WordTrace (prefixWord ++ tailWord_2127584) baseStart_2127584 baseEnd_2127584 := by
    simpa [prefixWord, tailWord_2127584, baseEnd_2127584] using wordTrace_append hprefix tailTrace_2127584
  have hstable : (prefixWord ++ tailWord_2127584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127584).length < 2 ^ (prefixWord ++ tailWord_2127584).sum := by decide
  have hdescent : baseEnd_2127584 < baseStart_2127584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127598 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_2127598 : Nat := 118140960795 + 2127598 * 2 ^ 59
def prefixEnd_2127598 : Nat := 4983230072969 + 3 ^ 40 * 2127598 * 2
def baseEnd_2127598 : Nat := 1092480413544671996740361

theorem tailTrace_2127598 : CollatzResearch.WordTrace tailWord_2127598 prefixEnd_2127598 1092480413544671996740361 := by
  unfold tailWord_2127598
  simp only [CollatzResearch.WordTrace]
  refine ⟨9699984268260410706819931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51733249430722190436372965 9699984268260410706819931)
  ·
    refine ⟨14549976402390616060229897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9699984268260410706819931 14549976402390616060229897)
    ·
      refine ⟨10912482301792962045172423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14549976402390616060229897 10912482301792962045172423)
      ·
        refine ⟨16368723452689443067758635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10912482301792962045172423 16368723452689443067758635)
        ·
          refine ⟨24553085179034164601637953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16368723452689443067758635 24553085179034164601637953)
          ·
            refine ⟨18414813884275623451228465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24553085179034164601637953 18414813884275623451228465)
            ·
              refine ⟨13811110413206717588421349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18414813884275623451228465 13811110413206717588421349)
              ·
                refine ⟨2589583202476259547829003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13811110413206717588421349 2589583202476259547829003)
                ·
                  refine ⟨3884374803714389321743505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2589583202476259547829003 3884374803714389321743505)
                  ·
                    refine ⟨2913281102785791991307629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3884374803714389321743505 2913281102785791991307629)
                    ·
                      refine ⟨1092480413544671996740361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2913281102785791991307629 1092480413544671996740361)
                      ·
                        rfl

theorem cell23_2127598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_2127598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127598 prefixEnd_2127598 := by exact prefixLift 2127598
  have htrace : WordTrace (prefixWord ++ tailWord_2127598) baseStart_2127598 baseEnd_2127598 := by
    simpa [prefixWord, tailWord_2127598, baseEnd_2127598] using wordTrace_append hprefix tailTrace_2127598
  have hstable : (prefixWord ++ tailWord_2127598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127598).length < 2 ^ (prefixWord ++ tailWord_2127598).sum := by decide
  have hdescent : baseEnd_2127598 < baseStart_2127598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127601 : List Nat := [1, 2, 2, 2, 2, 4, 3, 7]
def baseStart_2127601 : Nat := 118140960795 + 2127601 * 2 ^ 59
def prefixEnd_2127601 : Nat := 4983230072969 + 3 ^ 40 * 2127601 * 2
def baseEnd_2127601 : Nat := 40462294592097610555661

theorem tailTrace_2127601 : CollatzResearch.WordTrace tailWord_2127601 prefixEnd_2127601 40462294592097610555661 := by
  unfold tailWord_2127601
  simp only [CollatzResearch.WordTrace]
  refine ⟨77599983565072417166918657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51733322376714944777945771 77599983565072417166918657)
  ·
    refine ⟨58199987673804312875188993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77599983565072417166918657 58199987673804312875188993)
    ·
      refine ⟨43649990755353234656391745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58199987673804312875188993 43649990755353234656391745)
      ·
        refine ⟨32737493066514925992293809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43649990755353234656391745 32737493066514925992293809)
        ·
          refine ⟨24553119799886194494220357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32737493066514925992293809 24553119799886194494220357)
          ·
            refine ⟨4603709962478661467666317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24553119799886194494220357 4603709962478661467666317)
            ·
              refine ⟨1726391235929498050374869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4603709962478661467666317 1726391235929498050374869)
              ·
                refine ⟨40462294592097610555661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1726391235929498050374869 40462294592097610555661)
                ·
                  rfl

theorem cell23_2127601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 7].length) (baseStart_2127601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127601 prefixEnd_2127601 := by exact prefixLift 2127601
  have htrace : WordTrace (prefixWord ++ tailWord_2127601) baseStart_2127601 baseEnd_2127601 := by
    simpa [prefixWord, tailWord_2127601, baseEnd_2127601] using wordTrace_append hprefix tailTrace_2127601
  have hstable : (prefixWord ++ tailWord_2127601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127601).length < 2 ^ (prefixWord ++ tailWord_2127601).sum := by decide
  have hdescent : baseEnd_2127601 < baseStart_2127601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127612 : List Nat := [2, 2, 2, 1, 3, 1, 4, 3, 1, 2, 2]
def baseStart_2127612 : Nat := 118140960795 + 2127612 * 2 ^ 59
def prefixEnd_2127612 : Nat := 4983230072969 + 3 ^ 40 * 2127612 * 2
def baseEnd_2127612 : Nat := 1092487602273834941965297

theorem tailTrace_2127612 : CollatzResearch.WordTrace tailWord_2127612 prefixEnd_2127612 1092487602273834941965297 := by
  unfold tailWord_2127612
  simp only [CollatzResearch.WordTrace]
  refine ⟨38800192384016283022784545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51733589845355044030379393 38800192384016283022784545)
  ·
    refine ⟨29100144288012212267088409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38800192384016283022784545 29100144288012212267088409)
    ·
      refine ⟨21825108216009159200316307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29100144288012212267088409 21825108216009159200316307)
      ·
        refine ⟨32737662324013738800474461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21825108216009159200316307 32737662324013738800474461)
        ·
          refine ⟨12276623371505152050177923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32737662324013738800474461 12276623371505152050177923)
          ·
            refine ⟨18414935057257728075266885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12276623371505152050177923 18414935057257728075266885)
            ·
              refine ⟨3452800323235824014112541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18414935057257728075266885 3452800323235824014112541)
              ·
                refine ⟨1294800121213434005292203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3452800323235824014112541 1294800121213434005292203)
                ·
                  refine ⟨1942200181820151007938305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1294800121213434005292203 1942200181820151007938305)
                  ·
                    refine ⟨1456650136365113255953729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1942200181820151007938305 1456650136365113255953729)
                    ·
                      refine ⟨1092487602273834941965297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456650136365113255953729 1092487602273834941965297)
                      ·
                        rfl

theorem cell23_2127612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_2127612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127612 prefixEnd_2127612 := by exact prefixLift 2127612
  have htrace : WordTrace (prefixWord ++ tailWord_2127612) baseStart_2127612 baseEnd_2127612 := by
    simpa [prefixWord, tailWord_2127612, baseEnd_2127612] using wordTrace_append hprefix tailTrace_2127612
  have hstable : (prefixWord ++ tailWord_2127612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127612).length < 2 ^ (prefixWord ++ tailWord_2127612).sum := by decide
  have hdescent : baseEnd_2127612 < baseStart_2127612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127685 : List Nat := [1, 3, 1, 1, 1, 2, 4, 4, 2, 2, 2]
def baseStart_2127685 : Nat := 118140960795 + 2127685 * 2 ^ 59
def prefixEnd_2127685 : Nat := 4983230072969 + 3 ^ 40 * 2127685 * 2
def baseEnd_2127685 : Nat := 1092525086361613156352461

theorem tailTrace_2127685 : CollatzResearch.WordTrace tailWord_2127685 prefixEnd_2127685 1092525086361613156352461 := by
  unfold tailWord_2127685
  simp only [CollatzResearch.WordTrace]
  refine ⟨77603047296768099512976509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51735364864512066341984339 77603047296768099512976509)
  ·
    refine ⟨29101142736288037317366191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77603047296768099512976509 29101142736288037317366191)
    ·
      refine ⟨43651714104432055976049287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29101142736288037317366191 43651714104432055976049287)
      ·
        refine ⟨65477571156648083964073931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43651714104432055976049287 65477571156648083964073931)
        ·
          refine ⟨98216356734972125946110897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65477571156648083964073931 98216356734972125946110897)
          ·
            refine ⟨73662267551229094459583173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98216356734972125946110897 73662267551229094459583173)
            ·
              refine ⟨13811675165855455211171845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73662267551229094459583173 13811675165855455211171845)
              ·
                refine ⟨2589689093597897852094721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13811675165855455211171845 2589689093597897852094721)
                ·
                  refine ⟨1942266820198423389071041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2589689093597897852094721 1942266820198423389071041)
                  ·
                    refine ⟨1456700115148817541803281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1942266820198423389071041 1456700115148817541803281)
                    ·
                      refine ⟨1092525086361613156352461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456700115148817541803281 1092525086361613156352461)
                      ·
                        rfl

theorem cell23_2127685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 2, 2].length) (baseStart_2127685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127685 prefixEnd_2127685 := by exact prefixLift 2127685
  have htrace : WordTrace (prefixWord ++ tailWord_2127685) baseStart_2127685 baseEnd_2127685 := by
    simpa [prefixWord, tailWord_2127685, baseEnd_2127685] using wordTrace_append hprefix tailTrace_2127685
  have hstable : (prefixWord ++ tailWord_2127685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127685).length < 2 ^ (prefixWord ++ tailWord_2127685).sum := by decide
  have hdescent : baseEnd_2127685 < baseStart_2127685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127741 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_2127741 : Nat := 118140960795 + 2127741 * 2 ^ 59
def prefixEnd_2127741 : Nat := 4983230072969 + 3 ^ 40 * 2127741 * 2
def baseEnd_2127741 : Nat := 1092553841278264937252203

theorem tailTrace_2127741 : CollatzResearch.WordTrace tailWord_2127741 prefixEnd_2127741 1092553841278264937252203 := by
  unfold tailWord_2127741
  simp only [CollatzResearch.WordTrace]
  refine ⟨77605089784565221077015077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51736726523043480718010051 77605089784565221077015077)
  ·
    refine ⟨14550954334605978951940327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77605089784565221077015077 14550954334605978951940327)
    ·
      refine ⟨21826431501908968427910491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14550954334605978951940327 21826431501908968427910491)
      ·
        refine ⟨32739647252863452641865737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21826431501908968427910491 32739647252863452641865737)
        ·
          refine ⟨24554735439647589481399303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32739647252863452641865737 24554735439647589481399303)
          ·
            refine ⟨36832103159471384222098955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24554735439647589481399303 36832103159471384222098955)
            ·
              refine ⟨55248154739207076333148433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36832103159471384222098955 55248154739207076333148433)
              ·
                refine ⟨41436116054405307249861325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55248154739207076333148433 41436116054405307249861325)
                ·
                  refine ⟨15538543520401990218697997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41436116054405307249861325 15538543520401990218697997)
                  ·
                    refine ⟨5826953820150746332011749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15538543520401990218697997 5826953820150746332011749)
                    ·
                      refine ⟨1092553841278264937252203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5826953820150746332011749 1092553841278264937252203)
                      ·
                        rfl

theorem cell23_2127741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_2127741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127741 prefixEnd_2127741 := by exact prefixLift 2127741
  have htrace : WordTrace (prefixWord ++ tailWord_2127741) baseStart_2127741 baseEnd_2127741 := by
    simpa [prefixWord, tailWord_2127741, baseEnd_2127741] using wordTrace_append hprefix tailTrace_2127741
  have hstable : (prefixWord ++ tailWord_2127741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127741).length < 2 ^ (prefixWord ++ tailWord_2127741).sum := by decide
  have hdescent : baseEnd_2127741 < baseStart_2127741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127742 : List Nat := [4, 2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_2127742 : Nat := 118140960795 + 2127742 * 2 ^ 59
def prefixEnd_2127742 : Nat := 4983230072969 + 3 ^ 40 * 2127742 * 2
def baseEnd_2127742 : Nat := 121394928306546603704411

theorem tailTrace_2127742 : CollatzResearch.WordTrace tailWord_2127742 prefixEnd_2127742 121394928306546603704411 := by
  unfold tailWord_2127742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9700640782195199780975185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51736750838374398831867653 9700640782195199780975185)
  ·
    refine ⟨7275480586646399835731389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9700640782195199780975185 7275480586646399835731389)
    ·
      refine ⟨2728305219992399938399271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7275480586646399835731389 2728305219992399938399271)
      ·
        refine ⟨4092457829988599907598907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2728305219992399938399271 4092457829988599907598907)
        ·
          refine ⟨6138686744982899861398361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4092457829988599907598907 6138686744982899861398361)
          ·
            refine ⟨4604015058737174896048771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6138686744982899861398361 4604015058737174896048771)
            ·
              refine ⟨6906022588105762344073157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4604015058737174896048771 6906022588105762344073157)
              ·
                refine ⟨1294879235269830439513717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6906022588105762344073157 1294879235269830439513717)
                ·
                  refine ⟨121394928306546603704411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1294879235269830439513717 121394928306546603704411)
                  ·
                    rfl

theorem cell23_2127742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_2127742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127742 prefixEnd_2127742 := by exact prefixLift 2127742
  have htrace : WordTrace (prefixWord ++ tailWord_2127742) baseStart_2127742 baseEnd_2127742 := by
    simpa [prefixWord, tailWord_2127742, baseEnd_2127742] using wordTrace_append hprefix tailTrace_2127742
  have hstable : (prefixWord ++ tailWord_2127742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127742).length < 2 ^ (prefixWord ++ tailWord_2127742).sum := by decide
  have hdescent : baseEnd_2127742 < baseStart_2127742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127801 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2127801 : Nat := 118140960795 + 2127801 * 2 ^ 59
def prefixEnd_2127801 : Nat := 4983230072969 + 3 ^ 40 * 2127801 * 2
def baseEnd_2127801 : Nat := 1092584650117534702501927

theorem tailTrace_2127801 : CollatzResearch.WordTrace tailWord_2127801 prefixEnd_2127801 1092584650117534702501927 := by
  unfold tailWord_2127801
  simp only [CollatzResearch.WordTrace]
  refine ⟨77607278164347851324199257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51738185442898567549466171 77607278164347851324199257)
  ·
    refine ⟨58205458623260888493149443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77607278164347851324199257 58205458623260888493149443)
    ·
      refine ⟨87308187934891332739724165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58205458623260888493149443 87308187934891332739724165)
      ·
        refine ⟨16370285237792124888698281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87308187934891332739724165 16370285237792124888698281)
        ·
          refine ⟨12277713928344093666523711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16370285237792124888698281 12277713928344093666523711)
          ·
            refine ⟨18416570892516140499785567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12277713928344093666523711 18416570892516140499785567)
            ·
              refine ⟨27624856338774210749678351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18416570892516140499785567 27624856338774210749678351)
              ·
                refine ⟨41437284508161316124517527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27624856338774210749678351 41437284508161316124517527)
                ·
                  refine ⟨62155926762241974186776291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41437284508161316124517527 62155926762241974186776291)
                  ·
                    refine ⟨93233890143362961280164437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62155926762241974186776291 93233890143362961280164437)
                    ·
                      refine ⟨1092584650117534702501927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 93233890143362961280164437 1092584650117534702501927)
                      ·
                        rfl

theorem cell23_2127801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2127801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127801 prefixEnd_2127801 := by exact prefixLift 2127801
  have htrace : WordTrace (prefixWord ++ tailWord_2127801) baseStart_2127801 baseEnd_2127801 := by
    simpa [prefixWord, tailWord_2127801, baseEnd_2127801] using wordTrace_append hprefix tailTrace_2127801
  have hstable : (prefixWord ++ tailWord_2127801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127801).length < 2 ^ (prefixWord ++ tailWord_2127801).sum := by decide
  have hdescent : baseEnd_2127801 < baseStart_2127801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127848 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2127848 : Nat := 118140960795 + 2127848 * 2 ^ 59
def prefixEnd_2127848 : Nat := 4983230072969 + 3 ^ 40 * 2127848 * 2
def baseEnd_2127848 : Nat := 1092608783708296018614211

theorem tailTrace_2127848 : CollatzResearch.WordTrace tailWord_2127848 prefixEnd_2127848 1092608783708296018614211 := by
  unfold tailWord_2127848
  simp only [CollatzResearch.WordTrace]
  refine ⟨38804496197588789175580099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51739328263451718900773465 38804496197588789175580099)
  ·
    refine ⟨58206744296383183763370149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38804496197588789175580099 58206744296383183763370149)
    ·
      refine ⟨10913764555571846955631903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58206744296383183763370149 10913764555571846955631903)
      ·
        refine ⟨16370646833357770433447855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10913764555571846955631903 16370646833357770433447855)
        ·
          refine ⟨24555970250036655650171783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16370646833357770433447855 24555970250036655650171783)
          ·
            refine ⟨36833955375054983475257675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24555970250036655650171783 36833955375054983475257675)
            ·
              refine ⟨55250933062582475212886513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36833955375054983475257675 55250933062582475212886513)
              ·
                refine ⟨41438199796936856409664885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55250933062582475212886513 41438199796936856409664885)
                ·
                  refine ⟨3884831230962830288406083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41438199796936856409664885 3884831230962830288406083)
                  ·
                    refine ⟨5827246846444245432609125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3884831230962830288406083 5827246846444245432609125)
                    ·
                      refine ⟨1092608783708296018614211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5827246846444245432609125 1092608783708296018614211)
                      ·
                        rfl

theorem cell23_2127848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2127848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127848 prefixEnd_2127848 := by exact prefixLift 2127848
  have htrace : WordTrace (prefixWord ++ tailWord_2127848) baseStart_2127848 baseEnd_2127848 := by
    simpa [prefixWord, tailWord_2127848, baseEnd_2127848] using wordTrace_append hprefix tailTrace_2127848
  have hstable : (prefixWord ++ tailWord_2127848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127848).length < 2 ^ (prefixWord ++ tailWord_2127848).sum := by decide
  have hdescent : baseEnd_2127848 < baseStart_2127848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127868 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_2127868 : Nat := 118140960795 + 2127868 * 2 ^ 59
def prefixEnd_2127868 : Nat := 4983230072969 + 3 ^ 40 * 2127868 * 2
def baseEnd_2127868 : Nat := 1092619053321385940364119

theorem tailTrace_2127868 : CollatzResearch.WordTrace tailWord_2127868 prefixEnd_2127868 1092619053321385940364119 := by
  unfold tailWord_2127868
  simp only [CollatzResearch.WordTrace]
  refine ⟨38804860927552560883444129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51739814570070081177925505 38804860927552560883444129)
  ·
    refine ⟨29103645695664420662583097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38804860927552560883444129 29103645695664420662583097)
    ·
      refine ⟨21827734271748315496937323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29103645695664420662583097 21827734271748315496937323)
      ·
        refine ⟨32741601407622473245405985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21827734271748315496937323 32741601407622473245405985)
        ·
          refine ⟨24556201055716854934054489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32741601407622473245405985 24556201055716854934054489)
          ·
            refine ⟨18417150791787641200540867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24556201055716854934054489 18417150791787641200540867)
            ·
              refine ⟨27625726187681461800811301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18417150791787641200540867 27625726187681461800811301)
              ·
                refine ⟨5179823660190274087652119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27625726187681461800811301 5179823660190274087652119)
                ·
                  refine ⟨7769735490285411131478179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5179823660190274087652119 7769735490285411131478179)
                  ·
                    refine ⟨11654603235428116697217269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7769735490285411131478179 11654603235428116697217269)
                    ·
                      refine ⟨1092619053321385940364119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11654603235428116697217269 1092619053321385940364119)
                      ·
                        rfl

theorem cell23_2127868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_2127868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127868 prefixEnd_2127868 := by exact prefixLift 2127868
  have htrace : WordTrace (prefixWord ++ tailWord_2127868) baseStart_2127868 baseEnd_2127868 := by
    simpa [prefixWord, tailWord_2127868, baseEnd_2127868] using wordTrace_append hprefix tailTrace_2127868
  have hstable : (prefixWord ++ tailWord_2127868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127868).length < 2 ^ (prefixWord ++ tailWord_2127868).sum := by decide
  have hdescent : baseEnd_2127868 < baseStart_2127868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127932 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_2127932 : Nat := 118140960795 + 2127932 * 2 ^ 59
def prefixEnd_2127932 : Nat := 4983230072969 + 3 ^ 40 * 2127932 * 2
def baseEnd_2127932 : Nat := 1092651916083273689963825

theorem tailTrace_2127932 : CollatzResearch.WordTrace tailWord_2127932 prefixEnd_2127932 1092651916083273689963825 := by
  unfold tailWord_2127932
  simp only [CollatzResearch.WordTrace]
  refine ⟨38806028063436630348609025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51741370751248840464812033 38806028063436630348609025)
  ·
    refine ⟨29104521047577472761456769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38806028063436630348609025 29104521047577472761456769)
    ·
      refine ⟨21828390785683104571092577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29104521047577472761456769 21828390785683104571092577)
      ·
        refine ⟨16371293089262328428319433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21828390785683104571092577 16371293089262328428319433)
        ·
          refine ⟨12278469816946746321239575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16371293089262328428319433 12278469816946746321239575)
          ·
            refine ⟨18417704725420119481859363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12278469816946746321239575 18417704725420119481859363)
            ·
              refine ⟨27626557088130179222789045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18417704725420119481859363 27626557088130179222789045)
              ·
                refine ⟨2589989727012204302136473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27626557088130179222789045 2589989727012204302136473)
                ·
                  refine ⟨1942492295259153226602355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2589989727012204302136473 1942492295259153226602355)
                  ·
                    refine ⟨2913738442888729839903533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1942492295259153226602355 2913738442888729839903533)
                    ·
                      refine ⟨1092651916083273689963825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2913738442888729839903533 1092651916083273689963825)
                      ·
                        rfl

theorem cell23_2127932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_2127932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127932 prefixEnd_2127932 := by exact prefixLift 2127932
  have htrace : WordTrace (prefixWord ++ tailWord_2127932) baseStart_2127932 baseEnd_2127932 := by
    simpa [prefixWord, tailWord_2127932, baseEnd_2127932] using wordTrace_append hprefix tailTrace_2127932
  have hstable : (prefixWord ++ tailWord_2127932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127932).length < 2 ^ (prefixWord ++ tailWord_2127932).sum := by decide
  have hdescent : baseEnd_2127932 < baseStart_2127932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2127959 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 1, 3, 2]
def baseStart_2127959 : Nat := 118140960795 + 2127959 * 2 ^ 59
def prefixEnd_2127959 : Nat := 4983230072969 + 3 ^ 40 * 2127959 * 2
def baseEnd_2127959 : Nat := 1092665780060945084326201

theorem tailTrace_2127959 : CollatzResearch.WordTrace tailWord_2127959 prefixEnd_2127959 1092665780060945084326201 := by
  unfold tailWord_2127959
  simp only [CollatzResearch.WordTrace]
  refine ⟨77613040897775444308450931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51742027265183629538967287 77613040897775444308450931)
  ·
    refine ⟨116419561346663166462676397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77613040897775444308450931 116419561346663166462676397)
    ·
      refine ⟨43657335504998687423503649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116419561346663166462676397 43657335504998687423503649)
      ·
        refine ⟨32743001628749015567627737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43657335504998687423503649 32743001628749015567627737)
        ·
          refine ⟨24557251221561761675720803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32743001628749015567627737 24557251221561761675720803)
          ·
            refine ⟨36835876832342642513581205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24557251221561761675720803 36835876832342642513581205)
            ·
              refine ⟨1726681726516061367824119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36835876832342642513581205 1726681726516061367824119)
              ·
                refine ⟨2590022589774092051736179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726681726516061367824119 2590022589774092051736179)
                ·
                  refine ⟨3885033884661138077604269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2590022589774092051736179 3885033884661138077604269)
                  ·
                    refine ⟨1456887706747926779101601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3885033884661138077604269 1456887706747926779101601)
                    ·
                      refine ⟨1092665780060945084326201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1456887706747926779101601 1092665780060945084326201)
                      ·
                        rfl

theorem cell23_2127959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_2127959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2127959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2127959 prefixEnd_2127959 := by exact prefixLift 2127959
  have htrace : WordTrace (prefixWord ++ tailWord_2127959) baseStart_2127959 baseEnd_2127959 := by
    simpa [prefixWord, tailWord_2127959, baseEnd_2127959] using wordTrace_append hprefix tailTrace_2127959
  have hstable : (prefixWord ++ tailWord_2127959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2127959).length < 2 ^ (prefixWord ++ tailWord_2127959).sum := by decide
  have hdescent : baseEnd_2127959 < baseStart_2127959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2127959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128029 : List Nat := [1, 4, 2, 1, 1, 4, 3, 2, 5]
def baseStart_2128029 : Nat := 118140960795 + 2128029 * 2 ^ 59
def prefixEnd_2128029 : Nat := 4983230072969 + 3 ^ 40 * 2128029 * 2
def baseEnd_2128029 : Nat := 121411302634084423383431

theorem tailTrace_2128029 : CollatzResearch.WordTrace tailWord_2128029 prefixEnd_2128029 121411302634084423383431 := by
  unfold tailWord_2128029
  simp only [CollatzResearch.WordTrace]
  refine ⟨77615594007521846263499141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51743729338347897508999427 77615594007521846263499141)
  ·
    refine ⟨14552923876410346174406089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77615594007521846263499141 14552923876410346174406089)
    ·
      refine ⟨10914692907307759630804567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14552923876410346174406089 10914692907307759630804567)
      ·
        refine ⟨16372039360961639446206851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10914692907307759630804567 16372039360961639446206851)
        ·
          refine ⟨24558059041442459169310277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16372039360961639446206851 24558059041442459169310277)
          ·
            refine ⟨4604636070270461094245677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24558059041442459169310277 4604636070270461094245677)
            ·
              refine ⟨1726738526351422910342129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4604636070270461094245677 1726738526351422910342129)
              ·
                refine ⟨1295053894763567182756597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1726738526351422910342129 1295053894763567182756597)
                ·
                  refine ⟨121411302634084423383431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1295053894763567182756597 121411302634084423383431)
                  ·
                    rfl

theorem cell23_2128029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_2128029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128029 prefixEnd_2128029 := by exact prefixLift 2128029
  have htrace : WordTrace (prefixWord ++ tailWord_2128029) baseStart_2128029 baseEnd_2128029 := by
    simpa [prefixWord, tailWord_2128029, baseEnd_2128029] using wordTrace_append hprefix tailTrace_2128029
  have hstable : (prefixWord ++ tailWord_2128029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128029).length < 2 ^ (prefixWord ++ tailWord_2128029).sum := by decide
  have hdescent : baseEnd_2128029 < baseStart_2128029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128095 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 3]
def baseStart_2128095 : Nat := 118140960795 + 2128095 * 2 ^ 59
def prefixEnd_2128095 : Nat := 4983230072969 + 3 ^ 40 * 2128095 * 2
def baseEnd_2128095 : Nat := 1092735613429956552225575

theorem tailTrace_2128095 : CollatzResearch.WordTrace tailWord_2128095 prefixEnd_2128095 1092735613429956552225575 := by
  unfold tailWord_2128095
  simp only [CollatzResearch.WordTrace]
  refine ⟨77618001225282739535401739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51745334150188493023601159 77618001225282739535401739)
  ·
    refine ⟨116427001837924109303102609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77618001225282739535401739 116427001837924109303102609)
    ·
      refine ⟨87320251378443081977326957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116427001837924109303102609 87320251378443081977326957)
      ·
        refine ⟨32745094266916155741497609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 87320251378443081977326957 32745094266916155741497609)
        ·
          refine ⟨24558820700187116806123207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32745094266916155741497609 24558820700187116806123207)
          ·
            refine ⟨36838231050280675209184811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24558820700187116806123207 36838231050280675209184811)
            ·
              refine ⟨55257346575421012813777217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36838231050280675209184811 55257346575421012813777217)
              ·
                refine ⟨41443009931565759610332913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55257346575421012813777217 41443009931565759610332913)
                ·
                  refine ⟨31082257448674319707749685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41443009931565759610332913 31082257448674319707749685)
                  ·
                    refine ⟨2913961635813217472601533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31082257448674319707749685 2913961635813217472601533)
                    ·
                      refine ⟨1092735613429956552225575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2913961635813217472601533 1092735613429956552225575)
                      ·
                        rfl

theorem cell23_2128095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_2128095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128095 prefixEnd_2128095 := by exact prefixLift 2128095
  have htrace : WordTrace (prefixWord ++ tailWord_2128095) baseStart_2128095 baseEnd_2128095 := by
    simpa [prefixWord, tailWord_2128095, baseEnd_2128095] using wordTrace_append hprefix tailTrace_2128095
  have hstable : (prefixWord ++ tailWord_2128095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128095).length < 2 ^ (prefixWord ++ tailWord_2128095).sum := by decide
  have hdescent : baseEnd_2128095 < baseStart_2128095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128115 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 3, 5]
def baseStart_2128115 : Nat := 118140960795 + 2128115 * 2 ^ 59
def prefixEnd_2128115 : Nat := 4983230072969 + 3 ^ 40 * 2128115 * 2
def baseEnd_2128115 : Nat := 364248627681015491325161

theorem tailTrace_2128115 : CollatzResearch.WordTrace tailWord_2128115 prefixEnd_2128115 364248627681015491325161 := by
  unfold tailWord_2128115
  simp only [CollatzResearch.WordTrace]
  refine ⟨77618730685210282951129799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51745820456806855300753199 77618730685210282951129799)
  ·
    refine ⟨116428096027815424426694699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77618730685210282951129799 116428096027815424426694699)
    ·
      refine ⟨174642144041723136640042049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116428096027815424426694699 174642144041723136640042049)
      ·
        refine ⟨130981608031292352480031537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174642144041723136640042049 130981608031292352480031537)
        ·
          refine ⟨98236206023469264360023653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130981608031292352480031537 98236206023469264360023653)
          ·
            refine ⟨18419288629400487067504435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98236206023469264360023653 18419288629400487067504435)
            ·
              refine ⟨27628932944100730601256653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18419288629400487067504435 27628932944100730601256653)
              ·
                refine ⟨10360849854037773975471245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27628932944100730601256653 10360849854037773975471245)
                ·
                  refine ⟨3885318695264165240801717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10360849854037773975471245 3885318695264165240801717)
                  ·
                    refine ⟨364248627681015491325161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3885318695264165240801717 364248627681015491325161)
                    ·
                      rfl

theorem cell23_2128115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 5].length) (baseStart_2128115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128115 prefixEnd_2128115 := by exact prefixLift 2128115
  have htrace : WordTrace (prefixWord ++ tailWord_2128115) baseStart_2128115 baseEnd_2128115 := by
    simpa [prefixWord, tailWord_2128115, baseEnd_2128115] using wordTrace_append hprefix tailTrace_2128115
  have hstable : (prefixWord ++ tailWord_2128115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128115).length < 2 ^ (prefixWord ++ tailWord_2128115).sum := by decide
  have hdescent : baseEnd_2128115 < baseStart_2128115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128155 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 5]
def baseStart_2128155 : Nat := 118140960795 + 2128155 * 2 ^ 59
def prefixEnd_2128155 : Nat := 4983230072969 + 3 ^ 40 * 2128155 * 2
def baseEnd_2128155 : Nat := 1092766422269226317475299

theorem tailTrace_2128155 : CollatzResearch.WordTrace tailWord_2128155 prefixEnd_2128155 1092766422269226317475299 := by
  unfold tailWord_2128155
  simp only [CollatzResearch.WordTrace]
  refine ⟨77620189605065369782585919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51746793070043579855057279 77620189605065369782585919)
  ·
    refine ⟨116430284407598054673878879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77620189605065369782585919 116430284407598054673878879)
    ·
      refine ⟨174645426611397082010818319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116430284407598054673878879 174645426611397082010818319)
      ·
        refine ⟨261968139917095623016227479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174645426611397082010818319 261968139917095623016227479)
        ·
          refine ⟨392952209875643434524341219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261968139917095623016227479 392952209875643434524341219)
          ·
            refine ⟨589428314813465151786511829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392952209875643434524341219 589428314813465151786511829)
            ·
              refine ⟨13814726128440589494996371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 589428314813465151786511829 13814726128440589494996371)
              ·
                refine ⟨20722089192660884242494557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13814726128440589494996371 20722089192660884242494557)
                ·
                  refine ⟨7770783447247831590935459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20722089192660884242494557 7770783447247831590935459)
                  ·
                    refine ⟨11656175170871747386403189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7770783447247831590935459 11656175170871747386403189)
                    ·
                      refine ⟨1092766422269226317475299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11656175170871747386403189 1092766422269226317475299)
                      ·
                        rfl

theorem cell23_2128155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 5].length) (baseStart_2128155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128155 prefixEnd_2128155 := by exact prefixLift 2128155
  have htrace : WordTrace (prefixWord ++ tailWord_2128155) baseStart_2128155 baseEnd_2128155 := by
    simpa [prefixWord, tailWord_2128155, baseEnd_2128155] using wordTrace_append hprefix tailTrace_2128155
  have hstable : (prefixWord ++ tailWord_2128155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128155).length < 2 ^ (prefixWord ++ tailWord_2128155).sum := by decide
  have hdescent : baseEnd_2128155 < baseStart_2128155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128172 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 3]
def baseStart_2128172 : Nat := 118140960795 + 2128172 * 2 ^ 59
def prefixEnd_2128172 : Nat := 4983230072969 + 3 ^ 40 * 2128172 * 2
def baseEnd_2128172 : Nat := 1092775151440352750962721

theorem tailTrace_2128172 : CollatzResearch.WordTrace tailWord_2128172 prefixEnd_2128172 1092775151440352750962721 := by
  unfold tailWord_2128172
  simp only [CollatzResearch.WordTrace]
  refine ⟨38810404823001890842977385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51747206430669187790636513 38810404823001890842977385)
  ·
    refine ⟨29107803617251418132233039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38810404823001890842977385 29107803617251418132233039)
    ·
      refine ⟨43661705425877127198349559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29107803617251418132233039 43661705425877127198349559)
      ·
        refine ⟨65492558138815690797524339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43661705425877127198349559 65492558138815690797524339)
        ·
          refine ⟨98238837208223536196286509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65492558138815690797524339 98238837208223536196286509)
          ·
            refine ⟨36839563953083826073607441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98238837208223536196286509 36839563953083826073607441)
            ·
              refine ⟨27629672964812869555205581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36839563953083826073607441 27629672964812869555205581)
              ·
                refine ⟨10361127361804826083202093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27629672964812869555205581 10361127361804826083202093)
                ·
                  refine ⟨3885422760676809781200785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10361127361804826083202093 3885422760676809781200785)
                  ·
                    refine ⟨2914067070507607335900589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3885422760676809781200785 2914067070507607335900589)
                    ·
                      refine ⟨1092775151440352750962721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2914067070507607335900589 1092775151440352750962721)
                      ·
                        rfl

theorem cell23_2128172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_2128172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128172 prefixEnd_2128172 := by exact prefixLift 2128172
  have htrace : WordTrace (prefixWord ++ tailWord_2128172) baseStart_2128172 baseEnd_2128172 := by
    simpa [prefixWord, tailWord_2128172, baseEnd_2128172] using wordTrace_append hprefix tailTrace_2128172
  have hstable : (prefixWord ++ tailWord_2128172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128172).length < 2 ^ (prefixWord ++ tailWord_2128172).sum := by decide
  have hdescent : baseEnd_2128172 < baseStart_2128172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128180 : List Nat := [2, 5, 1, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_2128180 : Nat := 118140960795 + 2128180 * 2 ^ 59
def prefixEnd_2128180 : Nat := 4983230072969 + 3 ^ 40 * 2128180 * 2
def baseEnd_2128180 : Nat := 1092779259285588719662685

theorem tailTrace_2128180 : CollatzResearch.WordTrace tailWord_2128180 prefixEnd_2128180 1092779259285588719662685 := by
  unfold tailWord_2128180
  simp only [CollatzResearch.WordTrace]
  refine ⟨38810550714987399526122997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51747400953316532701497329 38810550714987399526122997)
  ·
    refine ⟨3638489129530068705574031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38810550714987399526122997 3638489129530068705574031)
    ·
      refine ⟨5457733694295103058361047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3638489129530068705574031 5457733694295103058361047)
      ·
        refine ⟨8186600541442654587541571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5457733694295103058361047 8186600541442654587541571)
        ·
          refine ⟨12279900812163981881312357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8186600541442654587541571 12279900812163981881312357)
          ·
            refine ⟨2302481402280746602746067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12279900812163981881312357 2302481402280746602746067)
            ·
              refine ⟨3453722103421119904119101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302481402280746602746067 3453722103421119904119101)
              ·
                refine ⟨1295145788782919964044663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3453722103421119904119101 1295145788782919964044663)
                ·
                  refine ⟨1942718683174379946066995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295145788782919964044663 1942718683174379946066995)
                  ·
                    refine ⟨2914078024761569919100493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1942718683174379946066995 2914078024761569919100493)
                    ·
                      refine ⟨1092779259285588719662685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2914078024761569919100493 1092779259285588719662685)
                      ·
                        rfl

theorem cell23_2128180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_2128180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128180 prefixEnd_2128180 := by exact prefixLift 2128180
  have htrace : WordTrace (prefixWord ++ tailWord_2128180) baseStart_2128180 baseEnd_2128180 := by
    simpa [prefixWord, tailWord_2128180, baseEnd_2128180] using wordTrace_append hprefix tailTrace_2128180
  have hstable : (prefixWord ++ tailWord_2128180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128180).length < 2 ^ (prefixWord ++ tailWord_2128180).sum := by decide
  have hdescent : baseEnd_2128180 < baseStart_2128180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128213 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 2, 4]
def baseStart_2128213 : Nat := 118140960795 + 2128213 * 2 ^ 59
def prefixEnd_2128213 : Nat := 4983230072969 + 3 ^ 40 * 2128213 * 2
def baseEnd_2128213 : Nat := 364265401382395696850011

theorem tailTrace_2128213 : CollatzResearch.WordTrace tailWord_2128213 prefixEnd_2128213 364265401382395696850011 := by
  unfold tailWord_2128213
  simp only [CollatzResearch.WordTrace]
  refine ⟨77622305038855245688197293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51748203359236830458798195 77622305038855245688197293)
  ·
    refine ⟨29108364389570717133073985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77622305038855245688197293 29108364389570717133073985)
    ·
      refine ⟨21831273292178037849805489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29108364389570717133073985 21831273292178037849805489)
      ·
        refine ⟨16373454969133528387354117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21831273292178037849805489 16373454969133528387354117)
        ·
          refine ⟨3070022806712536572628897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16373454969133528387354117 3070022806712536572628897)
          ·
            refine ⟨2302517105034402429471673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3070022806712536572628897 2302517105034402429471673)
            ·
              refine ⟨1726887828775801822103755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2302517105034402429471673 1726887828775801822103755)
              ·
                refine ⟨2590331743163702733155633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1726887828775801822103755 2590331743163702733155633)
                ·
                  refine ⟨1942748807372777049866725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2590331743163702733155633 1942748807372777049866725)
                  ·
                    refine ⟨364265401382395696850011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1942748807372777049866725 364265401382395696850011)
                    ·
                      rfl

theorem cell23_2128213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_2128213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128213 prefixEnd_2128213 := by exact prefixLift 2128213
  have htrace : WordTrace (prefixWord ++ tailWord_2128213) baseStart_2128213 baseEnd_2128213 := by
    simpa [prefixWord, tailWord_2128213, baseEnd_2128213] using wordTrace_append hprefix tailTrace_2128213
  have hstable : (prefixWord ++ tailWord_2128213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128213).length < 2 ^ (prefixWord ++ tailWord_2128213).sum := by decide
  have hdescent : baseEnd_2128213 < baseStart_2128213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128220 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_2128220 : Nat := 118140960795 + 2128220 * 2 ^ 59
def prefixEnd_2128220 : Nat := 4983230072969 + 3 ^ 40 * 2128220 * 2
def baseEnd_2128220 : Nat := 1092799798511768563162501

theorem tailTrace_2128220 : CollatzResearch.WordTrace tailWord_2128220 prefixEnd_2128220 1092799798511768563162501 := by
  unfold tailWord_2128220
  simp only [CollatzResearch.WordTrace]
  refine ⟨38811280174914942941851057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51748373566553257255801409 38811280174914942941851057)
  ·
    refine ⟨29108460131186207206388293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38811280174914942941851057 29108460131186207206388293)
    ·
      refine ⟨5457836274597413851197805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29108460131186207206388293 5457836274597413851197805)
      ·
        refine ⟨2046688602974030194199177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5457836274597413851197805 2046688602974030194199177)
        ·
          refine ⟨1535016452230522645649383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2046688602974030194199177 1535016452230522645649383)
          ·
            refine ⟨2302524678345783968474075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535016452230522645649383 2302524678345783968474075)
            ·
              refine ⟨3453787017518675952711113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302524678345783968474075 3453787017518675952711113)
              ·
                refine ⟨2590340263139006964533335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3453787017518675952711113 2590340263139006964533335)
                ·
                  refine ⟨3885510394708510446800003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2590340263139006964533335 3885510394708510446800003)
                  ·
                    refine ⟨5828265592062765670200005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3885510394708510446800003 5828265592062765670200005)
                    ·
                      refine ⟨1092799798511768563162501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5828265592062765670200005 1092799798511768563162501)
                      ·
                        rfl

theorem cell23_2128220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_2128220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128220 prefixEnd_2128220 := by exact prefixLift 2128220
  have htrace : WordTrace (prefixWord ++ tailWord_2128220) baseStart_2128220 baseEnd_2128220 := by
    simpa [prefixWord, tailWord_2128220, baseEnd_2128220] using wordTrace_append hprefix tailTrace_2128220
  have hstable : (prefixWord ++ tailWord_2128220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128220).length < 2 ^ (prefixWord ++ tailWord_2128220).sum := by decide
  have hdescent : baseEnd_2128220 < baseStart_2128220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128225 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_2128225 : Nat := 118140960795 + 2128225 * 2 ^ 59
def prefixEnd_2128225 : Nat := 4983230072969 + 3 ^ 40 * 2128225 * 2
def baseEnd_2128225 : Nat := 1092802365915041043599977

theorem tailTrace_2128225 : CollatzResearch.WordTrace tailWord_2128225 prefixEnd_2128225 1092802365915041043599977 := by
  unfold tailWord_2128225
  simp only [CollatzResearch.WordTrace]
  refine ⟨77622742714811771737634129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51748495143207847825089419 77622742714811771737634129)
  ·
    refine ⟨58217057036108828803225597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77622742714811771737634129 58217057036108828803225597)
    ·
      refine ⟨21831396388540810801209599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58217057036108828803225597 21831396388540810801209599)
      ·
        refine ⟨32747094582811216201814399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21831396388540810801209599 32747094582811216201814399)
        ·
          refine ⟨49120641874216824302721599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32747094582811216201814399 49120641874216824302721599)
          ·
            refine ⟨73680962811325236454082399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49120641874216824302721599 73680962811325236454082399)
            ·
              refine ⟨110521444216987854681123599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73680962811325236454082399 110521444216987854681123599)
              ·
                refine ⟨165782166325481782021685399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110521444216987854681123599 165782166325481782021685399)
                ·
                  refine ⟨248673249488222673032528099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165782166325481782021685399 248673249488222673032528099)
                  ·
                    refine ⟨373009874232334009548792149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 248673249488222673032528099 373009874232334009548792149)
                    ·
                      refine ⟨1092802365915041043599977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 373009874232334009548792149 1092802365915041043599977)
                      ·
                        rfl

theorem cell23_2128225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_2128225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128225 prefixEnd_2128225 := by exact prefixLift 2128225
  have htrace : WordTrace (prefixWord ++ tailWord_2128225) baseStart_2128225 baseEnd_2128225 := by
    simpa [prefixWord, tailWord_2128225, baseEnd_2128225] using wordTrace_append hprefix tailTrace_2128225
  have hstable : (prefixWord ++ tailWord_2128225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128225).length < 2 ^ (prefixWord ++ tailWord_2128225).sum := by decide
  have hdescent : baseEnd_2128225 < baseStart_2128225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128235 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 1, 8]
def baseStart_2128235 : Nat := 118140960795 + 2128235 * 2 ^ 59
def prefixEnd_2128235 : Nat := 4983230072969 + 3 ^ 40 * 2128235 * 2
def baseEnd_2128235 : Nat := 364269166907195334824977

theorem tailTrace_2128235 : CollatzResearch.WordTrace tailWord_2128235 prefixEnd_2128235 364269166907195334824977 := by
  unfold tailWord_2128235
  simp only [CollatzResearch.WordTrace]
  refine ⟨77623107444775543445498159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51748738296517028963665439 77623107444775543445498159)
  ·
    refine ⟨116434661167163315168247239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77623107444775543445498159 116434661167163315168247239)
    ·
      refine ⟨174651991750744972752370859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116434661167163315168247239 174651991750744972752370859)
      ·
        refine ⟨261977987626117459128556289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174651991750744972752370859 261977987626117459128556289)
        ·
          refine ⟨196483490719588094346417217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261977987626117459128556289 196483490719588094346417217)
          ·
            refine ⟨147362618039691070759812913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196483490719588094346417217 147362618039691070759812913)
            ·
              refine ⟨110521963529768303069859685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147362618039691070759812913 110521963529768303069859685)
              ·
                refine ⟨20722868161831556825598691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110521963529768303069859685 20722868161831556825598691)
                ·
                  refine ⟨31084302242747335238398037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20722868161831556825598691 31084302242747335238398037)
                  ·
                    refine ⟨364269166907195334824977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31084302242747335238398037 364269166907195334824977)
                    ·
                      rfl

theorem cell23_2128235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 8].length) (baseStart_2128235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128235 prefixEnd_2128235 := by exact prefixLift 2128235
  have htrace : WordTrace (prefixWord ++ tailWord_2128235) baseStart_2128235 baseEnd_2128235 := by
    simpa [prefixWord, tailWord_2128235, baseEnd_2128235] using wordTrace_append hprefix tailTrace_2128235
  have hstable : (prefixWord ++ tailWord_2128235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128235).length < 2 ^ (prefixWord ++ tailWord_2128235).sum := by decide
  have hdescent : baseEnd_2128235 < baseStart_2128235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128282 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 9]
def baseStart_2128282 : Nat := 118140960795 + 2128282 * 2 ^ 59
def prefixEnd_2128282 : Nat := 4983230072969 + 3 ^ 40 * 2128282 * 2
def baseEnd_2128282 : Nat := 121425737145816368954135

theorem tailTrace_2128282 : CollatzResearch.WordTrace tailWord_2128282 prefixEnd_2128282 121425737145816368954135 := by
  unfold tailWord_2128282
  simp only [CollatzResearch.WordTrace]
  refine ⟨19406205418901317618114775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51749881117070180314972733 19406205418901317618114775)
  ·
    refine ⟨29109308128351976427172163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19406205418901317618114775 29109308128351976427172163)
    ·
      refine ⟨43663962192527964640758245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29109308128351976427172163 43663962192527964640758245)
      ·
        refine ⟨8186992911098993370142171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43663962192527964640758245 8186992911098993370142171)
        ·
          refine ⟨12280489366648490055213257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8186992911098993370142171 12280489366648490055213257)
          ·
            refine ⟨9210367024986367541409943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12280489366648490055213257 9210367024986367541409943)
            ·
              refine ⟨13815550537479551312114915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9210367024986367541409943 13815550537479551312114915)
              ·
                refine ⟨20723325806219326968172373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13815550537479551312114915 20723325806219326968172373)
                ·
                  refine ⟨121425737145816368954135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20723325806219326968172373 121425737145816368954135)
                  ·
                    rfl

theorem cell23_2128282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_2128282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128282 prefixEnd_2128282 := by exact prefixLift 2128282
  have htrace : WordTrace (prefixWord ++ tailWord_2128282) baseStart_2128282 baseEnd_2128282 := by
    simpa [prefixWord, tailWord_2128282, baseEnd_2128282] using wordTrace_append hprefix tailTrace_2128282
  have hstable : (prefixWord ++ tailWord_2128282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128282).length < 2 ^ (prefixWord ++ tailWord_2128282).sum := by decide
  have hdescent : baseEnd_2128282 < baseStart_2128282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128312 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 4, 5]
def baseStart_2128312 : Nat := 118140960795 + 2128312 * 2 ^ 59
def prefixEnd_2128312 : Nat := 4983230072969 + 3 ^ 40 * 2128312 * 2
def baseEnd_2128312 : Nat := 364282346243994067737359

theorem tailTrace_2128312 : CollatzResearch.WordTrace tailWord_2128312 prefixEnd_2128312 364282346243994067737359 := by
  unfold tailWord_2128312
  simp only [CollatzResearch.WordTrace]
  refine ⟨38812957932748292798025595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51750610576997723730700793 38812957932748292798025595)
  ·
    refine ⟨58219436899122439197038393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38812957932748292798025595 58219436899122439197038393)
    ·
      refine ⟨43664577674341829397778795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58219436899122439197038393 43664577674341829397778795)
      ·
        refine ⟨65496866511512744096668193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43664577674341829397778795 65496866511512744096668193)
        ·
          refine ⟨49122649883634558072501145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65496866511512744096668193 49122649883634558072501145)
          ·
            refine ⟨36841987412725918554375859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49122649883634558072501145 36841987412725918554375859)
            ·
              refine ⟨55262981119088877831563789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36841987412725918554375859 55262981119088877831563789)
              ·
                refine ⟨20723617919658329186836421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55262981119088877831563789 20723617919658329186836421)
                ·
                  refine ⟨3885678359935936722531829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20723617919658329186836421 3885678359935936722531829)
                  ·
                    refine ⟨364282346243994067737359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3885678359935936722531829 364282346243994067737359)
                    ·
                      rfl

theorem cell23_2128312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_2128312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128312 prefixEnd_2128312 := by exact prefixLift 2128312
  have htrace : WordTrace (prefixWord ++ tailWord_2128312) baseStart_2128312 baseEnd_2128312 := by
    simpa [prefixWord, tailWord_2128312, baseEnd_2128312] using wordTrace_append hprefix tailTrace_2128312
  have hstable : (prefixWord ++ tailWord_2128312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128312).length < 2 ^ (prefixWord ++ tailWord_2128312).sum := by decide
  have hdescent : baseEnd_2128312 < baseStart_2128312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128316 : List Nat := [2, 2, 2, 4, 1, 1, 2, 4, 5]
def baseStart_2128316 : Nat := 118140960795 + 2128316 * 2 ^ 59
def prefixEnd_2128316 : Nat := 4983230072969 + 3 ^ 40 * 2128316 * 2
def baseEnd_2128316 : Nat := 121427676961622243062451

theorem tailTrace_2128316 : CollatzResearch.WordTrace tailWord_2128316 prefixEnd_2128316 121427676961622243062451 := by
  unfold tailWord_2128316
  simp only [CollatzResearch.WordTrace]
  refine ⟨38813030878741047139598401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51750707838321396186131201 38813030878741047139598401)
  ·
    refine ⟨29109773159055785354698801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38813030878741047139598401 29109773159055785354698801)
    ·
      refine ⟨21832329869291839016024101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29109773159055785354698801 21832329869291839016024101)
      ·
        refine ⟨4093561850492219815504519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21832329869291839016024101 4093561850492219815504519)
        ·
          refine ⟨6140342775738329723256779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4093561850492219815504519 6140342775738329723256779)
          ·
            refine ⟨9210514163607494584885169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6140342775738329723256779 9210514163607494584885169)
            ·
              refine ⟨6907885622705620938663877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9210514163607494584885169 6907885622705620938663877)
              ·
                refine ⟨1295228554257303925999477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6907885622705620938663877 1295228554257303925999477)
                ·
                  refine ⟨121427676961622243062451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1295228554257303925999477 121427676961622243062451)
                  ·
                    rfl

theorem cell23_2128316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_2128316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128316 prefixEnd_2128316 := by exact prefixLift 2128316
  have htrace : WordTrace (prefixWord ++ tailWord_2128316) baseStart_2128316 baseEnd_2128316 := by
    simpa [prefixWord, tailWord_2128316, baseEnd_2128316] using wordTrace_append hprefix tailTrace_2128316
  have hstable : (prefixWord ++ tailWord_2128316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128316).length < 2 ^ (prefixWord ++ tailWord_2128316).sum := by decide
  have hdescent : baseEnd_2128316 < baseStart_2128316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128349 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2128349 : Nat := 118140960795 + 2128349 * 2 ^ 59
def prefixEnd_2128349 : Nat := 4983230072969 + 3 ^ 40 * 2128349 * 2
def baseEnd_2128349 : Nat := 1092866037516198558449407

theorem tailTrace_2128349 : CollatzResearch.WordTrace tailWord_2128349 prefixEnd_2128349 1092866037516198558449407 := by
  unfold tailWord_2128349
  simp only [CollatzResearch.WordTrace]
  refine ⟨77627265366362540915148101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51751510244241693943432067 77627265366362540915148101)
  ·
    refine ⟨14555112256192976421590269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77627265366362540915148101 14555112256192976421590269)
    ·
      refine ⟨5458167096072366158096351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14555112256192976421590269 5458167096072366158096351)
      ·
        refine ⟨8187250644108549237144527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5458167096072366158096351 8187250644108549237144527)
        ·
          refine ⟨12280875966162823855716791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8187250644108549237144527 12280875966162823855716791)
          ·
            refine ⟨18421313949244235783575187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12280875966162823855716791 18421313949244235783575187)
            ·
              refine ⟨27631970923866353675362781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18421313949244235783575187 27631970923866353675362781)
              ·
                refine ⟨10361989096449882628261043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27631970923866353675362781 10361989096449882628261043)
                ·
                  refine ⟨15542983644674823942391565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10361989096449882628261043 15542983644674823942391565)
                  ·
                    refine ⟨5828618866753058978396837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15542983644674823942391565 5828618866753058978396837)
                    ·
                      refine ⟨1092866037516198558449407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5828618866753058978396837 1092866037516198558449407)
                      ·
                        rfl

theorem cell23_2128349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2128349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128349 prefixEnd_2128349 := by exact prefixLift 2128349
  have htrace : WordTrace (prefixWord ++ tailWord_2128349) baseStart_2128349 baseEnd_2128349 := by
    simpa [prefixWord, tailWord_2128349, baseEnd_2128349] using wordTrace_append hprefix tailTrace_2128349
  have hstable : (prefixWord ++ tailWord_2128349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128349).length < 2 ^ (prefixWord ++ tailWord_2128349).sum := by decide
  have hdescent : baseEnd_2128349 < baseStart_2128349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128366 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_2128366 : Nat := 118140960795 + 2128366 * 2 ^ 59
def prefixEnd_2128366 : Nat := 4983230072969 + 3 ^ 40 * 2128366 * 2
def baseEnd_2128366 : Nat := 1092874766687324991936829

theorem tailTrace_2128366 : CollatzResearch.WordTrace tailWord_2128366 prefixEnd_2128366 1092874766687324991936829 := by
  unfold tailWord_2128366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9703485675912619102314619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51751923604867301879011301 9703485675912619102314619)
  ·
    refine ⟨14555228513868928653471929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9703485675912619102314619 14555228513868928653471929)
    ·
      refine ⟨10916421385401696490103947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14555228513868928653471929 10916421385401696490103947)
      ·
        refine ⟨16374632078102544735155921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10916421385401696490103947 16374632078102544735155921)
        ·
          refine ⟨12280974058576908551366941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16374632078102544735155921 12280974058576908551366941)
          ·
            refine ⟨4605365271966340706762603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12280974058576908551366941 4605365271966340706762603)
            ·
              refine ⟨6908047907949511060143905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4605365271966340706762603 6908047907949511060143905)
              ·
                refine ⟨5181035930962133295107929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6908047907949511060143905 5181035930962133295107929)
                ·
                  refine ⟨3885776948221599971330947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5181035930962133295107929 3885776948221599971330947)
                  ·
                    refine ⟨5828665422332399956996421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3885776948221599971330947 5828665422332399956996421)
                    ·
                      refine ⟨1092874766687324991936829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5828665422332399956996421 1092874766687324991936829)
                      ·
                        rfl

theorem cell23_2128366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_2128366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128366 prefixEnd_2128366 := by exact prefixLift 2128366
  have htrace : WordTrace (prefixWord ++ tailWord_2128366) baseStart_2128366 baseEnd_2128366 := by
    simpa [prefixWord, tailWord_2128366, baseEnd_2128366] using wordTrace_append hprefix tailTrace_2128366
  have hstable : (prefixWord ++ tailWord_2128366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128366).length < 2 ^ (prefixWord ++ tailWord_2128366).sum := by decide
  have hdescent : baseEnd_2128366 < baseStart_2128366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128439 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_2128439 : Nat := 118140960795 + 2128439 * 2 ^ 59
def prefixEnd_2128439 : Nat := 4983230072969 + 3 ^ 40 * 2128439 * 2
def baseEnd_2128439 : Nat := 1092912250775103206323993

theorem tailTrace_2128439 : CollatzResearch.WordTrace tailWord_2128439 prefixEnd_2128439 1092912250775103206323993 := by
  unfold tailWord_2128439
  simp only [CollatzResearch.WordTrace]
  refine ⟨77630547936036486285924371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51753698624024324190616247 77630547936036486285924371)
  ·
    refine ⟨116445821904054729428886557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77630547936036486285924371 116445821904054729428886557)
    ·
      refine ⟨43667183214020523535832459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116445821904054729428886557 43667183214020523535832459)
      ·
        refine ⟨65500774821030785303748689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43667183214020523535832459 65500774821030785303748689)
        ·
          refine ⟨49125581115773088977811517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65500774821030785303748689 49125581115773088977811517)
          ·
            refine ⟨18422092918414908366679319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49125581115773088977811517 18422092918414908366679319)
            ·
              refine ⟨27633139377622362550018979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18422092918414908366679319 27633139377622362550018979)
              ·
                refine ⟨41449709066433543825028469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27633139377622362550018979 41449709066433543825028469)
                ·
                  refine ⟨3885910224978144733596419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41449709066433543825028469 3885910224978144733596419)
                  ·
                    refine ⟨5828865337467217100394629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3885910224978144733596419 5828865337467217100394629)
                    ·
                      refine ⟨1092912250775103206323993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5828865337467217100394629 1092912250775103206323993)
                      ·
                        rfl

theorem cell23_2128439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_2128439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128439 prefixEnd_2128439 := by exact prefixLift 2128439
  have htrace : WordTrace (prefixWord ++ tailWord_2128439) baseStart_2128439 baseEnd_2128439 := by
    simpa [prefixWord, tailWord_2128439, baseEnd_2128439] using wordTrace_append hprefix tailTrace_2128439
  have hstable : (prefixWord ++ tailWord_2128439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128439).length < 2 ^ (prefixWord ++ tailWord_2128439).sum := by decide
  have hdescent : baseEnd_2128439 < baseStart_2128439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128466 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_2128466 : Nat := 118140960795 + 2128466 * 2 ^ 59
def prefixEnd_2128466 : Nat := 4983230072969 + 3 ^ 40 * 2128466 * 2
def baseEnd_2128466 : Nat := 364308704917591533562123

theorem tailTrace_2128466 : CollatzResearch.WordTrace tailWord_2128466 prefixEnd_2128466 364308704917591533562123 := by
  unfold tailWord_2128466
  simp only [CollatzResearch.WordTrace]
  refine ⟨19407883176734667474289313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51754355137959113264771501 19407883176734667474289313)
  ·
    refine ⟨14555912382551000605716985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19407883176734667474289313 14555912382551000605716985)
    ·
      refine ⟨10916934286913250454287739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14555912382551000605716985 10916934286913250454287739)
      ·
        refine ⟨16375401430369875681431609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10916934286913250454287739 16375401430369875681431609)
        ·
          refine ⟨12281551072777406761073707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16375401430369875681431609 12281551072777406761073707)
          ·
            refine ⟨18422326609166110141610561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12281551072777406761073707 18422326609166110141610561)
            ·
              refine ⟨13816744956874582606207921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18422326609166110141610561 13816744956874582606207921)
              ·
                refine ⟨10362558717655936954655941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13816744956874582606207921 10362558717655936954655941)
                ·
                  refine ⟨1942979759560488178997989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10362558717655936954655941 1942979759560488178997989)
                  ·
                    refine ⟨364308704917591533562123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1942979759560488178997989 364308704917591533562123)
                    ·
                      rfl

theorem cell23_2128466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_2128466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128466 prefixEnd_2128466 := by exact prefixLift 2128466
  have htrace : WordTrace (prefixWord ++ tailWord_2128466) baseStart_2128466 baseEnd_2128466 := by
    simpa [prefixWord, tailWord_2128466, baseEnd_2128466] using wordTrace_append hprefix tailTrace_2128466
  have hstable : (prefixWord ++ tailWord_2128466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128466).length < 2 ^ (prefixWord ++ tailWord_2128466).sum := by decide
  have hdescent : baseEnd_2128466 < baseStart_2128466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128490 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_2128490 : Nat := 118140960795 + 2128490 * 2 ^ 59
def prefixEnd_2128490 : Nat := 4983230072969 + 3 ^ 40 * 2128490 * 2
def baseEnd_2128490 : Nat := 1092938438288482506786259

theorem tailTrace_2128490 : CollatzResearch.WordTrace tailWord_2128490 prefixEnd_2128490 1092938438288482506786259 := by
  unfold tailWord_2128490
  simp only [CollatzResearch.WordTrace]
  refine ⟨19408102014712930499007731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51754938705901147997353949 19408102014712930499007731)
  ·
    refine ⟨29112153022069395748511597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19408102014712930499007731 29112153022069395748511597)
    ·
      refine ⟨10917057383276023405691849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29112153022069395748511597 10917057383276023405691849)
      ·
        refine ⟨8187793037457017554268887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10917057383276023405691849 8187793037457017554268887)
        ·
          refine ⟨12281689556185526331403331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8187793037457017554268887 12281689556185526331403331)
          ·
            refine ⟨18422534334278289497104997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12281689556185526331403331 18422534334278289497104997)
            ·
              refine ⟨3454225187677179280707187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18422534334278289497104997 3454225187677179280707187)
              ·
                refine ⟨5181337781515768921060781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454225187677179280707187 5181337781515768921060781)
                ·
                  refine ⟨1943001668068413345397793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5181337781515768921060781 1943001668068413345397793)
                  ·
                    refine ⟨1457251251051310009048345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1943001668068413345397793 1457251251051310009048345)
                    ·
                      refine ⟨1092938438288482506786259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1457251251051310009048345 1092938438288482506786259)
                      ·
                        rfl

theorem cell23_2128490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_2128490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128490 prefixEnd_2128490 := by exact prefixLift 2128490
  have htrace : WordTrace (prefixWord ++ tailWord_2128490) baseStart_2128490 baseEnd_2128490 := by
    simpa [prefixWord, tailWord_2128490, baseEnd_2128490] using wordTrace_append hprefix tailTrace_2128490
  have hstable : (prefixWord ++ tailWord_2128490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128490).length < 2 ^ (prefixWord ++ tailWord_2128490).sum := by decide
  have hdescent : baseEnd_2128490 < baseStart_2128490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128519 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_2128519 : Nat := 118140960795 + 2128519 * 2 ^ 59
def prefixEnd_2128519 : Nat := 4983230072969 + 3 ^ 40 * 2128519 * 2
def baseEnd_2128519 : Nat := 1092953329227462893323625

theorem tailTrace_2128519 : CollatzResearch.WordTrace tailWord_2128519 prefixEnd_2128519 1092953329227462893323625 := by
  unfold tailWord_2128519
  simp only [CollatzResearch.WordTrace]
  refine ⟨77633465775746659948836611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51755643850497773299224407 77633465775746659948836611)
  ·
    refine ⟨116450198663619989923254917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77633465775746659948836611 116450198663619989923254917)
    ·
      refine ⟨21834412249428748110610297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116450198663619989923254917 21834412249428748110610297)
      ·
        refine ⟨16375809187071561082957723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21834412249428748110610297 16375809187071561082957723)
        ·
          refine ⟨24563713780607341624436585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16375809187071561082957723 24563713780607341624436585)
          ·
            refine ⟨18422785335455506218327439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24563713780607341624436585 18422785335455506218327439)
            ·
              refine ⟨27634178003183259327491159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18422785335455506218327439 27634178003183259327491159)
              ·
                refine ⟨41451267004774888991236739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27634178003183259327491159 41451267004774888991236739)
                ·
                  refine ⟨62176900507162333486855109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41451267004774888991236739 62176900507162333486855109)
                  ·
                    refine ⟨11658168845092937528785333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62176900507162333486855109 11658168845092937528785333)
                    ·
                      refine ⟨1092953329227462893323625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11658168845092937528785333 1092953329227462893323625)
                      ·
                        rfl

theorem cell23_2128519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_2128519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128519 prefixEnd_2128519 := by exact prefixLift 2128519
  have htrace : WordTrace (prefixWord ++ tailWord_2128519) baseStart_2128519 baseEnd_2128519 := by
    simpa [prefixWord, tailWord_2128519, baseEnd_2128519] using wordTrace_append hprefix tailTrace_2128519
  have hstable : (prefixWord ++ tailWord_2128519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128519).length < 2 ^ (prefixWord ++ tailWord_2128519).sum := by decide
  have hdescent : baseEnd_2128519 < baseStart_2128519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128549 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_2128549 : Nat := 118140960795 + 2128549 * 2 ^ 59
def prefixEnd_2128549 : Nat := 4983230072969 + 3 ^ 40 * 2128549 * 2
def baseEnd_2128549 : Nat := 1092968733647097775948487

theorem tailTrace_2128549 : CollatzResearch.WordTrace tailWord_2128549 prefixEnd_2128549 1092968733647097775948487 := by
  unfold tailWord_2128549
  simp only [CollatzResearch.WordTrace]
  refine ⟨77634559965637975072428701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51756373310425316714952467 77634559965637975072428701)
  ·
    refine ⟨29112959987114240652160763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77634559965637975072428701 29112959987114240652160763)
    ·
      refine ⟨43669439980671360978241145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29112959987114240652160763 43669439980671360978241145)
      ·
        refine ⟨32752079985503520733680859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43669439980671360978241145 32752079985503520733680859)
        ·
          refine ⟨49128119978255281100521289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32752079985503520733680859 49128119978255281100521289)
          ·
            refine ⟨36846089983691460825390967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49128119978255281100521289 36846089983691460825390967)
            ·
              refine ⟨55269134975537191238086451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36846089983691460825390967 55269134975537191238086451)
              ·
                refine ⟨82903702463305786857129677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55269134975537191238086451 82903702463305786857129677)
                ·
                  refine ⟨31088888423739670071423629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82903702463305786857129677 31088888423739670071423629)
                  ·
                    refine ⟨11658333158902376276783861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31088888423739670071423629 11658333158902376276783861)
                    ·
                      refine ⟨1092968733647097775948487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11658333158902376276783861 1092968733647097775948487)
                      ·
                        rfl

theorem cell23_2128549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_2128549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128549 prefixEnd_2128549 := by exact prefixLift 2128549
  have htrace : WordTrace (prefixWord ++ tailWord_2128549) baseStart_2128549 baseEnd_2128549 := by
    simpa [prefixWord, tailWord_2128549, baseEnd_2128549] using wordTrace_append hprefix tailTrace_2128549
  have hstable : (prefixWord ++ tailWord_2128549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128549).length < 2 ^ (prefixWord ++ tailWord_2128549).sum := by decide
  have hdescent : baseEnd_2128549 < baseStart_2128549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128557 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_2128557 : Nat := 118140960795 + 2128557 * 2 ^ 59
def prefixEnd_2128557 : Nat := 4983230072969 + 3 ^ 40 * 2128557 * 2
def baseEnd_2128557 : Nat := 1092972841492333744648451

theorem tailTrace_2128557 : CollatzResearch.WordTrace tailWord_2128557 prefixEnd_2128557 1092972841492333744648451 := by
  unfold tailWord_2128557
  simp only [CollatzResearch.WordTrace]
  refine ⟨77634851749608992438719925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51756567833072661625813283 77634851749608992438719925)
  ·
    refine ⟨7278267351525843041129993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77634851749608992438719925 7278267351525843041129993)
    ·
      refine ⟨5458700513644382280847495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7278267351525843041129993 5458700513644382280847495)
      ·
        refine ⟨8188050770466573421271243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5458700513644382280847495 8188050770466573421271243)
        ·
          refine ⟨12282076155699860131906865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8188050770466573421271243 12282076155699860131906865)
          ·
            refine ⟨9211557116774895098930149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12282076155699860131906865 9211557116774895098930149)
            ·
              refine ⟨1727166959395292831049403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9211557116774895098930149 1727166959395292831049403)
              ·
                refine ⟨2590750439092939246574105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727166959395292831049403 2590750439092939246574105)
                ·
                  refine ⟨1943062829319704434930579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2590750439092939246574105 1943062829319704434930579)
                  ·
                    refine ⟨2914594243979556652395869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1943062829319704434930579 2914594243979556652395869)
                    ·
                      refine ⟨1092972841492333744648451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2914594243979556652395869 1092972841492333744648451)
                      ·
                        rfl

theorem cell23_2128557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_2128557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128557 prefixEnd_2128557 := by exact prefixLift 2128557
  have htrace : WordTrace (prefixWord ++ tailWord_2128557) baseStart_2128557 baseEnd_2128557 := by
    simpa [prefixWord, tailWord_2128557, baseEnd_2128557] using wordTrace_append hprefix tailTrace_2128557
  have hstable : (prefixWord ++ tailWord_2128557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128557).length < 2 ^ (prefixWord ++ tailWord_2128557).sum := by decide
  have hdescent : baseEnd_2128557 < baseStart_2128557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128567 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 1, 3, 2]
def baseStart_2128567 : Nat := 118140960795 + 2128567 * 2 ^ 59
def prefixEnd_2128567 : Nat := 4983230072969 + 3 ^ 40 * 2128567 * 2
def baseEnd_2128567 : Nat := 1092977976298878705523405

theorem tailTrace_2128567 : CollatzResearch.WordTrace tailWord_2128567 prefixEnd_2128567 1092977976298878705523405 := by
  unfold tailWord_2128567
  simp only [CollatzResearch.WordTrace]
  refine ⟨77635216479572764146583955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51756810986381842764389303 77635216479572764146583955)
  ·
    refine ⟨116452824719359146219875933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77635216479572764146583955 116452824719359146219875933)
    ·
      refine ⟨43669809269759679832453475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116452824719359146219875933 43669809269759679832453475)
      ·
        refine ⟨65504713904639519748680213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43669809269759679832453475 65504713904639519748680213)
        ·
          refine ⟨3070533464279977488219385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65504713904639519748680213 3070533464279977488219385)
          ·
            refine ⟨2302900098209983116164539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3070533464279977488219385 2302900098209983116164539)
            ·
              refine ⟨3454350147314974674246809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2302900098209983116164539 3454350147314974674246809)
              ·
                refine ⟨2590762610486231005685107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3454350147314974674246809 2590762610486231005685107)
                ·
                  refine ⟨3886143915729346508527661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2590762610486231005685107 3886143915729346508527661)
                  ·
                    refine ⟨1457303968398504940697873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3886143915729346508527661 1457303968398504940697873)
                    ·
                      refine ⟨1092977976298878705523405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1457303968398504940697873 1092977976298878705523405)
                      ·
                        rfl

theorem cell23_2128567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 3, 2].length) (baseStart_2128567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128567 prefixEnd_2128567 := by exact prefixLift 2128567
  have htrace : WordTrace (prefixWord ++ tailWord_2128567) baseStart_2128567 baseEnd_2128567 := by
    simpa [prefixWord, tailWord_2128567, baseEnd_2128567] using wordTrace_append hprefix tailTrace_2128567
  have hstable : (prefixWord ++ tailWord_2128567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128567).length < 2 ^ (prefixWord ++ tailWord_2128567).sum := by decide
  have hdescent : baseEnd_2128567 < baseStart_2128567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128569 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 9]
def baseStart_2128569 : Nat := 118140960795 + 2128569 * 2 ^ 59
def prefixEnd_2128569 : Nat := 4983230072969 + 3 ^ 40 * 2128569 * 2
def baseEnd_2128569 : Nat := 121442111473354188633155

theorem tailTrace_2128569 : CollatzResearch.WordTrace tailWord_2128569 prefixEnd_2128569 121442111473354188633155 := by
  unfold tailWord_2128569
  simp only [CollatzResearch.WordTrace]
  refine ⟨77635289425565518488156761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51756859617043678992104507 77635289425565518488156761)
  ·
    refine ⟨58226467069174138866117571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77635289425565518488156761 58226467069174138866117571)
    ·
      refine ⟨87339700603761208299176357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58226467069174138866117571 87339700603761208299176357)
      ·
        refine ⟨16376193863205226556095567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87339700603761208299176357 16376193863205226556095567)
        ·
          refine ⟨24564290794807839834143351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16376193863205226556095567 24564290794807839834143351)
          ·
            refine ⟨36846436192211759751215027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24564290794807839834143351 36846436192211759751215027)
            ·
              refine ⟨55269654288317639626822541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36846436192211759751215027 55269654288317639626822541)
              ·
                refine ⟨20726120358119114860058453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55269654288317639626822541 20726120358119114860058453)
                ·
                  refine ⟨121442111473354188633155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 20726120358119114860058453 121442111473354188633155)
                  ·
                    rfl

theorem cell23_2128569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 9].length) (baseStart_2128569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128569 prefixEnd_2128569 := by exact prefixLift 2128569
  have htrace : WordTrace (prefixWord ++ tailWord_2128569) baseStart_2128569 baseEnd_2128569 := by
    simpa [prefixWord, tailWord_2128569, baseEnd_2128569] using wordTrace_append hprefix tailTrace_2128569
  have hstable : (prefixWord ++ tailWord_2128569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128569).length < 2 ^ (prefixWord ++ tailWord_2128569).sum := by decide
  have hdescent : baseEnd_2128569 < baseStart_2128569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128580 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_2128580 : Nat := 118140960795 + 2128580 * 2 ^ 59
def prefixEnd_2128580 : Nat := 4983230072969 + 3 ^ 40 * 2128580 * 2
def baseEnd_2128580 : Nat := 1092984651547387154660845

theorem tailTrace_2128580 : CollatzResearch.WordTrace tailWord_2128580 prefixEnd_2128580 1092984651547387154660845 := by
  unfold tailWord_2128580
  simp only [CollatzResearch.WordTrace]
  refine ⟨38817845314262833683403597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51757127085683778244538129 38817845314262833683403597)
  ·
    refine ⟨14556691992848562631276349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38817845314262833683403597 14556691992848562631276349)
    ·
      refine ⟨5458759497318210986728631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14556691992848562631276349 5458759497318210986728631)
      ·
        refine ⟨8188139245977316480092947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5458759497318210986728631 8188139245977316480092947)
        ·
          refine ⟨12282208868965974720139421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8188139245977316480092947 12282208868965974720139421)
          ·
            refine ⟨4605828325862240520052283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12282208868965974720139421 4605828325862240520052283)
            ·
              refine ⟨6908742488793360780078425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4605828325862240520052283 6908742488793360780078425)
              ·
                refine ⟨5181556866595020585058819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6908742488793360780078425 5181556866595020585058819)
                ·
                  refine ⟨7772335299892530877588229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5181556866595020585058819 7772335299892530877588229)
                  ·
                    refine ⟨1457312868729849539547793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7772335299892530877588229 1457312868729849539547793)
                    ·
                      refine ⟨1092984651547387154660845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1457312868729849539547793 1092984651547387154660845)
                      ·
                        rfl

theorem cell23_2128580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_2128580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128580 prefixEnd_2128580 := by exact prefixLift 2128580
  have htrace : WordTrace (prefixWord ++ tailWord_2128580) baseStart_2128580 baseEnd_2128580 := by
    simpa [prefixWord, tailWord_2128580, baseEnd_2128580] using wordTrace_append hprefix tailTrace_2128580
  have hstable : (prefixWord ++ tailWord_2128580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128580).length < 2 ^ (prefixWord ++ tailWord_2128580).sum := by decide
  have hdescent : baseEnd_2128580 < baseStart_2128580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128613 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 2, 3, 3]
def baseStart_2128613 : Nat := 118140960795 + 2128613 * 2 ^ 59
def prefixEnd_2128613 : Nat := 4983230072969 + 3 ^ 40 * 2128613 * 2
def baseEnd_2128613 : Nat := 1093001596408985525548193

theorem tailTrace_2128613 : CollatzResearch.WordTrace tailWord_2128613 prefixEnd_2128613 1093001596408985525548193 := by
  unfold tailWord_2128613
  simp only [CollatzResearch.WordTrace]
  refine ⟨77636894237406114002758493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51757929491604076001838995 77636894237406114002758493)
  ·
    refine ⟨29113835339027292751034435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77636894237406114002758493 29113835339027292751034435)
    ·
      refine ⟨43670753008540939126551653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29113835339027292751034435 43670753008540939126551653)
      ·
        refine ⟨8188266189101426086228435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43670753008540939126551653 8188266189101426086228435)
        ·
          refine ⟨12282399283652139129342653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8188266189101426086228435 12282399283652139129342653)
          ·
            refine ⟨4605899731369552173503495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12282399283652139129342653 4605899731369552173503495)
            ·
              refine ⟨6908849597054328260255243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4605899731369552173503495 6908849597054328260255243)
              ·
                refine ⟨10363274395581492390382865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6908849597054328260255243 10363274395581492390382865)
                ·
                  refine ⟨7772455796686119292787149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10363274395581492390382865 7772455796686119292787149)
                  ·
                    refine ⟨2914670923757294734795181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7772455796686119292787149 2914670923757294734795181)
                    ·
                      refine ⟨1093001596408985525548193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2914670923757294734795181 1093001596408985525548193)
                      ·
                        rfl

theorem cell23_2128613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_2128613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128613 prefixEnd_2128613 := by exact prefixLift 2128613
  have htrace : WordTrace (prefixWord ++ tailWord_2128613) baseStart_2128613 baseEnd_2128613 := by
    simpa [prefixWord, tailWord_2128613, baseEnd_2128613] using wordTrace_append hprefix tailTrace_2128613
  have hstable : (prefixWord ++ tailWord_2128613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128613).length < 2 ^ (prefixWord ++ tailWord_2128613).sum := by decide
  have hdescent : baseEnd_2128613 < baseStart_2128613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128666 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_2128666 : Nat := 118140960795 + 2128666 * 2 ^ 59
def prefixEnd_2128666 : Nat := 4983230072969 + 3 ^ 40 * 2128666 * 2
def baseEnd_2128666 : Nat := 1093028810883673818185449

theorem tailTrace_2128666 : CollatzResearch.WordTrace tailWord_2128666 prefixEnd_2128666 1093028810883673818185449 := by
  unfold tailWord_2128666
  simp only [CollatzResearch.WordTrace]
  refine ⟨19409706826553526013609463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51759218204142736036291901 19409706826553526013609463)
  ·
    refine ⟨29114560239830289020414195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19409706826553526013609463 29114560239830289020414195)
    ·
      refine ⟨43671840359745433530621293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29114560239830289020414195 43671840359745433530621293)
      ·
        refine ⟨16376940134904537573982985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43671840359745433530621293 16376940134904537573982985)
        ·
          refine ⟨12282705101178403180487239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16376940134904537573982985 12282705101178403180487239)
          ·
            refine ⟨18424057651767604770730859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12282705101178403180487239 18424057651767604770730859)
            ·
              refine ⟨27636086477651407156096289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18424057651767604770730859 27636086477651407156096289)
              ·
                refine ⟨20727064858238555367072217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27636086477651407156096289 20727064858238555367072217)
                ·
                  refine ⟨15545298643678916525304163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20727064858238555367072217 15545298643678916525304163)
                  ·
                    refine ⟨23317947965518374787956245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15545298643678916525304163 23317947965518374787956245)
                    ·
                      refine ⟨1093028810883673818185449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23317947965518374787956245 1093028810883673818185449)
                      ·
                        rfl

theorem cell23_2128666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_2128666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128666 prefixEnd_2128666 := by exact prefixLift 2128666
  have htrace : WordTrace (prefixWord ++ tailWord_2128666) baseStart_2128666 baseEnd_2128666 := by
    simpa [prefixWord, tailWord_2128666, baseEnd_2128666] using wordTrace_append hprefix tailTrace_2128666
  have hstable : (prefixWord ++ tailWord_2128666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128666).length < 2 ^ (prefixWord ++ tailWord_2128666).sum := by decide
  have hdescent : baseEnd_2128666 < baseStart_2128666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128720 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 3, 1, 3]
def baseStart_2128720 : Nat := 118140960795 + 2128720 * 2 ^ 59
def prefixEnd_2128720 : Nat := 4983230072969 + 3 ^ 40 * 2128720 * 2
def baseEnd_2128720 : Nat := 1093056538839016606910201

theorem tailTrace_2128720 : CollatzResearch.WordTrace tailWord_2128720 prefixEnd_2128720 1093056538839016606910201 := by
  unfold tailWord_2128720
  simp only [CollatzResearch.WordTrace]
  refine ⟨38820398424009235638451807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51760531232012314184602409 38820398424009235638451807)
  ·
    refine ⟨58230597636013853457677711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38820398424009235638451807 58230597636013853457677711)
    ·
      refine ⟨87345896454020780186516567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58230597636013853457677711 87345896454020780186516567)
      ·
        refine ⟨131018844681031170279774851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87345896454020780186516567 131018844681031170279774851)
        ·
          refine ⟨196528267021546755419662277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131018844681031170279774851 196528267021546755419662277)
          ·
            refine ⟨36849050066540016641186677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 196528267021546755419662277 36849050066540016641186677)
            ·
              refine ⟨3454598443738126560111251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36849050066540016641186677 3454598443738126560111251)
              ·
                refine ⟨5181897665607189840166877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454598443738126560111251 5181897665607189840166877)
                ·
                  refine ⟨1943211624602696190062579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5181897665607189840166877 1943211624602696190062579)
                  ·
                    refine ⟨2914817436904044285093869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1943211624602696190062579 2914817436904044285093869)
                    ·
                      refine ⟨1093056538839016606910201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2914817436904044285093869 1093056538839016606910201)
                      ·
                        rfl

theorem cell23_2128720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3, 1, 3].length) (baseStart_2128720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128720 prefixEnd_2128720 := by exact prefixLift 2128720
  have htrace : WordTrace (prefixWord ++ tailWord_2128720) baseStart_2128720 baseEnd_2128720 := by
    simpa [prefixWord, tailWord_2128720, baseEnd_2128720] using wordTrace_append hprefix tailTrace_2128720
  have hstable : (prefixWord ++ tailWord_2128720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128720).length < 2 ^ (prefixWord ++ tailWord_2128720).sum := by decide
  have hdescent : baseEnd_2128720 < baseStart_2128720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128740 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_2128740 : Nat := 118140960795 + 2128740 * 2 ^ 59
def prefixEnd_2128740 : Nat := 4983230072969 + 3 ^ 40 * 2128740 * 2
def baseEnd_2128740 : Nat := 364355602817368842886703

theorem tailTrace_2128740 : CollatzResearch.WordTrace tailWord_2128740 prefixEnd_2128740 364355602817368842886703 := by
  unfold tailWord_2128740
  simp only [CollatzResearch.WordTrace]
  refine ⟨38820763153973007346315837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51761017538630676461754449 38820763153973007346315837)
  ·
    refine ⟨14557786182739877754868439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38820763153973007346315837 14557786182739877754868439)
    ·
      refine ⟨21836679274109816632302659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14557786182739877754868439 21836679274109816632302659)
      ·
        refine ⟨32755018911164724948453989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21836679274109816632302659 32755018911164724948453989)
        ·
          refine ⟨6141566045843385927835123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32755018911164724948453989 6141566045843385927835123)
          ·
            refine ⟨9212349068765078891752685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6141566045843385927835123 9212349068765078891752685)
            ·
              refine ⟨3454630900786904584407257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9212349068765078891752685 3454630900786904584407257)
              ·
                refine ⟨2590973175590178438305443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3454630900786904584407257 2590973175590178438305443)
                ·
                  refine ⟨3886459763385267657458165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2590973175590178438305443 3886459763385267657458165)
                  ·
                    refine ⟨364355602817368842886703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3886459763385267657458165 364355602817368842886703)
                    ·
                      rfl

theorem cell23_2128740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_2128740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128740 prefixEnd_2128740 := by exact prefixLift 2128740
  have htrace : WordTrace (prefixWord ++ tailWord_2128740) baseStart_2128740 baseEnd_2128740 := by
    simpa [prefixWord, tailWord_2128740, baseEnd_2128740] using wordTrace_append hprefix tailTrace_2128740
  have hstable : (prefixWord ++ tailWord_2128740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128740).length < 2 ^ (prefixWord ++ tailWord_2128740).sum := by decide
  have hdescent : baseEnd_2128740 < baseStart_2128740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128753 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 1, 6]
def baseStart_2128753 : Nat := 118140960795 + 2128753 * 2 ^ 59
def prefixEnd_2128753 : Nat := 4983230072969 + 3 ^ 40 * 2128753 * 2
def baseEnd_2128753 : Nat := 364357827900204992599183

theorem tailTrace_2128753 : CollatzResearch.WordTrace tailWord_2128753 prefixEnd_2128753 364357827900204992599183 := by
  unfold tailWord_2128753
  simp only [CollatzResearch.WordTrace]
  refine ⟨77642000456898917912854913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51761333637932611941903275 77642000456898917912854913)
  ·
    refine ⟨58231500342674188434641185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77642000456898917912854913 58231500342674188434641185)
    ·
      refine ⟨43673625257005641325980889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58231500342674188434641185 43673625257005641325980889)
      ·
        refine ⟨32755218942754230994485667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43673625257005641325980889 32755218942754230994485667)
        ·
          refine ⟨49132828414131346491728501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32755218942754230994485667 49132828414131346491728501)
          ·
            refine ⟨4606202663824813733599547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49132828414131346491728501 4606202663824813733599547)
            ·
              refine ⟨6909303995737220600399321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4606202663824813733599547 6909303995737220600399321)
              ·
                refine ⟨5181977996802915450299491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6909303995737220600399321 5181977996802915450299491)
                ·
                  refine ⟨7772966995204373175449237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5181977996802915450299491 7772966995204373175449237)
                  ·
                    refine ⟨364357827900204992599183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7772966995204373175449237 364357827900204992599183)
                    ·
                      rfl

theorem cell23_2128753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_2128753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128753 prefixEnd_2128753 := by exact prefixLift 2128753
  have htrace : WordTrace (prefixWord ++ tailWord_2128753) baseStart_2128753 baseEnd_2128753 := by
    simpa [prefixWord, tailWord_2128753, baseEnd_2128753] using wordTrace_append hprefix tailTrace_2128753
  have hstable : (prefixWord ++ tailWord_2128753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128753).length < 2 ^ (prefixWord ++ tailWord_2128753).sum := by decide
  have hdescent : baseEnd_2128753 < baseStart_2128753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128757 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2128757 : Nat := 118140960795 + 2128757 * 2 ^ 59
def prefixEnd_2128757 : Nat := 4983230072969 + 3 ^ 40 * 2128757 * 2
def baseEnd_2128757 : Nat := 364358512541077654049177

theorem tailTrace_2128757 : CollatzResearch.WordTrace tailWord_2128757 prefixEnd_2128757 364358512541077654049177 := by
  unfold tailWord_2128757
  simp only [CollatzResearch.WordTrace]
  refine ⟨77642146348884426596000525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51761430899256284397333683 77642146348884426596000525)
  ·
    refine ⟨29115804880831659973500197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77642146348884426596000525 29115804880831659973500197)
    ·
      refine ⟨5459213415155936245031287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29115804880831659973500197 5459213415155936245031287)
      ·
        refine ⟨8188820122733904367546931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5459213415155936245031287 8188820122733904367546931)
        ·
          refine ⟨12283230184100856551320397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8188820122733904367546931 12283230184100856551320397)
          ·
            refine ⟨4606211319037821206745149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12283230184100856551320397 4606211319037821206745149)
            ·
              refine ⟨1727329244639182952529431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4606211319037821206745149 1727329244639182952529431)
              ·
                refine ⟨2590993866958774428794147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727329244639182952529431 2590993866958774428794147)
                ·
                  refine ⟨3886490800438161643191221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2590993866958774428794147 3886490800438161643191221)
                  ·
                    refine ⟨364358512541077654049177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3886490800438161643191221 364358512541077654049177)
                    ·
                      rfl

theorem cell23_2128757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2128757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128757 prefixEnd_2128757 := by exact prefixLift 2128757
  have htrace : WordTrace (prefixWord ++ tailWord_2128757) baseStart_2128757 baseEnd_2128757 := by
    simpa [prefixWord, tailWord_2128757, baseEnd_2128757] using wordTrace_append hprefix tailTrace_2128757
  have hstable : (prefixWord ++ tailWord_2128757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128757).length < 2 ^ (prefixWord ++ tailWord_2128757).sum := by decide
  have hdescent : baseEnd_2128757 < baseStart_2128757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128760 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 7, 2, 2]
def baseStart_2128760 : Nat := 118140960795 + 2128760 * 2 ^ 59
def prefixEnd_2128760 : Nat := 4983230072969 + 3 ^ 40 * 2128760 * 2
def baseEnd_2128760 : Nat := 1093077078065196450410017

theorem tailTrace_2128760 : CollatzResearch.WordTrace tailWord_2128760 prefixEnd_2128760 1093077078065196450410017 := by
  unfold tailWord_2128760
  simp only [CollatzResearch.WordTrace]
  refine ⟨38821127883936779054179867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51761503845249038738906489 38821127883936779054179867)
  ·
    refine ⟨58231691825905168581269801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38821127883936779054179867 58231691825905168581269801)
    ·
      refine ⟨43673768869428876435952351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58231691825905168581269801 43673768869428876435952351)
      ·
        refine ⟨65510653304143314653928527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43673768869428876435952351 65510653304143314653928527)
        ·
          refine ⟨98265979956214971980892791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65510653304143314653928527 98265979956214971980892791)
          ·
            refine ⟨147398969934322457971339187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98265979956214971980892791 147398969934322457971339187)
            ·
              refine ⟨221098454901483686957008781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147398969934322457971339187 221098454901483686957008781)
              ·
                refine ⟨82911920588056382608878293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221098454901483686957008781 82911920588056382608878293)
                ·
                  refine ⟨1943248138782571467395585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 82911920588056382608878293 1943248138782571467395585)
                  ·
                    refine ⟨1457436104086928600546689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1943248138782571467395585 1457436104086928600546689)
                    ·
                      refine ⟨1093077078065196450410017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1457436104086928600546689 1093077078065196450410017)
                      ·
                        rfl

theorem cell23_2128760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 7, 2, 2].length) (baseStart_2128760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128760 prefixEnd_2128760 := by exact prefixLift 2128760
  have htrace : WordTrace (prefixWord ++ tailWord_2128760) baseStart_2128760 baseEnd_2128760 := by
    simpa [prefixWord, tailWord_2128760, baseEnd_2128760] using wordTrace_append hprefix tailTrace_2128760
  have hstable : (prefixWord ++ tailWord_2128760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128760).length < 2 ^ (prefixWord ++ tailWord_2128760).sum := by decide
  have hdescent : baseEnd_2128760 < baseStart_2128760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128763 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 5]
def baseStart_2128763 : Nat := 118140960795 + 2128763 * 2 ^ 59
def prefixEnd_2128763 : Nat := 4983230072969 + 3 ^ 40 * 2128763 * 2
def baseEnd_2128763 : Nat := 1093078618507159938672503

theorem tailTrace_2128763 : CollatzResearch.WordTrace tailWord_2128763 prefixEnd_2128763 1093078618507159938672503 := by
  unfold tailWord_2128763
  simp only [CollatzResearch.WordTrace]
  refine ⟨77642365186862689620718943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51761576791241793080479295 77642365186862689620718943)
  ·
    refine ⟨116463547780294034431078415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77642365186862689620718943 116463547780294034431078415)
    ·
      refine ⟨174695321670441051646617623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116463547780294034431078415 174695321670441051646617623)
      ·
        refine ⟨262042982505661577469926435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174695321670441051646617623 262042982505661577469926435)
        ·
          refine ⟨393064473758492366204889653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262042982505661577469926435 393064473758492366204889653)
          ·
            refine ⟨36849794414858659331708405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 393064473758492366204889653 36849794414858659331708405)
            ·
              refine ⟨3454668226392999312347663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36849794414858659331708405 3454668226392999312347663)
              ·
                refine ⟨5182002339589498968521495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454668226392999312347663 5182002339589498968521495)
                ·
                  refine ⟨7773003509384248452782243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5182002339589498968521495 7773003509384248452782243)
                  ·
                    refine ⟨11659505264076372679173365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7773003509384248452782243 11659505264076372679173365)
                    ·
                      refine ⟨1093078618507159938672503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11659505264076372679173365 1093078618507159938672503)
                      ·
                        rfl

theorem cell23_2128763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 5].length) (baseStart_2128763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128763 prefixEnd_2128763 := by exact prefixLift 2128763
  have htrace : WordTrace (prefixWord ++ tailWord_2128763) baseStart_2128763 baseEnd_2128763 := by
    simpa [prefixWord, tailWord_2128763, baseEnd_2128763] using wordTrace_append hprefix tailTrace_2128763
  have hstable : (prefixWord ++ tailWord_2128763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128763).length < 2 ^ (prefixWord ++ tailWord_2128763).sum := by decide
  have hdescent : baseEnd_2128763 < baseStart_2128763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128794 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2]
def baseStart_2128794 : Nat := 118140960795 + 2128794 * 2 ^ 59
def prefixEnd_2128794 : Nat := 4983230072969 + 3 ^ 40 * 2128794 * 2
def baseEnd_2128794 : Nat := 1093094536407449317384861

theorem tailTrace_2128794 : CollatzResearch.WordTrace tailWord_2128794 prefixEnd_2128794 1093094536407449317384861 := by
  unfold tailWord_2128794
  simp only [CollatzResearch.WordTrace]
  refine ⟨19410873962437595478774359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51762330566500254610064957 19410873962437595478774359)
  ·
    refine ⟨29116310943656393218161539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19410873962437595478774359 29116310943656393218161539)
    ·
      refine ⟨43674466415484589827242309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29116310943656393218161539 43674466415484589827242309)
      ·
        refine ⟨8188962452903360592607933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43674466415484589827242309 8188962452903360592607933)
        ·
          refine ⟨3070860919838760222227975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8188962452903360592607933 3070860919838760222227975)
          ·
            refine ⟨4606291379758140333341963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3070860919838760222227975 4606291379758140333341963)
            ·
              refine ⟨6909437069637210500012945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4606291379758140333341963 6909437069637210500012945)
              ·
                refine ⟨5182077802227907875009709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6909437069637210500012945 5182077802227907875009709)
                ·
                  refine ⟨1943279175835465453128641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5182077802227907875009709 1943279175835465453128641)
                  ·
                    refine ⟨1457459381876599089846481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1943279175835465453128641 1457459381876599089846481)
                    ·
                      refine ⟨1093094536407449317384861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1457459381876599089846481 1093094536407449317384861)
                      ·
                        rfl

theorem cell23_2128794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_2128794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128794 prefixEnd_2128794 := by exact prefixLift 2128794
  have htrace : WordTrace (prefixWord ++ tailWord_2128794) baseStart_2128794 baseEnd_2128794 := by
    simpa [prefixWord, tailWord_2128794, baseEnd_2128794] using wordTrace_append hprefix tailTrace_2128794
  have hstable : (prefixWord ++ tailWord_2128794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128794).length < 2 ^ (prefixWord ++ tailWord_2128794).sum := by decide
  have hdescent : baseEnd_2128794 < baseStart_2128794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128838 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2128838 : Nat := 118140960795 + 2128838 * 2 ^ 59
def prefixEnd_2128838 : Nat := 4983230072969 + 3 ^ 40 * 2128838 * 2
def baseEnd_2128838 : Nat := 364372376518749048411553

theorem tailTrace_2128838 : CollatzResearch.WordTrace tailWord_2128838 prefixEnd_2128838 364372376518749048411553 := by
  unfold tailWord_2128838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2426409395674718044678099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51763400441060651619799445 2426409395674718044678099)
  ·
    refine ⟨3639614093512077067017149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2426409395674718044678099 3639614093512077067017149)
    ·
      refine ⟨1364855285067028900131431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3639614093512077067017149 1364855285067028900131431)
      ·
        refine ⟨2047282927600543350197147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364855285067028900131431 2047282927600543350197147)
        ·
          refine ⟨3070924391400815025295721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047282927600543350197147 3070924391400815025295721)
          ·
            refine ⟨2303193293550611268971791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3070924391400815025295721 2303193293550611268971791)
            ·
              refine ⟨3454789940325916903457687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303193293550611268971791 3454789940325916903457687)
              ·
                refine ⟨5182184910488875355186531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3454789940325916903457687 5182184910488875355186531)
                ·
                  refine ⟨7773277365733313032779797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5182184910488875355186531 7773277365733313032779797)
                  ·
                    refine ⟨364372376518749048411553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7773277365733313032779797 364372376518749048411553)
                    ·
                      rfl

theorem cell23_2128838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2128838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128838 prefixEnd_2128838 := by exact prefixLift 2128838
  have htrace : WordTrace (prefixWord ++ tailWord_2128838) baseStart_2128838 baseEnd_2128838 := by
    simpa [prefixWord, tailWord_2128838, baseEnd_2128838] using wordTrace_append hprefix tailTrace_2128838
  have hstable : (prefixWord ++ tailWord_2128838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128838).length < 2 ^ (prefixWord ++ tailWord_2128838).sum := by decide
  have hdescent : baseEnd_2128838 < baseStart_2128838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128843 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 2, 6]
def baseStart_2128843 : Nat := 118140960795 + 2128843 * 2 ^ 59
def prefixEnd_2128843 : Nat := 4983230072969 + 3 ^ 40 * 2128843 * 2
def baseEnd_2128843 : Nat := 364373232319839875224045

theorem tailTrace_2128843 : CollatzResearch.WordTrace tailWord_2128843 prefixEnd_2128843 364373232319839875224045 := by
  unfold tailWord_2128843
  simp only [CollatzResearch.WordTrace]
  refine ⟨77645283026572863283631183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51763522017715242189087455 77645283026572863283631183)
  ·
    refine ⟨116467924539859294925446775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77645283026572863283631183 116467924539859294925446775)
    ·
      refine ⟨174701886809788942388170163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116467924539859294925446775 174701886809788942388170163)
      ·
        refine ⟨262052830214683413582255245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174701886809788942388170163 262052830214683413582255245)
        ·
          refine ⟨98269811330506280093345717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262052830214683413582255245 98269811330506280093345717)
          ·
            refine ⟨9212794812234963758751161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 98269811330506280093345717 9212794812234963758751161)
            ·
              refine ⟨6909596109176222819063371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9212794812234963758751161 6909596109176222819063371)
              ·
                refine ⟨10364394163764334228595057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6909596109176222819063371 10364394163764334228595057)
                ·
                  refine ⟨7773295622823250671446293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10364394163764334228595057 7773295622823250671446293)
                  ·
                    refine ⟨364373232319839875224045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7773295622823250671446293 364373232319839875224045)
                    ·
                      rfl

theorem cell23_2128843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 6].length) (baseStart_2128843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128843 prefixEnd_2128843 := by exact prefixLift 2128843
  have htrace : WordTrace (prefixWord ++ tailWord_2128843) baseStart_2128843 baseEnd_2128843 := by
    simpa [prefixWord, tailWord_2128843, baseEnd_2128843] using wordTrace_append hprefix tailTrace_2128843
  have hstable : (prefixWord ++ tailWord_2128843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128843).length < 2 ^ (prefixWord ++ tailWord_2128843).sum := by decide
  have hdescent : baseEnd_2128843 < baseStart_2128843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128844 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 2, 1, 3]
def baseStart_2128844 : Nat := 118140960795 + 2128844 * 2 ^ 59
def prefixEnd_2128844 : Nat := 4983230072969 + 3 ^ 40 * 2128844 * 2
def baseEnd_2128844 : Nat := 1093120210440174121759631

theorem tailTrace_2128844 : CollatzResearch.WordTrace tailWord_2128844 prefixEnd_2128844 1093120210440174121759631 := by
  unfold tailWord_2128844
  simp only [CollatzResearch.WordTrace]
  refine ⟨38822659749784620227208793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51763546333046160302945057 38822659749784620227208793)
  ·
    refine ⟨29116994812338465170406595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38822659749784620227208793 29116994812338465170406595)
    ·
      refine ⟨43675492218507697755609893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29116994812338465170406595 43675492218507697755609893)
      ·
        refine ⟨8189154790970193329176855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43675492218507697755609893 8189154790970193329176855)
        ·
          refine ⟨12283732186455289993765283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8189154790970193329176855 12283732186455289993765283)
          ·
            refine ⟨18425598279682934990647925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12283732186455289993765283 18425598279682934990647925)
            ·
              refine ⟨1727399838720275155373243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18425598279682934990647925 1727399838720275155373243)
              ·
                refine ⟨2591099758080412733059865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727399838720275155373243 2591099758080412733059865)
                ·
                  refine ⟨1943324818560309549794899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2591099758080412733059865 1943324818560309549794899)
                  ·
                    refine ⟨2914987227840464324692349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1943324818560309549794899 2914987227840464324692349)
                    ·
                      refine ⟨1093120210440174121759631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2914987227840464324692349 1093120210440174121759631)
                      ·
                        rfl

theorem cell23_2128844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_2128844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128844 prefixEnd_2128844 := by exact prefixLift 2128844
  have htrace : WordTrace (prefixWord ++ tailWord_2128844) baseStart_2128844 baseEnd_2128844 := by
    simpa [prefixWord, tailWord_2128844, baseEnd_2128844] using wordTrace_append hprefix tailTrace_2128844
  have hstable : (prefixWord ++ tailWord_2128844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128844).length < 2 ^ (prefixWord ++ tailWord_2128844).sum := by decide
  have hdescent : baseEnd_2128844 < baseStart_2128844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128867 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 6, 2, 2]
def baseStart_2128867 : Nat := 118140960795 + 2128867 * 2 ^ 59
def prefixEnd_2128867 : Nat := 4983230072969 + 3 ^ 40 * 2128867 * 2
def baseEnd_2128867 : Nat := 1093132020495227531772025

theorem tailTrace_2128867 : CollatzResearch.WordTrace tailWord_2128867 prefixEnd_2128867 1093132020495227531772025 := by
  unfold tailWord_2128867
  simp only [CollatzResearch.WordTrace]
  refine ⟨77646158378485915382504855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51764105585657276921669903 77646158378485915382504855)
  ·
    refine ⟨116469237567728873073757283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77646158378485915382504855 116469237567728873073757283)
    ·
      refine ⟨174703856351593309610635925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116469237567728873073757283 174703856351593309610635925)
      ·
        refine ⟨8189243266480936387998559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 174703856351593309610635925 8189243266480936387998559)
        ·
          refine ⟨12283864899721404581997839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8189243266480936387998559 12283864899721404581997839)
          ·
            refine ⟨18425797349582106872996759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12283864899721404581997839 18425797349582106872996759)
            ·
              refine ⟨27638696024373160309495139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18425797349582106872996759 27638696024373160309495139)
              ·
                refine ⟨41458044036559740464242709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27638696024373160309495139 41458044036559740464242709)
                ·
                  refine ⟨1943345814213737834261377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41458044036559740464242709 1943345814213737834261377)
                  ·
                    refine ⟨1457509360660303375696033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1943345814213737834261377 1457509360660303375696033)
                    ·
                      refine ⟨1093132020495227531772025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1457509360660303375696033 1093132020495227531772025)
                      ·
                        rfl

theorem cell23_2128867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_2128867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128867 prefixEnd_2128867 := by exact prefixLift 2128867
  have htrace : WordTrace (prefixWord ++ tailWord_2128867) baseStart_2128867 baseEnd_2128867 := by
    simpa [prefixWord, tailWord_2128867, baseEnd_2128867] using wordTrace_append hprefix tailTrace_2128867
  have hstable : (prefixWord ++ tailWord_2128867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128867).length < 2 ^ (prefixWord ++ tailWord_2128867).sum := by decide
  have hdescent : baseEnd_2128867 < baseStart_2128867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128890 : List Nat := [3, 1, 1, 1, 1, 2, 1, 8, 5]
def baseStart_2128890 : Nat := 118140960795 + 2128890 * 2 ^ 59
def prefixEnd_2128890 : Nat := 4983230072969 + 3 ^ 40 * 2128890 * 2
def baseEnd_2128890 : Nat := 121460425616697882420491

theorem tailTrace_2128890 : CollatzResearch.WordTrace tailWord_2128890 prefixEnd_2128890 121460425616697882420491 := by
  unfold tailWord_2128890
  simp only [CollatzResearch.WordTrace]
  refine ⟨19411749314350647577648031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51764664838268393540394749 19411749314350647577648031)
  ·
    refine ⟨29117623971525971366472047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19411749314350647577648031 29117623971525971366472047)
    ·
      refine ⟨43676435957288957049708071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29117623971525971366472047 43676435957288957049708071)
      ·
        refine ⟨65514653935933435574562107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43676435957288957049708071 65514653935933435574562107)
        ·
          refine ⟨98271980903900153361843161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65514653935933435574562107 98271980903900153361843161)
          ·
            refine ⟨73703985677925115021382371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98271980903900153361843161 73703985677925115021382371)
            ·
              refine ⟨110555978516887672532073557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73703985677925115021382371 110555978516887672532073557)
              ·
                refine ⟨1295577873244777412485237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 110555978516887672532073557 1295577873244777412485237)
                ·
                  refine ⟨121460425616697882420491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1295577873244777412485237 121460425616697882420491)
                  ·
                    rfl

theorem cell23_2128890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_2128890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128890 prefixEnd_2128890 := by exact prefixLift 2128890
  have htrace : WordTrace (prefixWord ++ tailWord_2128890) baseStart_2128890 baseEnd_2128890 := by
    simpa [prefixWord, tailWord_2128890, baseEnd_2128890] using wordTrace_append hprefix tailTrace_2128890
  have hstable : (prefixWord ++ tailWord_2128890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128890).length < 2 ^ (prefixWord ++ tailWord_2128890).sum := by decide
  have hdescent : baseEnd_2128890 < baseStart_2128890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128920 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 2, 5]
def baseStart_2128920 : Nat := 118140960795 + 2128920 * 2 ^ 59
def prefixEnd_2128920 : Nat := 4983230072969 + 3 ^ 40 * 2128920 * 2
def baseEnd_2128920 : Nat := 364386411656638608136427

theorem tailTrace_2128920 : CollatzResearch.WordTrace tailWord_2128920 prefixEnd_2128920 364386411656638608136427 := by
  unfold tailWord_2128920
  simp only [CollatzResearch.WordTrace]
  refine ⟨38824045723646952717092107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51765394298195936956122809 38824045723646952717092107)
  ·
    refine ⟨58236068585470429075638161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38824045723646952717092107 58236068585470429075638161)
    ·
      refine ⟨43677051439102821806728621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58236068585470429075638161 43677051439102821806728621)
      ·
        refine ⟨16378894289663558177523233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43677051439102821806728621 16378894289663558177523233)
        ·
          refine ⟨12284170717247668633142425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16378894289663558177523233 12284170717247668633142425)
          ·
            refine ⟨9213128037935751474856819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12284170717247668633142425 9213128037935751474856819)
            ·
              refine ⟨13819692056903627212285229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9213128037935751474856819 13819692056903627212285229)
              ·
                refine ⟨5182384521338860204606961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13819692056903627212285229 5182384521338860204606961)
                ·
                  refine ⟨3886788391004145153455221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5182384521338860204606961 3886788391004145153455221)
                  ·
                    refine ⟨364386411656638608136427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3886788391004145153455221 364386411656638608136427)
                    ·
                      rfl

theorem cell23_2128920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_2128920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128920 prefixEnd_2128920 := by exact prefixLift 2128920
  have htrace : WordTrace (prefixWord ++ tailWord_2128920) baseStart_2128920 baseEnd_2128920 := by
    simpa [prefixWord, tailWord_2128920, baseEnd_2128920] using wordTrace_append hprefix tailTrace_2128920
  have hstable : (prefixWord ++ tailWord_2128920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128920).length < 2 ^ (prefixWord ++ tailWord_2128920).sum := by decide
  have hdescent : baseEnd_2128920 < baseStart_2128920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128923 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 4]
def baseStart_2128923 : Nat := 118140960795 + 2128923 * 2 ^ 59
def prefixEnd_2128923 : Nat := 4983230072969 + 3 ^ 40 * 2128923 * 2
def baseEnd_2128923 : Nat := 1093160775411879312671767

theorem tailTrace_2128923 : CollatzResearch.WordTrace tailWord_2128923 prefixEnd_2128923 1093160775411879312671767 := by
  unfold tailWord_2128923
  simp only [CollatzResearch.WordTrace]
  refine ⟨77648200866283036946543423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51765467244188691297695615 77648200866283036946543423)
  ·
    refine ⟨116472301299424555419815135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77648200866283036946543423 116472301299424555419815135)
    ·
      refine ⟨174708451949136833129722703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116472301299424555419815135 174708451949136833129722703)
      ·
        refine ⟨262062677923705249694584055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174708451949136833129722703 262062677923705249694584055)
        ·
          refine ⟨393094016885557874541876083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262062677923705249694584055 393094016885557874541876083)
          ·
            refine ⟨589641025328336811812814125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393094016885557874541876083 589641025328336811812814125)
            ·
              refine ⟨221115384498126304429805297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 589641025328336811812814125 221115384498126304429805297)
              ·
                refine ⟨165836538373594728322353973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221115384498126304429805297 165836538373594728322353973)
                ·
                  refine ⟨15547175472524505780220685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165836538373594728322353973 15547175472524505780220685)
                  ·
                    refine ⟨5830190802196689667582757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15547175472524505780220685 5830190802196689667582757)
                    ·
                      refine ⟨1093160775411879312671767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5830190802196689667582757 1093160775411879312671767)
                      ·
                        rfl

theorem cell23_2128923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 3, 4].length) (baseStart_2128923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128923 prefixEnd_2128923 := by exact prefixLift 2128923
  have htrace : WordTrace (prefixWord ++ tailWord_2128923) baseStart_2128923 baseEnd_2128923 := by
    simpa [prefixWord, tailWord_2128923, baseEnd_2128923] using wordTrace_append hprefix tailTrace_2128923
  have hstable : (prefixWord ++ tailWord_2128923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128923).length < 2 ^ (prefixWord ++ tailWord_2128923).sum := by decide
  have hdescent : baseEnd_2128923 < baseStart_2128923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128930 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_2128930 : Nat := 118140960795 + 2128930 * 2 ^ 59
def prefixEnd_2128930 : Nat := 4983230072969 + 3 ^ 40 * 2128930 * 2
def baseEnd_2128930 : Nat := 1093164369776460785284235

theorem tailTrace_2128930 : CollatzResearch.WordTrace tailWord_2128930 prefixEnd_2128930 1093164369776460785284235 := by
  unfold tailWord_2128930
  simp only [CollatzResearch.WordTrace]
  refine ⟨19412114044314419285512061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51765637451505118094698829 19412114044314419285512061)
  ·
    refine ⟨7279542766617907232067023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19412114044314419285512061 7279542766617907232067023)
    ·
      refine ⟨10919314149926860848100535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7279542766617907232067023 10919314149926860848100535)
      ·
        refine ⟨16378971224890291272150803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10919314149926860848100535 16378971224890291272150803)
        ·
          refine ⟨24568456837335436908226205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16378971224890291272150803 24568456837335436908226205)
          ·
            refine ⟨9213171314000788840584827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24568456837335436908226205 9213171314000788840584827)
            ·
              refine ⟨13819756971001183260877241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9213171314000788840584827 13819756971001183260877241)
              ·
                refine ⟨10364817728250887445657931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13819756971001183260877241 10364817728250887445657931)
                ·
                  refine ⟨15547226592376331168486897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10364817728250887445657931 15547226592376331168486897)
                  ·
                    refine ⟨11660419944282248376365173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15547226592376331168486897 11660419944282248376365173)
                    ·
                      refine ⟨1093164369776460785284235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11660419944282248376365173 1093164369776460785284235)
                      ·
                        rfl

theorem cell23_2128930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_2128930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128930 prefixEnd_2128930 := by exact prefixLift 2128930
  have htrace : WordTrace (prefixWord ++ tailWord_2128930) baseStart_2128930 baseEnd_2128930 := by
    simpa [prefixWord, tailWord_2128930, baseEnd_2128930] using wordTrace_append hprefix tailTrace_2128930
  have hstable : (prefixWord ++ tailWord_2128930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128930).length < 2 ^ (prefixWord ++ tailWord_2128930).sum := by decide
  have hdescent : baseEnd_2128930 < baseStart_2128930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128940 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_2128940 : Nat := 118140960795 + 2128940 * 2 ^ 59
def prefixEnd_2128940 : Nat := 4983230072969 + 3 ^ 40 * 2128940 * 2
def baseEnd_2128940 : Nat := 1093169504583005746159189

theorem tailTrace_2128940 : CollatzResearch.WordTrace tailWord_2128940 prefixEnd_2128940 1093169504583005746159189 := by
  unfold tailWord_2128940
  simp only [CollatzResearch.WordTrace]
  refine ⟨38824410453610724424956137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51765880604814299233274849 38824410453610724424956137)
  ·
    refine ⟨29118307840208043318717103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38824410453610724424956137 29118307840208043318717103)
    ·
      refine ⟨43677461760312064978075655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29118307840208043318717103 43677461760312064978075655)
      ·
        refine ⟨65516192640468097467113483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43677461760312064978075655 65516192640468097467113483)
        ·
          refine ⟨98274288960702146200670225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65516192640468097467113483 98274288960702146200670225)
          ·
            refine ⟨73705716720526609650502669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98274288960702146200670225 73705716720526609650502669)
            ·
              refine ⟨27639643770197478618938501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73705716720526609650502669 27639643770197478618938501)
              ·
                refine ⟨5182433206912027241050969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27639643770197478618938501 5182433206912027241050969)
                ·
                  refine ⟨3886824905184020430788227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5182433206912027241050969 3886824905184020430788227)
                  ·
                    refine ⟨5830237357776030646182341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3886824905184020430788227 5830237357776030646182341)
                    ·
                      refine ⟨1093169504583005746159189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5830237357776030646182341 1093169504583005746159189)
                      ·
                        rfl

theorem cell23_2128940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_2128940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128940 prefixEnd_2128940 := by exact prefixLift 2128940
  have htrace : WordTrace (prefixWord ++ tailWord_2128940) baseStart_2128940 baseEnd_2128940 := by
    simpa [prefixWord, tailWord_2128940, baseEnd_2128940] using wordTrace_append hprefix tailTrace_2128940
  have hstable : (prefixWord ++ tailWord_2128940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128940).length < 2 ^ (prefixWord ++ tailWord_2128940).sum := by decide
  have hdescent : baseEnd_2128940 < baseStart_2128940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128957 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 1, 6, 2]
def baseStart_2128957 : Nat := 118140960795 + 2128957 * 2 ^ 59
def prefixEnd_2128957 : Nat := 4983230072969 + 3 ^ 40 * 2128957 * 2
def baseEnd_2128957 : Nat := 1093178233754132179646611

theorem tailTrace_2128957 : CollatzResearch.WordTrace tailWord_2128957 prefixEnd_2128957 1093178233754132179646611 := by
  unfold tailWord_2128957
  simp only [CollatzResearch.WordTrace]
  refine ⟨77649440948159860753281125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51766293965439907168854083 77649440948159860753281125)
  ·
    refine ⟨14559270177779973891240211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77649440948159860753281125 14559270177779973891240211)
    ·
      refine ⟨21838905266669960836860317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14559270177779973891240211 21838905266669960836860317)
      ·
        refine ⟨8189589475001235313822619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21838905266669960836860317 8189589475001235313822619)
        ·
          refine ⟨12284384212501852970733929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8189589475001235313822619 12284384212501852970733929)
          ·
            refine ⟨9213288159376389728050447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12284384212501852970733929 9213288159376389728050447)
            ·
              refine ⟨13819932239064584592075671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9213288159376389728050447 13819932239064584592075671)
              ·
                refine ⟨20729898358596876888113507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13819932239064584592075671 20729898358596876888113507)
                ·
                  refine ⟨31094847537895315332170261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20729898358596876888113507 31094847537895315332170261)
                  ·
                    refine ⟨1457570978338842906195481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31094847537895315332170261 1457570978338842906195481)
                    ·
                      refine ⟨1093178233754132179646611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1457570978338842906195481 1093178233754132179646611)
                      ·
                        rfl

theorem cell23_2128957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_2128957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128957 prefixEnd_2128957 := by exact prefixLift 2128957
  have htrace : WordTrace (prefixWord ++ tailWord_2128957) baseStart_2128957 baseEnd_2128957 := by
    simpa [prefixWord, tailWord_2128957, baseEnd_2128957] using wordTrace_append hprefix tailTrace_2128957
  have hstable : (prefixWord ++ tailWord_2128957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128957).length < 2 ^ (prefixWord ++ tailWord_2128957).sum := by decide
  have hdescent : baseEnd_2128957 < baseStart_2128957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128960 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 3]
def baseStart_2128960 : Nat := 118140960795 + 2128960 * 2 ^ 59
def prefixEnd_2128960 : Nat := 4983230072969 + 3 ^ 40 * 2128960 * 2
def baseEnd_2128960 : Nat := 1093179774196095667909097

theorem tailTrace_2128960 : CollatzResearch.WordTrace tailWord_2128960 prefixEnd_2128960 1093179774196095667909097 := by
  unfold tailWord_2128960
  simp only [CollatzResearch.WordTrace]
  refine ⟨38824775183574496132820167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51766366911432661510426889 38824775183574496132820167)
  ·
    refine ⟨58237162775361744199230251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38824775183574496132820167 58237162775361744199230251)
    ·
      refine ⟨87355744163042616298845377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58237162775361744199230251 87355744163042616298845377)
      ·
        refine ⟨65516808122281962224134033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87355744163042616298845377 65516808122281962224134033)
        ·
          refine ⟨49137606091711471668100525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65516808122281962224134033 49137606091711471668100525)
          ·
            refine ⟨18426602284391801875537697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49137606091711471668100525 18426602284391801875537697)
            ·
              refine ⟨13819951713293851406653273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18426602284391801875537697 13819951713293851406653273)
              ·
                refine ⟨10364963784970388554989955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13819951713293851406653273 10364963784970388554989955)
                ·
                  refine ⟨15547445677455582832484933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10364963784970388554989955 15547445677455582832484933)
                  ·
                    refine ⟨2915146064522921781090925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15547445677455582832484933 2915146064522921781090925)
                    ·
                      refine ⟨1093179774196095667909097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2915146064522921781090925 1093179774196095667909097)
                      ·
                        rfl

theorem cell23_2128960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_2128960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128960 prefixEnd_2128960 := by exact prefixLift 2128960
  have htrace : WordTrace (prefixWord ++ tailWord_2128960) baseStart_2128960 baseEnd_2128960 := by
    simpa [prefixWord, tailWord_2128960, baseEnd_2128960] using wordTrace_append hprefix tailTrace_2128960
  have hstable : (prefixWord ++ tailWord_2128960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128960).length < 2 ^ (prefixWord ++ tailWord_2128960).sum := by decide
  have hdescent : baseEnd_2128960 < baseStart_2128960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128967 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 3, 4]
def baseStart_2128967 : Nat := 118140960795 + 2128967 * 2 ^ 59
def prefixEnd_2128967 : Nat := 4983230072969 + 3 ^ 40 * 2128967 * 2
def baseEnd_2128967 : Nat := 364394456186892380173855

theorem tailTrace_2128967 : CollatzResearch.WordTrace tailWord_2128967 prefixEnd_2128967 364394456186892380173855 := by
  unfold tailWord_2128967
  simp only [CollatzResearch.WordTrace]
  refine ⟨77649805678123632461145155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51766537118749088307430103 77649805678123632461145155)
  ·
    refine ⟨116474708517185448691717733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77649805678123632461145155 116474708517185448691717733)
    ·
      refine ⟨21839007846972271629697075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 116474708517185448691717733 21839007846972271629697075)
      ·
        refine ⟨32758511770458407444545613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21839007846972271629697075 32758511770458407444545613)
        ·
          refine ⟨12284441913921902791704605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32758511770458407444545613 12284441913921902791704605)
          ·
            refine ⟨4606665717720713546889227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12284441913921902791704605 4606665717720713546889227)
            ·
              refine ⟨6909998576581070320333841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4606665717720713546889227 6909998576581070320333841)
              ·
                refine ⟨5182498932435802740250381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6909998576581070320333841 5182498932435802740250381)
                ·
                  refine ⟨1943437099663426027593893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5182498932435802740250381 1943437099663426027593893)
                  ·
                    refine ⟨364394456186892380173855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1943437099663426027593893 364394456186892380173855)
                    ·
                      rfl

theorem cell23_2128967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_2128967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128967 prefixEnd_2128967 := by exact prefixLift 2128967
  have htrace : WordTrace (prefixWord ++ tailWord_2128967) baseStart_2128967 baseEnd_2128967 := by
    simpa [prefixWord, tailWord_2128967, baseEnd_2128967] using wordTrace_append hprefix tailTrace_2128967
  have hstable : (prefixWord ++ tailWord_2128967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128967).length < 2 ^ (prefixWord ++ tailWord_2128967).sum := by decide
  have hdescent : baseEnd_2128967 < baseStart_2128967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128977 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 2, 2, 3]
def baseStart_2128977 : Nat := 118140960795 + 2128977 * 2 ^ 59
def prefixEnd_2128977 : Nat := 4983230072969 + 3 ^ 40 * 2128977 * 2
def baseEnd_2128977 : Nat := 1093188503367222101396519

theorem tailTrace_2128977 : CollatzResearch.WordTrace tailWord_2128977 prefixEnd_2128977 1093188503367222101396519 := by
  unfold tailWord_2128977
  simp only [CollatzResearch.WordTrace]
  refine ⟨77650170408087404169009185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51766780272058269446006123 77650170408087404169009185)
  ·
    refine ⟨58237627806065553126756889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77650170408087404169009185 58237627806065553126756889)
    ·
      refine ⟨43678220854549164845067667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58237627806065553126756889 43678220854549164845067667)
      ·
        refine ⟨65517331281823747267601501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43678220854549164845067667 65517331281823747267601501)
        ·
          refine ⟨24568999230683905225350563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65517331281823747267601501 24568999230683905225350563)
          ·
            refine ⟨36853498846025857838025845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24568999230683905225350563 36853498846025857838025845)
            ·
              refine ⟨3455015516814924172314923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36853498846025857838025845 3455015516814924172314923)
              ·
                refine ⟨5182523275222386258472385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3455015516814924172314923 5182523275222386258472385)
                ·
                  refine ⟨3886892456416789693854289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5182523275222386258472385 3886892456416789693854289)
                  ·
                    refine ⟨2915169342312592270390717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3886892456416789693854289 2915169342312592270390717)
                    ·
                      refine ⟨1093188503367222101396519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2915169342312592270390717 1093188503367222101396519)
                      ·
                        rfl

theorem cell23_2128977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_2128977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128977 prefixEnd_2128977 := by exact prefixLift 2128977
  have htrace : WordTrace (prefixWord ++ tailWord_2128977) baseStart_2128977 baseEnd_2128977 := by
    simpa [prefixWord, tailWord_2128977, baseEnd_2128977] using wordTrace_append hprefix tailTrace_2128977
  have hstable : (prefixWord ++ tailWord_2128977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128977).length < 2 ^ (prefixWord ++ tailWord_2128977).sum := by decide
  have hdescent : baseEnd_2128977 < baseStart_2128977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2128984 : List Nat := [2, 1, 2, 2, 1, 3, 4, 3, 1, 4]
def baseStart_2128984 : Nat := 118140960795 + 2128984 * 2 ^ 59
def prefixEnd_2128984 : Nat := 4983230072969 + 3 ^ 40 * 2128984 * 2
def baseEnd_2128984 : Nat := 364397365910601191336329

theorem tailTrace_2128984 : CollatzResearch.WordTrace tailWord_2128984 prefixEnd_2128984 364397365910601191336329 := by
  unfold tailWord_2128984
  simp only [CollatzResearch.WordTrace]
  refine ⟨38825212859531022182257003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51766950479374696243009337 38825212859531022182257003)
  ·
    refine ⟨58237819289296533273385505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38825212859531022182257003 58237819289296533273385505)
    ·
      refine ⟨43678364466972399955039129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58237819289296533273385505 43678364466972399955039129)
      ·
        refine ⟨32758773350229299966279347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43678364466972399955039129 32758773350229299966279347)
        ·
          refine ⟨49138160025343949949419021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32758773350229299966279347 49138160025343949949419021)
          ·
            refine ⟨18426810009503981231032133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49138160025343949949419021 18426810009503981231032133)
            ·
              refine ⟨3455026876781996480818525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18426810009503981231032133 3455026876781996480818525)
              ·
                refine ⟨1295635078793248680306947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3455026876781996480818525 1295635078793248680306947)
                ·
                  refine ⟨1943452618189873020460421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295635078793248680306947 1943452618189873020460421)
                  ·
                    refine ⟨364397365910601191336329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1943452618189873020460421 364397365910601191336329)
                    ·
                      rfl

theorem cell23_2128984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_2128984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2128984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2128984 prefixEnd_2128984 := by exact prefixLift 2128984
  have htrace : WordTrace (prefixWord ++ tailWord_2128984) baseStart_2128984 baseEnd_2128984 := by
    simpa [prefixWord, tailWord_2128984, baseEnd_2128984] using wordTrace_append hprefix tailTrace_2128984
  have hstable : (prefixWord ++ tailWord_2128984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2128984).length < 2 ^ (prefixWord ++ tailWord_2128984).sum := by decide
  have hdescent : baseEnd_2128984 < baseStart_2128984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2128984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129014 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_2129014 : Nat := 118140960795 + 2129014 * 2 ^ 59
def prefixEnd_2129014 : Nat := 4983230072969 + 3 ^ 40 * 2129014 * 2
def baseEnd_2129014 : Nat := 121467500239048717403761

theorem tailTrace_2129014 : CollatzResearch.WordTrace tailWord_2129014 prefixEnd_2129014 121467500239048717403761 := by
  unfold tailWord_2129014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4853219994309584968006631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51767679939302239658737397 4853219994309584968006631)
  ·
    refine ⟨7279829991464377452009947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4853219994309584968006631 7279829991464377452009947)
    ·
      refine ⟨10919744987196566178014921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7279829991464377452009947 10919744987196566178014921)
      ·
        refine ⟨8189808740397424633511191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10919744987196566178014921 8189808740397424633511191)
        ·
          refine ⟨12284713110596136950266787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8189808740397424633511191 12284713110596136950266787)
          ·
            refine ⟨18427069665894205425400181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12284713110596136950266787 18427069665894205425400181)
            ·
              refine ⟨1727537781177581758631267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18427069665894205425400181 1727537781177581758631267)
              ·
                refine ⟨2591306671766372637946901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727537781177581758631267 2591306671766372637946901)
                ·
                  refine ⟨121467500239048717403761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2591306671766372637946901 121467500239048717403761)
                  ·
                    rfl

theorem cell23_2129014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_2129014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129014 prefixEnd_2129014 := by exact prefixLift 2129014
  have htrace : WordTrace (prefixWord ++ tailWord_2129014) baseStart_2129014 baseEnd_2129014 := by
    simpa [prefixWord, tailWord_2129014, baseEnd_2129014] using wordTrace_append hprefix tailTrace_2129014
  have hstable : (prefixWord ++ tailWord_2129014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129014).length < 2 ^ (prefixWord ++ tailWord_2129014).sum := by decide
  have hdescent : baseEnd_2129014 < baseStart_2129014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129027 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 1, 5]
def baseStart_2129027 : Nat := 118140960795 + 2129027 * 2 ^ 59
def prefixEnd_2129027 : Nat := 4983230072969 + 3 ^ 40 * 2129027 * 2
def baseEnd_2129027 : Nat := 364404725799982301923763

theorem tailTrace_2129027 : CollatzResearch.WordTrace tailWord_2129027 prefixEnd_2129027 364404725799982301923763 := by
  unfold tailWord_2129027
  simp only [CollatzResearch.WordTrace]
  refine ⟨77651994057906262708329335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51767996038604175138886223 77651994057906262708329335)
  ·
    refine ⟨116477991086859394062494003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77651994057906262708329335 116477991086859394062494003)
    ·
      refine ⟨174716986630289091093741005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116477991086859394062494003 174716986630289091093741005)
      ·
        refine ⟨65518869986358409160152877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 174716986630289091093741005 65518869986358409160152877)
        ·
          refine ⟨24569576244884403435057329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65518869986358409160152877 24569576244884403435057329)
          ·
            refine ⟨18427182183663302576292997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24569576244884403435057329 18427182183663302576292997)
            ·
              refine ⟨3455096659436869233054937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18427182183663302576292997 3455096659436869233054937)
              ·
                refine ⟨2591322494577651924791203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3455096659436869233054937 2591322494577651924791203)
                ·
                  refine ⟨3886983741866477887186805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2591322494577651924791203 3886983741866477887186805)
                  ·
                    refine ⟨364404725799982301923763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3886983741866477887186805 364404725799982301923763)
                    ·
                      rfl

theorem cell23_2129027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 5].length) (baseStart_2129027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129027 prefixEnd_2129027 := by exact prefixLift 2129027
  have htrace : WordTrace (prefixWord ++ tailWord_2129027) baseStart_2129027 baseEnd_2129027 := by
    simpa [prefixWord, tailWord_2129027, baseEnd_2129027] using wordTrace_append hprefix tailTrace_2129027
  have hstable : (prefixWord ++ tailWord_2129027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129027).length < 2 ^ (prefixWord ++ tailWord_2129027).sum := by decide
  have hdescent : baseEnd_2129027 < baseStart_2129027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129034 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2]
def baseStart_2129034 : Nat := 118140960795 + 2129034 * 2 ^ 59
def prefixEnd_2129034 : Nat := 4983230072969 + 3 ^ 40 * 2129034 * 2
def baseEnd_2129034 : Nat := 1093217771764528378383757

theorem tailTrace_2129034 : CollatzResearch.WordTrace tailWord_2129034 prefixEnd_2129034 1093217771764528378383757 := by
  unfold tailWord_2129034
  simp only [CollatzResearch.WordTrace]
  refine ⟨19413062342220225725958539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51768166245920601935889437 19413062342220225725958539)
  ·
    refine ⟨29119593513330338588937809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19413062342220225725958539 29119593513330338588937809)
    ·
      refine ⟨21839695134997753941703357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29119593513330338588937809 21839695134997753941703357)
      ·
        refine ⟨8189885675624157728138759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21839695134997753941703357 8189885675624157728138759)
        ·
          refine ⟨12284828513436236592208139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8189885675624157728138759 12284828513436236592208139)
          ·
            refine ⟨18427242770154354888312209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12284828513436236592208139 18427242770154354888312209)
            ·
              refine ⟨13820432077615766166234157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18427242770154354888312209 13820432077615766166234157)
              ·
                refine ⟨5182662029105912312337809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13820432077615766166234157 5182662029105912312337809)
                ·
                  refine ⟨3886996521829434234253357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5182662029105912312337809 3886996521829434234253357)
                  ·
                    refine ⟨1457623695686037837845009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3886996521829434234253357 1457623695686037837845009)
                    ·
                      refine ⟨1093217771764528378383757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1457623695686037837845009 1093217771764528378383757)
                      ·
                        rfl

theorem cell23_2129034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_2129034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129034 prefixEnd_2129034 := by exact prefixLift 2129034
  have htrace : WordTrace (prefixWord ++ tailWord_2129034) baseStart_2129034 baseEnd_2129034 := by
    simpa [prefixWord, tailWord_2129034, baseEnd_2129034] using wordTrace_append hprefix tailTrace_2129034
  have hstable : (prefixWord ++ tailWord_2129034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129034).length < 2 ^ (prefixWord ++ tailWord_2129034).sum := by decide
  have hdescent : baseEnd_2129034 < baseStart_2129034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129057 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 4, 4]
def baseStart_2129057 : Nat := 118140960795 + 2129057 * 2 ^ 59
def prefixEnd_2129057 : Nat := 4983230072969 + 3 ^ 40 * 2129057 * 2
def baseEnd_2129057 : Nat := 364409860606527262798717

theorem tailTrace_2129057 : CollatzResearch.WordTrace tailWord_2129057 prefixEnd_2129057 364409860606527262798717 := by
  unfold tailWord_2129057
  simp only [CollatzResearch.WordTrace]
  refine ⟨77653088247797577831921425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51768725498531718554614283 77653088247797577831921425)
  ·
    refine ⟨58239816185848183373941069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77653088247797577831921425 58239816185848183373941069)
    ·
      refine ⟨21839931069693068765227901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58239816185848183373941069 21839931069693068765227901)
      ·
        refine ⟨8189974151134900786960463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21839931069693068765227901 8189974151134900786960463)
        ·
          refine ⟨12284961226702351180440695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8189974151134900786960463 12284961226702351180440695)
          ·
            refine ⟨18427441840053526770661043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12284961226702351180440695 18427441840053526770661043)
            ·
              refine ⟨27641162760080290155991565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18427441840053526770661043 27641162760080290155991565)
              ·
                refine ⟨10365436035030108808496837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27641162760080290155991565 10365436035030108808496837)
                ·
                  refine ⟨1943519256568145401593157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10365436035030108808496837 1943519256568145401593157)
                  ·
                    refine ⟨364409860606527262798717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1943519256568145401593157 364409860606527262798717)
                    ·
                      rfl

theorem cell23_2129057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_2129057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129057 prefixEnd_2129057 := by exact prefixLift 2129057
  have htrace : WordTrace (prefixWord ++ tailWord_2129057) baseStart_2129057 baseEnd_2129057 := by
    simpa [prefixWord, tailWord_2129057, baseEnd_2129057] using wordTrace_append hprefix tailTrace_2129057
  have hstable : (prefixWord ++ tailWord_2129057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129057).length < 2 ^ (prefixWord ++ tailWord_2129057).sum := by decide
  have hdescent : baseEnd_2129057 < baseStart_2129057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129058 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2129058 : Nat := 118140960795 + 2129058 * 2 ^ 59
def prefixEnd_2129058 : Nat := 4983230072969 + 3 ^ 40 * 2129058 * 2
def baseEnd_2129058 : Nat := 1093230095300236284483647

theorem tailTrace_2129058 : CollatzResearch.WordTrace tailWord_2129058 prefixEnd_2129058 1093230095300236284483647 := by
  unfold tailWord_2129058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19413281180198488750676957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51768749813862636668471885 19413281180198488750676957)
  ·
    refine ⟨7279980442574433281503859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19413281180198488750676957 7279980442574433281503859)
    ·
      refine ⟨10919970663861649922255789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7279980442574433281503859 10919970663861649922255789)
      ·
        refine ⟨4094988998948118720845921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10919970663861649922255789 4094988998948118720845921)
        ·
          refine ⟨3071241749211089040634441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4094988998948118720845921 3071241749211089040634441)
          ·
            refine ⟨2303431311908316780475831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3071241749211089040634441 2303431311908316780475831)
            ·
              refine ⟨3455146967862475170713747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303431311908316780475831 3455146967862475170713747)
              ·
                refine ⟨5182720451793712756070621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3455146967862475170713747 5182720451793712756070621)
                ·
                  refine ⟨1943520169422642283526483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5182720451793712756070621 1943520169422642283526483)
                  ·
                    refine ⟨2915280254133963425289725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1943520169422642283526483 2915280254133963425289725)
                    ·
                      refine ⟨1093230095300236284483647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2915280254133963425289725 1093230095300236284483647)
                      ·
                        rfl

theorem cell23_2129058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2129058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129058 prefixEnd_2129058 := by exact prefixLift 2129058
  have htrace : WordTrace (prefixWord ++ tailWord_2129058) baseStart_2129058 baseEnd_2129058 := by
    simpa [prefixWord, tailWord_2129058, baseEnd_2129058] using wordTrace_append hprefix tailTrace_2129058
  have hstable : (prefixWord ++ tailWord_2129058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129058).length < 2 ^ (prefixWord ++ tailWord_2129058).sum := by decide
  have hdescent : baseEnd_2129058 < baseStart_2129058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129074 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_2129074 : Nat := 118140960795 + 2129074 * 2 ^ 59
def prefixEnd_2129074 : Nat := 4983230072969 + 3 ^ 40 * 2129074 * 2
def baseEnd_2129074 : Nat := 364412770330236073961191

theorem tailTrace_2129074 : CollatzResearch.WordTrace tailWord_2129074 prefixEnd_2129074 364412770330236073961191 := by
  unfold tailWord_2129074
  simp only [CollatzResearch.WordTrace]
  refine ⟨19413427072183997433822569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51769138859157326490193517 19413427072183997433822569)
  ·
    refine ⟨14560070304137998075366927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19413427072183997433822569 14560070304137998075366927)
    ·
      refine ⟨21840105456206997113050391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14560070304137998075366927 21840105456206997113050391)
      ·
        refine ⟨32760158184310495669575587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21840105456206997113050391 32760158184310495669575587)
        ·
          refine ⟨49140237276465743504363381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32760158184310495669575587 49140237276465743504363381)
          ·
            refine ⟨4606897244668663453534067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49140237276465743504363381 4606897244668663453534067)
            ·
              refine ⟨6910345867002995180301101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4606897244668663453534067 6910345867002995180301101)
              ·
                refine ⟨2591379700126123192612913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6910345867002995180301101 2591379700126123192612913)
                ·
                  refine ⟨1943534775094592394459685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2591379700126123192612913 1943534775094592394459685)
                  ·
                    refine ⟨364412770330236073961191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1943534775094592394459685 364412770330236073961191)
                    ·
                      rfl

theorem cell23_2129074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_2129074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129074 prefixEnd_2129074 := by exact prefixLift 2129074
  have htrace : WordTrace (prefixWord ++ tailWord_2129074) baseStart_2129074 baseEnd_2129074 := by
    simpa [prefixWord, tailWord_2129074, baseEnd_2129074] using wordTrace_append hprefix tailTrace_2129074
  have hstable : (prefixWord ++ tailWord_2129074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129074).length < 2 ^ (prefixWord ++ tailWord_2129074).sum := by decide
  have hdescent : baseEnd_2129074 < baseStart_2129074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129084 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_2129084 : Nat := 118140960795 + 2129084 * 2 ^ 59
def prefixEnd_2129084 : Nat := 4983230072969 + 3 ^ 40 * 2129084 * 2
def baseEnd_2129084 : Nat := 1093243445797253182758527

theorem tailTrace_2129084 : CollatzResearch.WordTrace tailWord_2129084 prefixEnd_2129084 1093243445797253182758527 := by
  unfold tailWord_2129084
  simp only [CollatzResearch.WordTrace]
  refine ⟨38827036509349880721577153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51769382012466507628769537 38827036509349880721577153)
  ·
    refine ⟨29120277382012410541182865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38827036509349880721577153 29120277382012410541182865)
    ·
      refine ⟨21840208036509307905887149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29120277382012410541182865 21840208036509307905887149)
      ·
        refine ⟨8190078013690990464707681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21840208036509307905887149 8190078013690990464707681)
        ·
          refine ⟨6142558510268242848530761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8190078013690990464707681 6142558510268242848530761)
          ·
            refine ⟨4606918882701182136398071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6142558510268242848530761 4606918882701182136398071)
            ·
              refine ⟨6910378324051773204597107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4606918882701182136398071 6910378324051773204597107)
              ·
                refine ⟨10365567486077659806895661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6910378324051773204597107 10365567486077659806895661)
                ·
                  refine ⟨3887087807279122427585873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10365567486077659806895661 3887087807279122427585873)
                  ·
                    refine ⟨2915315855459341820689405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3887087807279122427585873 2915315855459341820689405)
                    ·
                      refine ⟨1093243445797253182758527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2915315855459341820689405 1093243445797253182758527)
                      ·
                        rfl

theorem cell23_2129084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_2129084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129084 prefixEnd_2129084 := by exact prefixLift 2129084
  have htrace : WordTrace (prefixWord ++ tailWord_2129084) baseStart_2129084 baseEnd_2129084 := by
    simpa [prefixWord, tailWord_2129084, baseEnd_2129084] using wordTrace_append hprefix tailTrace_2129084
  have hstable : (prefixWord ++ tailWord_2129084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129084).length < 2 ^ (prefixWord ++ tailWord_2129084).sum := by decide
  have hdescent : baseEnd_2129084 < baseStart_2129084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129108 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_2129108 : Nat := 118140960795 + 2129108 * 2 ^ 59
def prefixEnd_2129108 : Nat := 4983230072969 + 3 ^ 40 * 2129108 * 2
def baseEnd_2129108 : Nat := 364418589777653696286139

theorem tailTrace_2129108 : CollatzResearch.WordTrace tailWord_2129108 prefixEnd_2129108 364418589777653696286139 := by
  unfold tailWord_2129108
  simp only [CollatzResearch.WordTrace]
  refine ⟨38827474185306406771013989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51769965580408542361351985 38827474185306406771013989)
  ·
    refine ⟨7280151409744951269565123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38827474185306406771013989 7280151409744951269565123)
    ·
      refine ⟨10920227114617426904347685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7280151409744951269565123 10920227114617426904347685)
      ·
        refine ⟨2047542583990767544565191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10920227114617426904347685 2047542583990767544565191)
        ·
          refine ⟨3071313875986151316847787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047542583990767544565191 3071313875986151316847787)
          ·
            refine ⟨4606970813979226975271681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071313875986151316847787 4606970813979226975271681)
            ·
              refine ⟨3455228110484420231453761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4606970813979226975271681 3455228110484420231453761)
              ·
                refine ⟨2591421082863315173590321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3455228110484420231453761 2591421082863315173590321)
                ·
                  refine ⟨1943565812147486380192741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2591421082863315173590321 1943565812147486380192741)
                  ·
                    refine ⟨364418589777653696286139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1943565812147486380192741 364418589777653696286139)
                    ·
                      rfl

theorem cell23_2129108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_2129108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129108 prefixEnd_2129108 := by exact prefixLift 2129108
  have htrace : WordTrace (prefixWord ++ tailWord_2129108) baseStart_2129108 baseEnd_2129108 := by
    simpa [prefixWord, tailWord_2129108, baseEnd_2129108] using wordTrace_append hprefix tailTrace_2129108
  have hstable : (prefixWord ++ tailWord_2129108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129108).length < 2 ^ (prefixWord ++ tailWord_2129108).sum := by decide
  have hdescent : baseEnd_2129108 < baseStart_2129108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129124 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 3, 3, 2]
def baseStart_2129124 : Nat := 118140960795 + 2129124 * 2 ^ 59
def prefixEnd_2129124 : Nat := 4983230072969 + 3 ^ 40 * 2129124 * 2
def baseEnd_2129124 : Nat := 1093263985023433026258343

theorem tailTrace_2129124 : CollatzResearch.WordTrace tailWord_2129124 prefixEnd_2129124 1093263985023433026258343 := by
  unfold tailWord_2129124
  simp only [CollatzResearch.WordTrace]
  refine ⟨38827765969277424137305213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51770354625703232183073617 38827765969277424137305213)
  ·
    refine ⟨14560412238479034051489455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38827765969277424137305213 14560412238479034051489455)
    ·
      refine ⟨21840618357718551077234183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14560412238479034051489455 21840618357718551077234183)
      ·
        refine ⟨32760927536577826615851275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21840618357718551077234183 32760927536577826615851275)
        ·
          refine ⟨49141391304866739923776913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32760927536577826615851275 49141391304866739923776913)
          ·
            refine ⟨36856043478650054942832685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49141391304866739923776913 36856043478650054942832685)
            ·
              refine ⟨13821016304493770603562257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36856043478650054942832685 13821016304493770603562257)
              ·
                refine ⟨10365762228370327952671693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13821016304493770603562257 10365762228370327952671693)
                ·
                  refine ⟨3887160835638872982251885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10365762228370327952671693 3887160835638872982251885)
                  ·
                    refine ⟨1457685313364577368344457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3887160835638872982251885 1457685313364577368344457)
                    ·
                      refine ⟨1093263985023433026258343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1457685313364577368344457 1093263985023433026258343)
                      ·
                        rfl

theorem cell23_2129124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_2129124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129124 prefixEnd_2129124 := by exact prefixLift 2129124
  have htrace : WordTrace (prefixWord ++ tailWord_2129124) baseStart_2129124 baseEnd_2129124 := by
    simpa [prefixWord, tailWord_2129124, baseEnd_2129124] using wordTrace_append hprefix tailTrace_2129124
  have hstable : (prefixWord ++ tailWord_2129124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129124).length < 2 ^ (prefixWord ++ tailWord_2129124).sum := by decide
  have hdescent : baseEnd_2129124 < baseStart_2129124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129182 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_2129182 : Nat := 118140960795 + 2129182 * 2 ^ 59
def prefixEnd_2129182 : Nat := 4983230072969 + 3 ^ 40 * 2129182 * 2
def baseEnd_2129182 : Nat := 1093293766901393799333077

theorem tailTrace_2129182 : CollatzResearch.WordTrace tailWord_2129182 prefixEnd_2129182 1093293766901393799333077 := by
  unfold tailWord_2129182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9707205921543090522527725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51771764914896482786814533 9707205921543090522527725)
  ·
    refine ⟨3640202220578658945947897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9707205921543090522527725 3640202220578658945947897)
    ·
      refine ⟨2730151665433994209460923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3640202220578658945947897 2730151665433994209460923)
      ·
        refine ⟨4095227498150991314191385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730151665433994209460923 4095227498150991314191385)
        ·
          refine ⟨3071420623613243485643539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4095227498150991314191385 3071420623613243485643539)
          ·
            refine ⟨4607130935419865228465309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3071420623613243485643539 4607130935419865228465309)
            ·
              refine ⟨1727674100782449460674491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4607130935419865228465309 1727674100782449460674491)
              ·
                refine ⟨2591511151173674191011737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727674100782449460674491 2591511151173674191011737)
                ·
                  refine ⟨1943633363380255643258803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2591511151173674191011737 1943633363380255643258803)
                  ·
                    refine ⟨2915450045070383464888205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1943633363380255643258803 2915450045070383464888205)
                    ·
                      refine ⟨1093293766901393799333077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2915450045070383464888205 1093293766901393799333077)
                      ·
                        rfl

theorem cell23_2129182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_2129182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129182 prefixEnd_2129182 := by exact prefixLift 2129182
  have htrace : WordTrace (prefixWord ++ tailWord_2129182) baseStart_2129182 baseEnd_2129182 := by
    simpa [prefixWord, tailWord_2129182, baseEnd_2129182] using wordTrace_append hprefix tailTrace_2129182
  have hstable : (prefixWord ++ tailWord_2129182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129182).length < 2 ^ (prefixWord ++ tailWord_2129182).sum := by decide
  have hdescent : baseEnd_2129182 < baseStart_2129182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129194 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 7]
def baseStart_2129194 : Nat := 118140960795 + 2129194 * 2 ^ 59
def prefixEnd_2129194 : Nat := 4983230072969 + 3 ^ 40 * 2129194 * 2
def baseEnd_2129194 : Nat := 121477769852138639153669

theorem tailTrace_2129194 : CollatzResearch.WordTrace tailWord_2129194 prefixEnd_2129194 121477769852138639153669 := by
  unfold tailWord_2129194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19414521262075312557414659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51772056698867500153105757 19414521262075312557414659)
  ·
    refine ⟨29121781893112968836121989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19414521262075312557414659 29121781893112968836121989)
    ·
      refine ⟨5460334104958681656772873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29121781893112968836121989 5460334104958681656772873)
      ·
        refine ⟨4095250578719011242579655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5460334104958681656772873 4095250578719011242579655)
        ·
          refine ⟨6142875868078516863869483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4095250578719011242579655 6142875868078516863869483)
          ·
            refine ⟨9214313802117775295804225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6142875868078516863869483 9214313802117775295804225)
            ·
              refine ⟨6910735351588331471853169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9214313802117775295804225 6910735351588331471853169)
              ·
                refine ⟨5183051513691248603889877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6910735351588331471853169 5183051513691248603889877)
                ·
                  refine ⟨121477769852138639153669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5183051513691248603889877 121477769852138639153669)
                  ·
                    rfl

theorem cell23_2129194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_2129194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129194 prefixEnd_2129194 := by exact prefixLift 2129194
  have htrace : WordTrace (prefixWord ++ tailWord_2129194) baseStart_2129194 baseEnd_2129194 := by
    simpa [prefixWord, tailWord_2129194, baseEnd_2129194] using wordTrace_append hprefix tailTrace_2129194
  have hstable : (prefixWord ++ tailWord_2129194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129194).length < 2 ^ (prefixWord ++ tailWord_2129194).sum := by decide
  have hdescent : baseEnd_2129194 < baseStart_2129194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129261 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_2129261 : Nat := 118140960795 + 2129261 * 2 ^ 59
def prefixEnd_2129261 : Nat := 4983230072969 + 3 ^ 40 * 2129261 * 2
def baseEnd_2129261 : Nat := 1093334331873098990245213

theorem tailTrace_2129261 : CollatzResearch.WordTrace tailWord_2129261 prefixEnd_2129261 1093334331873098990245213 := by
  unfold tailWord_2129261
  simp only [CollatzResearch.WordTrace]
  refine ⟨77660528739058520672347637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51773685826039013781565091 77660528739058520672347637)
  ·
    refine ⟨7280674569286736313032591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77660528739058520672347637 7280674569286736313032591)
    ·
      refine ⟨10921011853930104469548887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7280674569286736313032591 10921011853930104469548887)
      ·
        refine ⟨16381517780895156704323331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10921011853930104469548887 16381517780895156704323331)
        ·
          refine ⟨24572276671342735056484997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16381517780895156704323331 24572276671342735056484997)
          ·
            refine ⟨4607301875876762823090937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24572276671342735056484997 4607301875876762823090937)
            ·
              refine ⟨3455476406907572117318203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4607301875876762823090937 3455476406907572117318203)
              ·
                refine ⟨5183214610361358175977305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3455476406907572117318203 5183214610361358175977305)
                ·
                  refine ⟨3887410957771018631982979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5183214610361358175977305 3887410957771018631982979)
                  ·
                    refine ⟨5831116436656527947974469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3887410957771018631982979 5831116436656527947974469)
                    ·
                      refine ⟨1093334331873098990245213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5831116436656527947974469 1093334331873098990245213)
                      ·
                        rfl

theorem cell23_2129261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_2129261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129261 prefixEnd_2129261 := by exact prefixLift 2129261
  have htrace : WordTrace (prefixWord ++ tailWord_2129261) baseStart_2129261 baseEnd_2129261 := by
    simpa [prefixWord, tailWord_2129261, baseEnd_2129261] using wordTrace_append hprefix tailTrace_2129261
  have hstable : (prefixWord ++ tailWord_2129261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129261).length < 2 ^ (prefixWord ++ tailWord_2129261).sum := by decide
  have hdescent : baseEnd_2129261 < baseStart_2129261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129271 : List Nat := [1, 1, 3, 1, 1, 2, 4, 5, 1, 4]
def baseStart_2129271 : Nat := 118140960795 + 2129271 * 2 ^ 59
def prefixEnd_2129271 : Nat := 4983230072969 + 3 ^ 40 * 2129271 * 2
def baseEnd_2129271 : Nat := 364446488893214650373389

theorem tailTrace_2129271 : CollatzResearch.WordTrace tailWord_2129271 prefixEnd_2129271 364446488893214650373389 := by
  unfold tailWord_2129271
  simp only [CollatzResearch.WordTrace]
  refine ⟨77660893469022292380211667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51773928979348194920141111 77660893469022292380211667)
  ·
    refine ⟨116491340203533438570317501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77660893469022292380211667 116491340203533438570317501)
    ·
      refine ⟨43684252576325039463869063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 116491340203533438570317501 43684252576325039463869063)
      ·
        refine ⟨65526378864487559195803595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43684252576325039463869063 65526378864487559195803595)
        ·
          refine ⟨98289568296731338793705393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65526378864487559195803595 98289568296731338793705393)
          ·
            refine ⟨73717176222548504095279045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98289568296731338793705393 73717176222548504095279045)
            ·
              refine ⟨13821970541727844517864821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73717176222548504095279045 13821970541727844517864821)
              ·
                refine ⟨1295809738286985423549827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13821970541727844517864821 1295809738286985423549827)
                ·
                  refine ⟨1943714607430478135324741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295809738286985423549827 1943714607430478135324741)
                  ·
                    refine ⟨364446488893214650373389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1943714607430478135324741 364446488893214650373389)
                    ·
                      rfl

theorem cell23_2129271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_2129271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129271 prefixEnd_2129271 := by exact prefixLift 2129271
  have htrace : WordTrace (prefixWord ++ tailWord_2129271) baseStart_2129271 baseEnd_2129271 := by
    simpa [prefixWord, tailWord_2129271, baseEnd_2129271] using wordTrace_append hprefix tailTrace_2129271
  have hstable : (prefixWord ++ tailWord_2129271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129271).length < 2 ^ (prefixWord ++ tailWord_2129271).sum := by decide
  have hdescent : baseEnd_2129271 < baseStart_2129271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129284 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 6]
def baseStart_2129284 : Nat := 118140960795 + 2129284 * 2 ^ 59
def prefixEnd_2129284 : Nat := 4983230072969 + 3 ^ 40 * 2129284 * 2
def baseEnd_2129284 : Nat := 121482904658683600028623

theorem tailTrace_2129284 : CollatzResearch.WordTrace tailWord_2129284 prefixEnd_2129284 121482904658683600028623 := by
  unfold tailWord_2129284
  simp only [CollatzResearch.WordTrace]
  refine ⟨38830683808987597800217453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51774245078650130400289937 38830683808987597800217453)
  ·
    refine ⟨14561506428370349175081545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38830683808987597800217453 14561506428370349175081545)
    ·
      refine ⟨10921129821277761881311159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14561506428370349175081545 10921129821277761881311159)
      ·
        refine ⟨16381694731916642821966739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10921129821277761881311159 16381694731916642821966739)
        ·
          refine ⟨24572542097874964232950109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16381694731916642821966739 24572542097874964232950109)
          ·
            refine ⟨9214703286703111587356291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24572542097874964232950109 9214703286703111587356291)
            ·
              refine ⟨13822054930054667381034437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9214703286703111587356291 13822054930054667381034437)
              ·
                refine ⟨2591635299385250133943957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13822054930054667381034437 2591635299385250133943957)
                ·
                  refine ⟨121482904658683600028623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2591635299385250133943957 121482904658683600028623)
                  ·
                    rfl

theorem cell23_2129284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_2129284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129284 prefixEnd_2129284 := by exact prefixLift 2129284
  have htrace : WordTrace (prefixWord ++ tailWord_2129284) baseStart_2129284 baseEnd_2129284 := by
    simpa [prefixWord, tailWord_2129284, baseEnd_2129284] using wordTrace_append hprefix tailTrace_2129284
  have hstable : (prefixWord ++ tailWord_2129284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129284).length < 2 ^ (prefixWord ++ tailWord_2129284).sum := by decide
  have hdescent : baseEnd_2129284 < baseStart_2129284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129288 : List Nat := [2, 1, 3, 3, 1, 3, 1, 4, 1, 4]
def baseStart_2129288 : Nat := 118140960795 + 2129288 * 2 ^ 59
def prefixEnd_2129288 : Nat := 4983230072969 + 3 ^ 40 * 2129288 * 2
def baseEnd_2129288 : Nat := 364449398616923461535863

theorem tailTrace_2129288 : CollatzResearch.WordTrace tailWord_2129288 prefixEnd_2129288 364449398616923461535863 := by
  unfold tailWord_2129288
  simp only [CollatzResearch.WordTrace]
  refine ⟨38830756754980352141790259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51774342339973802855720345 38830756754980352141790259)
  ·
    refine ⟨58246135132470528212685389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38830756754980352141790259 58246135132470528212685389)
    ·
      refine ⟨21842300674676448079757021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58246135132470528212685389 21842300674676448079757021)
      ·
        refine ⟨8190862753003668029908883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21842300674676448079757021 8190862753003668029908883)
        ·
          refine ⟨12286294129505502044863325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8190862753003668029908883 12286294129505502044863325)
          ·
            refine ⟨4607360298564563266823747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12286294129505502044863325 4607360298564563266823747)
            ·
              refine ⟨6911040447846844900235621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4607360298564563266823747 6911040447846844900235621)
              ·
                refine ⟨1295820083971283418794179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6911040447846844900235621 1295820083971283418794179)
                ·
                  refine ⟨1943730125956925128191269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295820083971283418794179 1943730125956925128191269)
                  ·
                    refine ⟨364449398616923461535863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1943730125956925128191269 364449398616923461535863)
                    ·
                      rfl

theorem cell23_2129288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_2129288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129288 prefixEnd_2129288 := by exact prefixLift 2129288
  have htrace : WordTrace (prefixWord ++ tailWord_2129288) baseStart_2129288 baseEnd_2129288 := by
    simpa [prefixWord, tailWord_2129288, baseEnd_2129288] using wordTrace_append hprefix tailTrace_2129288
  have hstable : (prefixWord ++ tailWord_2129288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129288).length < 2 ^ (prefixWord ++ tailWord_2129288).sum := by decide
  have hdescent : baseEnd_2129288 < baseStart_2129288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129311 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 5, 1, 3]
def baseStart_2129311 : Nat := 118140960795 + 2129311 * 2 ^ 59
def prefixEnd_2129311 : Nat := 4983230072969 + 3 ^ 40 * 2129311 * 2
def baseEnd_2129311 : Nat := 1093360005905823794619983

theorem tailTrace_2129311 : CollatzResearch.WordTrace tailWord_2129311 prefixEnd_2129311 1093360005905823794619983 := by
  unfold tailWord_2129311
  simp only [CollatzResearch.WordTrace]
  refine ⟨77662352388877379211667787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51774901592584919474445191 77662352388877379211667787)
  ·
    refine ⟨116493528583316068817501681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77662352388877379211667787 116493528583316068817501681)
    ·
      refine ⟨87370146437487051613126261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116493528583316068817501681 87370146437487051613126261)
      ·
        refine ⟨8190951228514411088730587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 87370146437487051613126261 8190951228514411088730587)
        ·
          refine ⟨12286426842771616633095881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8190951228514411088730587 12286426842771616633095881)
          ·
            refine ⟨9214820132078712474821911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12286426842771616633095881 9214820132078712474821911)
            ·
              refine ⟨13822230198118068712232867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9214820132078712474821911 13822230198118068712232867)
              ·
                refine ⟨20733345297177103068349301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13822230198118068712232867 20733345297177103068349301)
                ·
                  refine ⟨1943751121610353412657747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20733345297177103068349301 1943751121610353412657747)
                  ·
                    refine ⟨2915626682415530118986621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1943751121610353412657747 2915626682415530118986621)
                    ·
                      refine ⟨1093360005905823794619983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2915626682415530118986621 1093360005905823794619983)
                      ·
                        rfl

theorem cell23_2129311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_2129311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129311 prefixEnd_2129311 := by exact prefixLift 2129311
  have htrace : WordTrace (prefixWord ++ tailWord_2129311) baseStart_2129311 baseEnd_2129311 := by
    simpa [prefixWord, tailWord_2129311, baseEnd_2129311] using wordTrace_append hprefix tailTrace_2129311
  have hstable : (prefixWord ++ tailWord_2129311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129311).length < 2 ^ (prefixWord ++ tailWord_2129311).sum := by decide
  have hdescent : baseEnd_2129311 < baseStart_2129311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129354 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_2129354 : Nat := 118140960795 + 2129354 * 2 ^ 59
def prefixEnd_2129354 : Nat := 4983230072969 + 3 ^ 40 * 2129354 * 2
def baseEnd_2129354 : Nat := 1093382085573967126382285

theorem tailTrace_2129354 : CollatzResearch.WordTrace tailWord_2129354 prefixEnd_2129354 1093382085573967126382285 := by
  unfold tailWord_2129354
  simp only [CollatzResearch.WordTrace]
  refine ⟨19415980181930399388870779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51775947151814398370322077 19415980181930399388870779)
  ·
    refine ⟨29123970272895599083306169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19415980181930399388870779 29123970272895599083306169)
    ·
      refine ⟨21842977704671699312479627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29123970272895599083306169 21842977704671699312479627)
      ·
        refine ⟨32764466557007548968719441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21842977704671699312479627 32764466557007548968719441)
        ·
          refine ⟨24573349917755661726539581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32764466557007548968719441 24573349917755661726539581)
          ·
            refine ⟨9215006219158373147452343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24573349917755661726539581 9215006219158373147452343)
            ·
              refine ⟨13822509328737559721178515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9215006219158373147452343 13822509328737559721178515)
              ·
                refine ⟨20733763993106339581767773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13822509328737559721178515 20733763993106339581767773)
                ·
                  refine ⟨7775161497414877343162915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20733763993106339581767773 7775161497414877343162915)
                  ·
                    refine ⟨11662742246122316014744373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7775161497414877343162915 11662742246122316014744373)
                    ·
                      refine ⟨1093382085573967126382285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11662742246122316014744373 1093382085573967126382285)
                      ·
                        rfl

theorem cell23_2129354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_2129354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129354 prefixEnd_2129354 := by exact prefixLift 2129354
  have htrace : WordTrace (prefixWord ++ tailWord_2129354) baseStart_2129354 baseEnd_2129354 := by
    simpa [prefixWord, tailWord_2129354, baseEnd_2129354] using wordTrace_append hprefix tailTrace_2129354
  have hstable : (prefixWord ++ tailWord_2129354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129354).length < 2 ^ (prefixWord ++ tailWord_2129354).sum := by decide
  have hdescent : baseEnd_2129354 < baseStart_2129354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129368 : List Nat := [2, 1, 2, 2, 2, 1, 4, 2, 3, 2, 2]
def baseStart_2129368 : Nat := 118140960795 + 2129368 * 2 ^ 59
def prefixEnd_2129368 : Nat := 4983230072969 + 3 ^ 40 * 2129368 * 2
def baseEnd_2129368 : Nat := 1093389274303130071607221

theorem tailTrace_2129368 : CollatzResearch.WordTrace tailWord_2129368 prefixEnd_2129368 1093389274303130071607221 := by
  unfold tailWord_2129368
  simp only [CollatzResearch.WordTrace]
  refine ⟨38832215674835438973246379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51776287566447251964328505 38832215674835438973246379)
  ·
    refine ⟨58248323512253158459869569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38832215674835438973246379 58248323512253158459869569)
    ·
      refine ⟨43686242634189868844902177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58248323512253158459869569 43686242634189868844902177)
      ·
        refine ⟨32764681975642401633676633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43686242634189868844902177 32764681975642401633676633)
        ·
          refine ⟨24573511481731801225257475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32764681975642401633676633 24573511481731801225257475)
          ·
            refine ⟨36860267222597701837886213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24573511481731801225257475 36860267222597701837886213)
            ·
              refine ⟨6911300104237069094603665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36860267222597701837886213 6911300104237069094603665)
              ·
                refine ⟨5183475078177801820952749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6911300104237069094603665 5183475078177801820952749)
                ·
                  refine ⟨1943803154316675682857281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5183475078177801820952749 1943803154316675682857281)
                  ·
                    refine ⟨1457852365737506762142961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1943803154316675682857281 1457852365737506762142961)
                    ·
                      refine ⟨1093389274303130071607221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1457852365737506762142961 1093389274303130071607221)
                      ·
                        rfl

theorem cell23_2129368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_2129368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129368 prefixEnd_2129368 := by exact prefixLift 2129368
  have htrace : WordTrace (prefixWord ++ tailWord_2129368) baseStart_2129368 baseEnd_2129368 := by
    simpa [prefixWord, tailWord_2129368, baseEnd_2129368] using wordTrace_append hprefix tailTrace_2129368
  have hstable : (prefixWord ++ tailWord_2129368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129368).length < 2 ^ (prefixWord ++ tailWord_2129368).sum := by decide
  have hdescent : baseEnd_2129368 < baseStart_2129368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129402 : List Nat := [3, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2]
def baseStart_2129402 : Nat := 118140960795 + 2129402 * 2 ^ 59
def prefixEnd_2129402 : Nat := 4983230072969 + 3 ^ 40 * 2129402 * 2
def baseEnd_2129402 : Nat := 1093406732645382938582065

theorem tailTrace_2129402 : CollatzResearch.WordTrace tailWord_2129402 prefixEnd_2129402 1093406732645382938582065 := by
  unfold tailWord_2129402
  simp only [CollatzResearch.WordTrace]
  refine ⟨19416417857886925438307615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51777114287698467835486973 19416417857886925438307615)
  ·
    refine ⟨29124626786830388157461423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19416417857886925438307615 29124626786830388157461423)
    ·
      refine ⟨43686940180245582236192135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29124626786830388157461423 43686940180245582236192135)
      ·
        refine ⟨65530410270368373354288203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43686940180245582236192135 65530410270368373354288203)
        ·
          refine ⟨98295615405552560031432305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65530410270368373354288203 98295615405552560031432305)
          ·
            refine ⟨73721711554164420023574229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98295615405552560031432305 73721711554164420023574229)
            ·
              refine ⟨1727852614550728594302521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 73721711554164420023574229 1727852614550728594302521)
              ·
                refine ⟨1295889460913046445726891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1727852614550728594302521 1295889460913046445726891)
                ·
                  refine ⟨1943834191369569668590337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1295889460913046445726891 1943834191369569668590337)
                  ·
                    refine ⟨1457875643527177251442753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1943834191369569668590337 1457875643527177251442753)
                    ·
                      refine ⟨1093406732645382938582065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1457875643527177251442753 1093406732645382938582065)
                      ·
                        rfl

theorem cell23_2129402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2].length) (baseStart_2129402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129402 prefixEnd_2129402 := by exact prefixLift 2129402
  have htrace : WordTrace (prefixWord ++ tailWord_2129402) baseStart_2129402 baseEnd_2129402 := by
    simpa [prefixWord, tailWord_2129402, baseEnd_2129402] using wordTrace_append hprefix tailTrace_2129402
  have hstable : (prefixWord ++ tailWord_2129402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129402).length < 2 ^ (prefixWord ++ tailWord_2129402).sum := by decide
  have hdescent : baseEnd_2129402 < baseStart_2129402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129412 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_2129412 : Nat := 118140960795 + 2129412 * 2 ^ 59
def prefixEnd_2129412 : Nat := 4983230072969 + 3 ^ 40 * 2129412 * 2
def baseEnd_2129412 : Nat := 364470622483975966485673

theorem tailTrace_2129412 : CollatzResearch.WordTrace tailWord_2129412 prefixEnd_2129412 364470622483975966485673 := by
  unfold tailWord_2129412
  simp only [CollatzResearch.WordTrace]
  refine ⟨38833018080755736730547245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51777357441007648974062993 38833018080755736730547245)
  ·
    refine ⟨14562381780283401273955217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38833018080755736730547245 14562381780283401273955217)
    ·
      refine ⟨10921786335212550955466413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14562381780283401273955217 10921786335212550955466413)
      ·
        refine ⟨4095669875704706608299905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10921786335212550955466413 4095669875704706608299905)
        ·
          refine ⟨3071752406778529956224929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4095669875704706608299905 3071752406778529956224929)
          ·
            refine ⟨2303814305083897467168697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3071752406778529956224929 2303814305083897467168697)
            ·
              refine ⟨1727860728812923100376523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2303814305083897467168697 1727860728812923100376523)
              ·
                refine ⟨2591791093219384650564785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1727860728812923100376523 2591791093219384650564785)
                ·
                  refine ⟨1943843319914538487923589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2591791093219384650564785 1943843319914538487923589)
                  ·
                    refine ⟨364470622483975966485673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1943843319914538487923589 364470622483975966485673)
                    ·
                      rfl

theorem cell23_2129412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_2129412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129412 prefixEnd_2129412 := by exact prefixLift 2129412
  have htrace : WordTrace (prefixWord ++ tailWord_2129412) baseStart_2129412 baseEnd_2129412 := by
    simpa [prefixWord, tailWord_2129412, baseEnd_2129412] using wordTrace_append hprefix tailTrace_2129412
  have hstable : (prefixWord ++ tailWord_2129412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129412).length < 2 ^ (prefixWord ++ tailWord_2129412).sum := by decide
  have hdescent : baseEnd_2129412 < baseStart_2129412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129422 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3]
def baseStart_2129422 : Nat := 118140960795 + 2129422 * 2 ^ 59
def prefixEnd_2129422 : Nat := 4983230072969 + 3 ^ 40 * 2129422 * 2
def baseEnd_2129422 : Nat := 1093417002258472860331973

theorem tailTrace_2129422 : CollatzResearch.WordTrace tailWord_2129422 prefixEnd_2129422 1093417002258472860331973 := by
  unfold tailWord_2129422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9708300111434405646119815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51777600594316830112639013 9708300111434405646119815)
  ·
    refine ⟨14562450167151608469179723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9708300111434405646119815 14562450167151608469179723)
    ·
      refine ⟨21843675250727412703769585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14562450167151608469179723 21843675250727412703769585)
      ·
        refine ⟨16382756438045559527827189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21843675250727412703769585 16382756438045559527827189)
        ·
          refine ⟨1535883416066771205733799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16382756438045559527827189 1535883416066771205733799)
          ·
            refine ⟨2303825124100156808600699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535883416066771205733799 2303825124100156808600699)
            ·
              refine ⟨3455737686150235212901049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2303825124100156808600699 3455737686150235212901049)
              ·
                refine ⟨2591803264612676409675787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3455737686150235212901049 2591803264612676409675787)
                ·
                  refine ⟨3887704896919014614513681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2591803264612676409675787 3887704896919014614513681)
                  ·
                    refine ⟨2915778672689260960885261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3887704896919014614513681 2915778672689260960885261)
                    ·
                      refine ⟨1093417002258472860331973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2915778672689260960885261 1093417002258472860331973)
                      ·
                        rfl

theorem cell23_2129422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_2129422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129422 prefixEnd_2129422 := by exact prefixLift 2129422
  have htrace : WordTrace (prefixWord ++ tailWord_2129422) baseStart_2129422 baseEnd_2129422 := by
    simpa [prefixWord, tailWord_2129422, baseEnd_2129422] using wordTrace_append hprefix tailTrace_2129422
  have hstable : (prefixWord ++ tailWord_2129422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129422).length < 2 ^ (prefixWord ++ tailWord_2129422).sum := by decide
  have hdescent : baseEnd_2129422 < baseStart_2129422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129434 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_2129434 : Nat := 118140960795 + 2129434 * 2 ^ 59
def prefixEnd_2129434 : Nat := 4983230072969 + 3 ^ 40 * 2129434 * 2
def baseEnd_2129434 : Nat := 364474388008775604460639

theorem tailTrace_2129434 : CollatzResearch.WordTrace tailWord_2129434 prefixEnd_2129434 364474388008775604460639 := by
  unfold tailWord_2129434
  simp only [CollatzResearch.WordTrace]
  refine ⟨19416709641857942804598839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51777892378287847478930237 19416709641857942804598839)
  ·
    refine ⟨29125064462786914206898259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19416709641857942804598839 29125064462786914206898259)
    ·
      refine ⟨43687596694180371310347389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29125064462786914206898259 43687596694180371310347389)
      ·
        refine ⟨16382848760317639241380271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43687596694180371310347389 16382848760317639241380271)
        ·
          refine ⟨24574273140476458862070407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16382848760317639241380271 24574273140476458862070407)
          ·
            refine ⟨36861409710714688293105611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24574273140476458862070407 36861409710714688293105611)
            ·
              refine ⟨55292114566072032439658417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36861409710714688293105611 55292114566072032439658417)
              ·
                refine ⟨41469085924554024329743813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55292114566072032439658417 41469085924554024329743813)
                ·
                  refine ⟨7775453610853879561826965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41469085924554024329743813 7775453610853879561826965)
                  ·
                    refine ⟨364474388008775604460639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7775453610853879561826965 364474388008775604460639)
                    ·
                      rfl

theorem cell23_2129434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_2129434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129434 prefixEnd_2129434 := by exact prefixLift 2129434
  have htrace : WordTrace (prefixWord ++ tailWord_2129434) baseStart_2129434 baseEnd_2129434 := by
    simpa [prefixWord, tailWord_2129434, baseEnd_2129434] using wordTrace_append hprefix tailTrace_2129434
  have hstable : (prefixWord ++ tailWord_2129434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129434).length < 2 ^ (prefixWord ++ tailWord_2129434).sum := by decide
  have hdescent : baseEnd_2129434 < baseStart_2129434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129461 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_2129461 : Nat := 118140960795 + 2129461 * 2 ^ 59
def prefixEnd_2129461 : Nat := 4983230072969 + 3 ^ 40 * 2129461 * 2
def baseEnd_2129461 : Nat := 1093437028003998207744293

theorem tailTrace_2129461 : CollatzResearch.WordTrace tailWord_2129461 prefixEnd_2129461 1093437028003998207744293 := by
  unfold tailWord_2129461
  simp only [CollatzResearch.WordTrace]
  refine ⟨77667823338333954829628237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51778548892222636553085491 77667823338333954829628237)
  ·
    refine ⟨29125433751875233061110589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77667823338333954829628237 29125433751875233061110589)
    ·
      refine ⟨10922037656953212397916471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29125433751875233061110589 10922037656953212397916471)
      ·
        refine ⟨16383056485429818596874707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10922037656953212397916471 16383056485429818596874707)
        ·
          refine ⟨24574584728144727895312061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16383056485429818596874707 24574584728144727895312061)
          ·
            refine ⟨9215469273054272960742023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24574584728144727895312061 9215469273054272960742023)
            ·
              refine ⟨13823203909581409441113035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9215469273054272960742023 13823203909581409441113035)
              ·
                refine ⟨20734805864372114161669553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13823203909581409441113035 20734805864372114161669553)
                ·
                  refine ⟨15551104398279085621252165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20734805864372114161669553 15551104398279085621252165)
                  ·
                    refine ⟨2915832074677328553984781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15551104398279085621252165 2915832074677328553984781)
                    ·
                      refine ⟨1093437028003998207744293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2915832074677328553984781 1093437028003998207744293)
                      ·
                        rfl

theorem cell23_2129461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_2129461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129461 prefixEnd_2129461 := by exact prefixLift 2129461
  have htrace : WordTrace (prefixWord ++ tailWord_2129461) baseStart_2129461 baseEnd_2129461 := by
    simpa [prefixWord, tailWord_2129461, baseEnd_2129461] using wordTrace_append hprefix tailTrace_2129461
  have hstable : (prefixWord ++ tailWord_2129461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129461).length < 2 ^ (prefixWord ++ tailWord_2129461).sum := by decide
  have hdescent : baseEnd_2129461 < baseStart_2129461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129471 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 4]
def baseStart_2129471 : Nat := 118140960795 + 2129471 * 2 ^ 59
def prefixEnd_2129471 : Nat := 4983230072969 + 3 ^ 40 * 2129471 * 2
def baseEnd_2129471 : Nat := 1093442162810543168619247

theorem tailTrace_2129471 : CollatzResearch.WordTrace tailWord_2129471 prefixEnd_2129471 1093442162810543168619247 := by
  unfold tailWord_2129471
  simp only [CollatzResearch.WordTrace]
  refine ⟨77668188068297726537492267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51778792045531817691661511 77668188068297726537492267)
  ·
    refine ⟨116502282102446589806238401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77668188068297726537492267 116502282102446589806238401)
    ·
      refine ⟨87376711576834942354678801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116502282102446589806238401 87376711576834942354678801)
      ·
        refine ⟨65532533682626206766009101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87376711576834942354678801 65532533682626206766009101)
        ·
          refine ⟨24574700130984827537253413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65532533682626206766009101 24574700130984827537253413)
          ·
            refine ⟨4607756274559655163235015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24574700130984827537253413 4607756274559655163235015)
            ·
              refine ⟨6911634411839482744852523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4607756274559655163235015 6911634411839482744852523)
              ·
                refine ⟨10367451617759224117278785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6911634411839482744852523 10367451617759224117278785)
                ·
                  refine ⟨7775588713319418087959089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10367451617759224117278785 7775588713319418087959089)
                  ·
                    refine ⟨5831691534989563565969317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7775588713319418087959089 5831691534989563565969317)
                    ·
                      refine ⟨1093442162810543168619247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5831691534989563565969317 1093442162810543168619247)
                      ·
                        rfl

theorem cell23_2129471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_2129471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129471 prefixEnd_2129471 := by exact prefixLift 2129471
  have htrace : WordTrace (prefixWord ++ tailWord_2129471) baseStart_2129471 baseEnd_2129471 := by
    simpa [prefixWord, tailWord_2129471, baseEnd_2129471] using wordTrace_append hprefix tailTrace_2129471
  have hstable : (prefixWord ++ tailWord_2129471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129471).length < 2 ^ (prefixWord ++ tailWord_2129471).sum := by decide
  have hdescent : baseEnd_2129471 < baseStart_2129471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129511 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 2, 5]
def baseStart_2129511 : Nat := 118140960795 + 2129511 * 2 ^ 59
def prefixEnd_2129511 : Nat := 4983230072969 + 3 ^ 40 * 2129511 * 2
def baseEnd_2129511 : Nat := 364487567345574337373021

theorem tailTrace_2129511 : CollatzResearch.WordTrace tailWord_2129511 prefixEnd_2129511 364487567345574337373021 := by
  unfold tailWord_2129511
  simp only [CollatzResearch.WordTrace]
  refine ⟨77669646988152813368948387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51779764658768542245965591 77669646988152813368948387)
  ·
    refine ⟨116504470482229220053422581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77669646988152813368948387 116504470482229220053422581)
    ·
      refine ⟨10922294107708989380008367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116504470482229220053422581 10922294107708989380008367)
      ·
        refine ⟨16383441161563484070012551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10922294107708989380008367 16383441161563484070012551)
        ·
          refine ⟨24575161742345226105018827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16383441161563484070012551 24575161742345226105018827)
          ·
            refine ⟨36862742613517839157528241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24575161742345226105018827 36862742613517839157528241)
            ·
              refine ⟨27647056960138379368146181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36862742613517839157528241 27647056960138379368146181)
              ·
                refine ⟨5183823180025946131527409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27647056960138379368146181 5183823180025946131527409)
                ·
                  refine ⟨3887867385019459598645557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5183823180025946131527409 3887867385019459598645557)
                  ·
                    refine ⟨364487567345574337373021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3887867385019459598645557 364487567345574337373021)
                    ·
                      rfl

theorem cell23_2129511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_2129511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129511 prefixEnd_2129511 := by exact prefixLift 2129511
  have htrace : WordTrace (prefixWord ++ tailWord_2129511) baseStart_2129511 baseEnd_2129511 := by
    simpa [prefixWord, tailWord_2129511, baseEnd_2129511] using wordTrace_append hprefix tailTrace_2129511
  have hstable : (prefixWord ++ tailWord_2129511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129511).length < 2 ^ (prefixWord ++ tailWord_2129511).sum := by decide
  have hdescent : baseEnd_2129511 < baseStart_2129511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129568 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 3]
def baseStart_2129568 : Nat := 118140960795 + 2129568 * 2 ^ 59
def prefixEnd_2129568 : Nat := 4983230072969 + 3 ^ 40 * 2129568 * 2
def baseEnd_2129568 : Nat := 1093491970434029289106301

theorem tailTrace_2129568 : CollatzResearch.WordTrace tailWord_2129568 prefixEnd_2129568 1093491970434029289106301 := by
  unfold tailWord_2129568
  simp only [CollatzResearch.WordTrace]
  refine ⟨38835862974473156051886679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51781150632630874735848905 38835862974473156051886679)
  ·
    refine ⟨58253794461709734077830019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38835862974473156051886679 58253794461709734077830019)
    ·
      refine ⟨87380691692564601116745029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58253794461709734077830019 87380691692564601116745029)
      ·
        refine ⟨16383879692355862709389693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 87380691692564601116745029 16383879692355862709389693)
        ·
          refine ⟨6143954884633448516021135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16383879692355862709389693 6143954884633448516021135)
          ·
            refine ⟨9215932326950172774031703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6143954884633448516021135 9215932326950172774031703)
            ·
              refine ⟨13823898490425259161047555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9215932326950172774031703 13823898490425259161047555)
              ·
                refine ⟨20735847735637888741571333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13823898490425259161047555 20735847735637888741571333)
                ·
                  refine ⟨3887971450432104139044625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20735847735637888741571333 3887971450432104139044625)
                  ·
                    refine ⟨2915978587824078104283469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3887971450432104139044625 2915978587824078104283469)
                    ·
                      refine ⟨1093491970434029289106301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2915978587824078104283469 1093491970434029289106301)
                      ·
                        rfl

theorem cell23_2129568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_2129568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129568 prefixEnd_2129568 := by exact prefixLift 2129568
  have htrace : WordTrace (prefixWord ++ tailWord_2129568) baseStart_2129568 baseEnd_2129568 := by
    simpa [prefixWord, tailWord_2129568, baseEnd_2129568] using wordTrace_append hprefix tailTrace_2129568
  have hstable : (prefixWord ++ tailWord_2129568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129568).length < 2 ^ (prefixWord ++ tailWord_2129568).sum := by decide
  have hdescent : baseEnd_2129568 < baseStart_2129568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129571 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 6]
def baseStart_2129571 : Nat := 118140960795 + 2129571 * 2 ^ 59
def prefixEnd_2129571 : Nat := 4983230072969 + 3 ^ 40 * 2129571 * 2
def baseEnd_2129571 : Nat := 121499278986221419707643

theorem tailTrace_2129571 : CollatzResearch.WordTrace tailWord_2129571 prefixEnd_2129571 121499278986221419707643 := by
  unfold tailWord_2129571
  simp only [CollatzResearch.WordTrace]
  refine ⟨77671835367935443616132567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51781223578623629077421711 77671835367935443616132567)
  ·
    refine ⟨116507753051903165424198851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77671835367935443616132567 116507753051903165424198851)
    ·
      refine ⟨174761629577854748136298277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 116507753051903165424198851 174761629577854748136298277)
      ·
        refine ⟨32767805545847765275555927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 174761629577854748136298277 32767805545847765275555927)
        ·
          refine ⟨49151708318771647913333891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32767805545847765275555927 49151708318771647913333891)
          ·
            refine ⟨73727562478157471870000837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49151708318771647913333891 73727562478157471870000837)
            ·
              refine ⟨13823917964654525975625157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73727562478157471870000837 13823917964654525975625157)
              ·
                refine ⟨2591984618372723620429717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13823917964654525975625157 2591984618372723620429717)
                ·
                  refine ⟨121499278986221419707643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2591984618372723620429717 121499278986221419707643)
                  ·
                    rfl

theorem cell23_2129571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 6].length) (baseStart_2129571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129571 prefixEnd_2129571 := by exact prefixLift 2129571
  have htrace : WordTrace (prefixWord ++ tailWord_2129571) baseStart_2129571 baseEnd_2129571 := by
    simpa [prefixWord, tailWord_2129571, baseEnd_2129571] using wordTrace_append hprefix tailTrace_2129571
  have hstable : (prefixWord ++ tailWord_2129571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129571).length < 2 ^ (prefixWord ++ tailWord_2129571).sum := by decide
  have hdescent : baseEnd_2129571 < baseStart_2129571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2129625 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 2, 3, 2]
def baseStart_2129625 : Nat := 118140960795 + 2129625 * 2 ^ 59
def prefixEnd_2129625 : Nat := 4983230072969 + 3 ^ 40 * 2129625 * 2
def baseEnd_2129625 : Nat := 1093521238831335566093539

theorem tailTrace_2129625 : CollatzResearch.WordTrace tailWord_2129625 prefixEnd_2129625 1093521238831335566093539 := by
  unfold tailWord_2129625
  simp only [CollatzResearch.WordTrace]
  refine ⟨77673804909739810838598329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51782536606493207225732219 77673804909739810838598329)
  ·
    refine ⟨58255353682304858128948747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77673804909739810838598329 58255353682304858128948747)
    ·
      refine ⟨87383030523457287193423121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58255353682304858128948747 87383030523457287193423121)
      ·
        refine ⟨65537272892592965395067341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87383030523457287193423121 65537272892592965395067341)
        ·
          refine ⟨24576477334722362023150253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65537272892592965395067341 24576477334722362023150253)
          ·
            refine ⟨9216179000520885758681345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24576477334722362023150253 9216179000520885758681345)
            ·
              refine ⟨6912134250390664319011009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9216179000520885758681345 6912134250390664319011009)
              ·
                refine ⟨5184100687792998239258257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6912134250390664319011009 5184100687792998239258257)
                ·
                  refine ⟨3888075515844748679443693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5184100687792998239258257 3888075515844748679443693)
                  ·
                    refine ⟨1458028318441780754791385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3888075515844748679443693 1458028318441780754791385)
                    ·
                      refine ⟨1093521238831335566093539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1458028318441780754791385 1093521238831335566093539)
                      ·
                        rfl

theorem cell23_2129625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 3, 2].length) (baseStart_2129625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2129625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2129625 prefixEnd_2129625 := by exact prefixLift 2129625
  have htrace : WordTrace (prefixWord ++ tailWord_2129625) baseStart_2129625 baseEnd_2129625 := by
    simpa [prefixWord, tailWord_2129625, baseEnd_2129625] using wordTrace_append hprefix tailTrace_2129625
  have hstable : (prefixWord ++ tailWord_2129625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2129625).length < 2 ^ (prefixWord ++ tailWord_2129625).sum := by decide
  have hdescent : baseEnd_2129625 < baseStart_2129625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2129625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
